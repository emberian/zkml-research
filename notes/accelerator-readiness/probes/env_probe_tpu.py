"""TPU v5e environment probe for the 61-bit RNS design: JAX version/devices, and three exactness facts
the limb design depends on, each checked against Python ints: (1) u32 multiply low word, (2) int8 x int8
-> int32 dot (preferred_element_type) at K = 1024, (3) whether jax_enable_x64 u64 multiply is exact and
what it costs relative to u32. Writes ACCEL_RESULTS."""
import json, os, pathlib, time
import numpy as np
R = {}
import jax
jax.config.update("jax_enable_x64", True)
import jax.numpy as jnp
R["jax"] = jax.__version__
R["backend"] = jax.default_backend()
R["devices"] = [str(d) for d in jax.devices()]
R["device_kind"] = jax.devices()[0].device_kind
rng = np.random.default_rng(1)
def timeit(f, *a, n=20):
    f(*a).block_until_ready()
    t = time.perf_counter()
    for _ in range(n):
        r = f(*a)
    r.block_until_ready()
    return (time.perf_counter() - t) / n
a = rng.integers(0, 2**32, 1 << 22, dtype=np.uint64).astype(np.uint32)
b = rng.integers(0, 2**32, 1 << 22, dtype=np.uint64).astype(np.uint32)
f32 = jax.jit(lambda x, y: x * y)
R["u32_mul_exact"] = bool(np.array_equal(np.asarray(f32(a, b)), a * b))
R["u32_mul_s_per_4M"] = timeit(f32, a, b)
A = rng.integers(-128, 128, (512, 1024), dtype=np.int64).astype(np.int8)
B = rng.integers(-128, 128, (1024, 512), dtype=np.int64).astype(np.int8)
fd = jax.jit(lambda x, y: jnp.dot(x, y, preferred_element_type=jnp.int32))
ref = A.astype(np.int64) @ B.astype(np.int64)
R["i8_dot_exact_K1024"] = bool(np.array_equal(np.asarray(fd(A, B)).astype(np.int64), ref))
A2 = rng.integers(-128, 128, (4096, 4096), dtype=np.int64).astype(np.int8)
R["i8_dot_s_4096cubed"] = timeit(fd, A2, A2, n=10)
a64 = rng.integers(0, 2**61, 1 << 22, dtype=np.uint64)
b64 = rng.integers(0, 2**61, 1 << 22, dtype=np.uint64)
f64 = jax.jit(lambda x, y: x * y)
try:
    R["u64_mul_lo_exact"] = bool(np.array_equal(np.asarray(f64(a64, b64)), a64 * b64))
    R["u64_mul_s_per_4M"] = timeit(f64, a64, b64)
except Exception as e:
    R["u64_mul_error"] = repr(e)[:300]
print(json.dumps(R, indent=1))
pathlib.Path(os.environ["ACCEL_RESULTS"]).write_text(json.dumps(R, indent=1))
