"""Second deviceless probe: (a) which generations' topologies compile, (b) does the Mosaic compiler reject an
illegal Pallas tile at compile time (it must, for the static linter to be backed by the real compiler),
(c) VMEM over-capacity rejection, (d) XLA dump of the after-optimization HLO works."""
import json, os, sys, traceback
import jax, jax.numpy as jnp
from jax.experimental import topologies, pallas as pl
from jax.sharding import SingleDeviceSharding
R = {}
def topo(name):
    return topologies.get_topology_desc(platform="tpu", topology_name=name).devices[0]
for name in ["v5e:1x1", "v6e:1x1", "v5p:2x2x1", "v4:2x2x1"]:
    try:
        R["topo " + name] = topo(name).device_kind
    except Exception as e:
        R["topo " + name] = "ERR " + str(e).splitlines()[0][:200]
def comp(dev, f, *shapes):
    shd = SingleDeviceSharding(dev)
    args = [jax.ShapeDtypeStruct(s, d, sharding=shd) for s, d in shapes]
    try:
        c = jax.jit(f).lower(*args).compile()
        return {"ok": True, "mem": str(c.memory_analysis())[:300]}
    except Exception as e:
        return {"ok": False, "err": str(e)[-700:]}
def kern(a_ref, b_ref, o_ref):
    o_ref[...] = jnp.dot(a_ref[...], b_ref[...], preferred_element_type=jnp.int32)
def mk(bm, bk, bn, M=1024, K=1024, N=1024):
    def f(a, b):
        return pl.pallas_call(kern, out_shape=jax.ShapeDtypeStruct((M, N), jnp.int32), grid=(M // bm, N // bn),
            in_specs=[pl.BlockSpec((bm, K), lambda i, j: (i, 0)), pl.BlockSpec((K, bn), lambda i, j: (0, j))],
            out_specs=pl.BlockSpec((bm, bn), lambda i, j: (i, j)))(a, b)
    return f
d5 = topo("v5e:1x1")
R["pallas legal 256x256"] = comp(d5, mk(256, 1024, 256), ((1024, 1024), jnp.int8), ((1024, 1024), jnp.int8))
R["pallas illegal bn=100 (not /128)"] = comp(d5, mk(256, 1000, 100, K=1000, N=1000, M=1024), ((1024, 1000), jnp.int8), ((1000, 1000), jnp.int8))
R["pallas vmem 8192x8192 int8 blocks"] = comp(d5, mk(8192, 8192, 8192, 8192, 8192, 8192), ((8192, 8192), jnp.int8), ((8192, 8192), jnp.int8))
def k64(a_ref, o_ref):
    o_ref[...] = a_ref[...] * a_ref[...]
jax.config.update("jax_enable_x64", True)
R["pallas u64 mul"] = comp(d5, lambda a: pl.pallas_call(k64, out_shape=jax.ShapeDtypeStruct((256, 256), jnp.uint64))(a), ((256, 256), jnp.uint64))
R["xla u64 mul"] = comp(d5, lambda a: a * a, ((256, 256), jnp.uint64))
print(json.dumps(R, indent=1))
