"""Kaggle TPU measurement: calibration microbenchmarks, then every workload kernel, as % of bound.

    python run_profile.py [--sections calib,kernels,xla] [--reps N]

Writes ACCEL_RESULTS (JSON) incrementally. Every kernel is checked bit-exactly on device output against an
independent host reference before its time is reported. Times: device time from the JAX profiler trace
when the trace can be parsed, else wall-clock over back-to-back async calls (both are recorded).
"""
import argparse
import json
import os
import pathlib
import statistics
import time
import traceback

import numpy as np

R = {"sections": {}}
OUT = pathlib.Path(os.environ.get("ACCEL_RESULTS", "/tmp/tpuperf-results.json"))


def save():
    OUT.write_text(json.dumps(R, indent=1, default=str))


def log(*a):
    print(time.strftime("%H:%M:%S"), *a, flush=True)


def wall(f, *args, reps=20):
    import jax
    jax.block_until_ready(f(*args))
    ts = []
    for _ in range(3):
        t = time.perf_counter()
        for _ in range(reps):
            o = f(*args)
        jax.block_until_ready(o)
        ts.append((time.perf_counter() - t) / reps)
    return min(ts)


def device_time(f, *args, reps=5, name_hint=None):
    """Sum of device-op durations per call from a profiler trace (best effort)."""
    import jax
    d = pathlib.Path("/tmp/tpuperf-trace") / str(time.time_ns())
    jax.block_until_ready(f(*args))
    with jax.profiler.trace(str(d)):
        for _ in range(reps):
            o = f(*args)
        jax.block_until_ready(o)
    try:
        from jax.profiler import ProfileData
    except Exception:
        from jax._src.lib import _profile_data as _pd  # noqa
        ProfileData = _pd.ProfileData
    pb = next(d.rglob("*.xplane.pb"))
    pd = ProfileData.from_file(str(pb))
    ops = {}
    for plane in pd.planes:
        if "TPU:0" not in plane.name:
            continue
        for line in plane.lines:
            if line.name not in ("XLA Ops", "XLA Modules"):
                continue
            for ev in line.events:
                key = (line.name, ev.name)
                ops[key] = ops.get(key, 0.0) + ev.duration_ns
    mods = {k[1]: v / reps / 1e9 for k, v in ops.items() if k[0] == "XLA Modules"}
    xops = sorted(((v / reps / 1e9, k[1]) for k, v in ops.items() if k[0] == "XLA Ops"), reverse=True)[:12]
    return dict(module_s=mods, top_ops=xops, total_module_s=sum(mods.values()))


def calib(reps):
    import functools
    import jax
    import jax.numpy as jnp
    from jax.experimental import pallas as pl
    from jax.experimental.pallas import tpu as pltpu
    c = {}
    # HBM: read+write copy, and read-only reduction
    x = jnp.ones((256 * 2**20,), jnp.int32)                       # 1 GiB
    t = wall(jax.jit(lambda v: v + 1), x, reps=reps)
    c["hbm_copy_GBps"] = 2 * x.nbytes / t / 1e9
    t = wall(jax.jit(lambda v: jnp.sum(v)), x, reps=reps)
    c["hbm_read_GBps"] = x.nbytes / t / 1e9
    del x
    log("hbm", c)
    # VPU int32 rate: VMEM-resident block, ITER dependent rounds of 4 int32 ops (mul, add, shift, xor)
    ITER = 2048

    def vk(x_ref, o_ref):
        def body(i, v):
            v = v * 1103515245 + 12345
            return v ^ (v >> 7)
        o_ref[...] = jax.lax.fori_loop(0, ITER, body, x_ref[...], unroll=8)
    blk = (512, 1024)
    xv = jnp.arange(blk[0] * blk[1] * 16, dtype=jnp.int32).reshape(16 * blk[0], blk[1])
    fv = jax.jit(lambda v: pl.pallas_call(vk, out_shape=jax.ShapeDtypeStruct(v.shape, v.dtype), grid=(16,),
                                          in_specs=[pl.BlockSpec(blk, lambda i: (i, 0))],
                                          out_specs=pl.BlockSpec(blk, lambda i: (i, 0)))(v))
    t = wall(fv, xv, reps=5)
    c["vpu_int32_ops_per_s"] = 4 * ITER * xv.size / t
    # same chain of the reduction's ops: and, shift-arith, compare+select, sub
    def vk2(x_ref, o_ref):
        def body(i, v):
            w = (v & 255) - (v >> 8)
            return jnp.where(w < 0, w + 977, w)
        o_ref[...] = jax.lax.fori_loop(0, ITER, body, x_ref[...], unroll=8)
    fv2 = jax.jit(lambda v: pl.pallas_call(vk2, out_shape=jax.ShapeDtypeStruct(v.shape, v.dtype), grid=(16,),
                                           in_specs=[pl.BlockSpec(blk, lambda i: (i, 0))],
                                           out_specs=pl.BlockSpec(blk, lambda i: (i, 0)))(v))
    t = wall(fv2, xv, reps=5)
    c["vpu_int32_ops_per_s_reduction_mix"] = 6 * ITER * xv.size / t   # and, shr, sub, cmp, add, select
    log("vpu", c)
    # per grid step overhead: trivial (8,128) copy over many steps
    for steps in (1024, 8192):
        xs = jnp.ones((steps * 8, 128), jnp.int32)
        fs = jax.jit(lambda v: pl.pallas_call(lambda a, o: o.__setitem__(Ellipsis, a[...]),
                                              out_shape=jax.ShapeDtypeStruct(v.shape, v.dtype), grid=(v.shape[0] // 8,),
                                              in_specs=[pl.BlockSpec((8, 128), lambda i: (i, 0))],
                                              out_specs=pl.BlockSpec((8, 128), lambda i: (i, 0)))(v))
        c[f"grid_step_s_{steps}"] = wall(fs, xs, reps=reps) / steps
    log("grid", c)
    # matmuls
    from .kernels.common import mm_i8
    rng = np.random.default_rng(0)
    for n in (1024, 4096, 8192):
        a = jnp.asarray(rng.integers(-128, 128, (n, n), dtype=np.int64).astype(np.int8))
        f = jax.jit(lambda u, v: jnp.dot(u, v, preferred_element_type=jnp.int32))
        t = wall(f, a, a, reps=reps)
        c[f"xla_int8_{n}_s"] = t
        c[f"xla_int8_{n}_TOPS"] = 2 * n**3 / t / 1e12
        if n == 8192:
            fp = jax.jit(lambda u, v: mm_i8(u, v, bm=512, bn=512, bk=2048))
            t = wall(fp, a, a, reps=reps)
            c["pallas_int8_8192_TOPS"] = 2 * n**3 / t / 1e12
            ab = a.astype(jnp.bfloat16)
            t = wall(jax.jit(lambda u, v: jnp.dot(u, v, preferred_element_type=jnp.float32)), ab, ab, reps=reps)
            c["xla_bf16_8192_TFLOPS"] = 2 * n**3 / t / 1e12
            try:
                c["xla_int8_8192_device"] = device_time(f, a, a)
            except Exception:
                c["device_time_error"] = traceback.format_exc()[-800:]
        log("mm", n, {k: v for k, v in c.items() if str(n) in k})
    return c


def run_kernels(reps, vpu_rate, only=None):
    import jax
    import jax.numpy as jnp
    from . import counts as C
    from .registry import KERNELS
    from .kernels import mxfp4, rns_ntt, sumcheck
    out = []
    rng = np.random.default_rng(7)
    for name, k in KERNELS.items():
        for cfg_name, p in k["cfgs"].items():
            if cfg_name == "mac" or (only and name not in only):
                continue
            row = dict(kernel=name, cfg=cfg_name, params=p)
            try:
                t0 = time.time()
                if name == "mxfp4_w4a8":
                    args, rd = mxfp4.inputs(rng, **p)
                    sub = dict(rd, x=rd["x"][:64])
                    expect = mxfp4.ref(sub, **dict(p, T=64))
                    check = lambda o: bool((np.asarray(o)[:64].astype(np.int64) == expect).all())
                elif name == "rns_ntt61":
                    B, N, N1 = p["B"], p["N"], p["N1"]
                    plan = rns_ntt.plan_for(N, N1)
                    raw = rng.integers(0, 2**60, (B, N), dtype=np.int64).astype(np.uint64)    # < 2^60 < q
                    xb = raw.view(np.uint8).reshape(B, N, 8)
                    xo = ((xb.reshape(B, N1, N // N1, 8).transpose(3, 0, 1, 2)).astype(np.int16) - 128).astype(np.int8)
                    T1p, T2p = rns_ntt.pallas_operands(plan)
                    args = (np.ascontiguousarray(xo), T1p, T2p)
                    polys = [0, B - 1]
                    sub = dict(x=[[int(v) for v in raw[b]] for b in polys])
                    exp_sub = rns_ntt.ref(sub, B=len(polys), N=N, N1=N1)                # [N1, 8, 2, N2]
                    check = lambda o: bool((np.asarray(o)[:, :, polys, :] == exp_sub).all())
                else:
                    H = p["H"]
                    args, rd = sumcheck.inputs_pallas(rng, H)
                    es = sumcheck_sums_numpy(rd, H)
                    def check(o, rd=rd, H=H, es=es):
                        okf, s = sumcheck.check_pallas(o, rd, H, sample_cols=2048)
                        return bool(okf and s == es)
                row["host_prep_s"] = round(time.time() - t0, 1)
                dev = [jnp.asarray(a) for a in args]
                f = jax.jit(k["impl"](**p))
                t0 = time.time()
                o = jax.block_until_ready(f(*dev))
                row["first_call_s"] = round(time.time() - t0, 2)
                row["exact"] = check(o)
                row["wall_s"] = wall(f, *dev, reps=reps)
                try:
                    row["device"] = device_time(f, *dev)
                except Exception:
                    row["device_error"] = traceback.format_exc()[-600:]
                cf, cs = k["count"](**p)
                cnt = C.counts(cf, *[jax.ShapeDtypeStruct(s, d) for s, d in cs])
                b = C.bound(cnt, "v5e", vpu_ops=vpu_rate)
                row["bound"] = b
                t_meas = row.get("device", {}).get("total_module_s") or row["wall_s"]
                row["t_meas_s"] = t_meas
                row["pct_of_bound"] = 100 * b["bound_s"] / t_meas
                log(name, cfg_name, "exact", row["exact"], "meas %.1f us" % (t_meas * 1e6),
                    "bound %.1f us (%s)" % (b["bound_s"] * 1e6, b["unit"]), "%.1f%%" % row["pct_of_bound"])
            except Exception:
                row["error"] = traceback.format_exc()[-1500:]
                log(name, cfg_name, "ERROR", row["error"][-300:])
            out.append(row)
            R["sections"]["kernels"] = out
            save()
    return out


def sumcheck_sums_numpy(rd, H):
    """Exact round sums with vectorized int64 (every product of two residues < 2^62, reduced before summing)."""
    from .kernels.sumcheck import P, W
    f, g, r = rd["f"].astype(np.int64), rd["g"].astype(np.int64), rd["r"]

    def emul(a, b):  # a, b: [4, n] int64 canonical
        c = [np.zeros(a.shape[1], np.int64) for _ in range(7)]
        for i in range(4):
            for j in range(4):
                c[i + j] = (c[i + j] + a[i] * b[j] % P) % P
        return np.stack([(c[m] + W * c[m + 4] % P) % P if m + 4 < 7 else c[m] for m in range(4)])

    rr = np.array(r, np.int64)[:, None] * np.ones((1, H), np.int64)

    def fold(x0, x1):
        return (x0 + emul(rr, (x1 - x0) % P)) % P
    f0, f1 = fold(f[:, 0, 0], f[:, 1, 0]), fold(f[:, 0, 1], f[:, 1, 1])
    g0, g1 = fold(g[:, 0, 0], g[:, 1, 0]), fold(g[:, 0, 1], g[:, 1, 1])
    out = []
    for ft, gt in ((f0, g0), (f1, g1), ((2 * f1 - f0) % P, (2 * g1 - g0) % P)):
        s = emul(ft, gt).sum(axis=1) % P
        out.append([int(v) for v in s])
    return out


def xla_baselines(reps):
    """The XLA formulations the static check predicted to be 24x/36x off: one measurement each."""
    import jax
    import jax.numpy as jnp
    from .kernels import rns_ntt, sumcheck
    res = {}
    rng = np.random.default_rng(9)
    plan = rns_ntt.plan_for(8192, 64)
    f, _ = rns_ntt.make_ntt(plan)
    xp = rng.integers(0, 256, (8, 64, 1024, 128), dtype=np.int64).astype(np.uint8)
    xp[7] &= 15                                                    # keep values < 2^60 < q
    T1, T2 = jnp.asarray(plan.T1), jnp.asarray(plan.T2)
    res["ntt_xla_s"] = wall(jax.jit(f), jnp.asarray(xp), T1, T2, reps=3)
    log("xla ntt", res)
    H = 2**22
    (fz, gz, Wb, Cb), rd = sumcheck.inputs(rng, H)
    res["sumcheck_xla_s"] = wall(jax.jit(sumcheck.round_fn), *map(jnp.asarray, (fz, gz, Wb, Cb)), reps=3)
    log("xla sumcheck", res)
    return res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--sections", default="calib,kernels,xla")
    ap.add_argument("--reps", type=int, default=20)
    a = ap.parse_args()
    import jax
    R["jax"] = jax.__version__
    R["backend"] = jax.default_backend()
    R["devices"] = [str(d) for d in jax.devices()]
    R["device_kind"] = jax.devices()[0].device_kind
    assert R["backend"] == "tpu", R["backend"]
    save()
    secs = a.sections.split(",")
    vpu = None
    if "calib" in secs:
        try:
            R["sections"]["calib"] = calib(a.reps)
            vpu = R["sections"]["calib"].get("vpu_int32_ops_per_s_reduction_mix")
        except Exception:
            R["sections"]["calib_error"] = traceback.format_exc()[-1500:]
        save()
    if "kernels" in secs:
        run_kernels(a.reps, vpu)
    if "xla" in secs:
        try:
            R["sections"]["xla"] = xla_baselines(a.reps)
        except Exception:
            R["sections"]["xla_error"] = traceback.format_exc()[-1500:]
        save()
    log("DONE")
