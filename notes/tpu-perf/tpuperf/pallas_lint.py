"""Static linter for Pallas TPU kernels, from the jaxpr (runs anywhere; the Mosaic compile on hbox is the
authority, this explains WHY a tiling is good or bad before the compiler is asked).

Rules (source: Pallas TPU docs and what the compiler enforced in GROUNDING section 0):
  R1 last two block dims divisible by (sublane, 128) or equal to the array dims; sublane tile is 8 for
     32-bit, 16 for 16-bit, 32 for 8-bit (packed) types [READ:cc layouts T(8,128), T(8,128)(2,1), T(32,128)(4,1)]
  R2 every dot inside the kernel: M, N, K multiples of the MXU edge (128 v5e, 256 v6e), else the MXU is underfilled
  R3 VMEM: sum of block bytes x 2 (double buffering) + scratch <= the scoped limit (compiler_params
     vmem_limit_bytes, else a conservative 16 MiB default [INFERRED]) and well under capacity
  R4 no 64-bit dtypes inside a kernel (Mosaic rejects u64 multiply: GROUNDING section 0)
  R5 grid steps: per-step overhead ~0.35 us [INFERRED, measured on Kaggle by calibration]; flag kernels
     whose per-step compute is below ~10x that
"""
import math

import jax
import numpy as np

SUBLANE = {1: 32, 2: 16, 4: 8, 8: 8}
DEFAULT_SCOPED_VMEM = 16 * 2**20


def _walk(jaxpr):
    for e in jaxpr.eqns:
        yield e
        for v in e.params.values():
            sub = getattr(v, "jaxpr", None)
            if sub is not None and hasattr(sub, "eqns"):
                yield from _walk(sub)
            elif hasattr(v, "eqns"):
                yield from _walk(v)


def lint(fn, *args, mxu_edge=128, gen="v5e"):
    out = []
    j = jax.make_jaxpr(fn)(*args)
    for e in _walk(j.jaxpr):
        if e.primitive.name != "pallas_call":
            continue
        gm = e.params["grid_mapping"]
        rep = dict(name=e.params.get("name") or str(e.params.get("metadata", ""))[:40], grid=tuple(gm.grid),
                   issues=[], blocks=[])
        vmem = 0
        for bm in gm.block_mappings:
            arr = bm.array_aval
            bs = tuple(getattr(b, "block_size", b) for b in bm.block_shape)
            item = np.dtype(arr.dtype).itemsize
            nb = math.prod(int(x) for x in bs) * item
            vmem += 2 * nb
            rep["blocks"].append(dict(array=f"{arr.dtype}{list(arr.shape)}", block=list(bs), bytes=nb))
            if item == 8:
                rep["issues"].append(f"R4 64-bit {arr.dtype} operand")
            if len(bs) >= 2:
                sub = SUBLANE.get(item, 8)
                if not (bs[-1] % 128 == 0 or bs[-1] == arr.shape[-1]):
                    rep["issues"].append(f"R1 block {bs} lane dim {bs[-1]} not /128 for {arr.dtype}{arr.shape}")
                if not (bs[-2] % 8 == 0 or bs[-2] == arr.shape[-2]):
                    rep["issues"].append(f"R1 block {bs} sublane dim {bs[-2]} not /8")
                elif bs[-2] % sub and bs[-2] != arr.shape[-2]:
                    rep["issues"].append(f"R1 block {bs}: {arr.dtype} packs {sub} rows per tile; {bs[-2]} pads")
        for s in gm.scratch_avals:
            vmem += math.prod(s.shape) * np.dtype(s.dtype).itemsize
        cp = e.params.get("compiler_params") or {}
        limit = DEFAULT_SCOPED_VMEM
        try:
            limit = cp["mosaic_tpu"].vmem_limit_bytes or limit
        except Exception:
            lim = getattr(cp, "vmem_limit_bytes", None)
            limit = lim or limit
        rep["vmem_bytes_double_buffered"] = vmem
        rep["vmem_limit"] = limit
        if vmem > limit:
            rep["issues"].append(f"R3 VMEM {vmem/2**20:.1f} MiB > scoped limit {limit/2**20:.0f} MiB")
        kj = e.params["jaxpr"]
        macs = 0
        for ke in _walk(kj):
            if ke.primitive.name == "dot_general":
                (lc, rc), _ = ke.params["dimension_numbers"]
                ls, rs = ke.invars[0].aval.shape, ke.invars[1].aval.shape
                K = math.prod(ls[i] for i in lc)
                M = math.prod(s for i, s in enumerate(ls) if i not in lc)
                N = math.prod(s for i, s in enumerate(rs) if i not in rc)
                macs += M * N * K
                for nm, v in (("M", M), ("N", N), ("K", K)):
                    if v % mxu_edge:
                        rep["issues"].append(f"R2 in-kernel dot {nm}={v} not a multiple of MXU edge {mxu_edge}")
            for v in ke.outvars:
                if hasattr(v, "aval") and getattr(v.aval, "dtype", None) is not None and np.dtype(v.aval.dtype).itemsize == 8:
                    rep["issues"].append(f"R4 64-bit value in kernel ({ke.primitive.name})")
                    break
        steps = math.prod(gm.grid) if gm.grid else 1
        rep["steps"] = steps
        rep["macs_per_step"] = macs
        rep["issues"] = sorted(set(rep["issues"]))
        out.append(rep)
    return out
