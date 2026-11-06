"""Static check of every workload kernel against the REAL TPU compiler, deviceless (hbox, libtpu installed).

    python -m tpuperf.static_check [--gens v5e v6e] [--only NAME] [--out DIR]

Per kernel x config x generation:
  bound      from the pre-optimization StableHLO counts (counts.py) and the published peaks (hw.py)
  compile    jit(...).lower(ShapeDtypeStructs on a topology device).compile(): optimized TPU HLO,
             cost_analysis, memory_analysis; the HLO is saved under OUT/hlo/
  inspect    inspect_hlo.py findings (relayout copies, transposes, padding, non-MXU dots, 64-bit, loops)
  lint       pallas_lint.py on the kernel's jaxpr
  compiler   sum of the compiler's own per-fusion estimated_cycles, at the inferred clock, vs the bound
Writes OUT/static.json and prints a table. The compiler estimate is a model, never a measurement.
"""
import argparse
import json
import os
import pathlib
import sys
import time
import traceback

import jax
from jax.experimental import topologies
from jax.sharding import SingleDeviceSharding

from . import counts as C
from .hw import GEN
from .inspect_hlo import inspect
from .pallas_lint import lint
from .registry import KERNELS


def specs(dev, arg_specs):
    shd = SingleDeviceSharding(dev)
    return [jax.ShapeDtypeStruct(s, d, sharding=shd) for s, d in arg_specs]


def check_one(k, cfg_name, p, gen, dev, outdir):
    g = GEN[gen]
    edge = g["mxu"][0]
    row = dict(kernel=k["name"], cfg=cfg_name, gen=gen, params=p)
    cf, cspecs = k["count"](**p)
    cnt = C.counts(cf, *[jax.ShapeDtypeStruct(s, d) for s, d in cspecs])
    row["counts"] = cnt
    row["bound"] = C.bound(cnt, gen)
    fn = k["impl"](**p)
    args = specs(dev, k["arg_specs"](**p))
    try:
        row["lint"] = lint(fn, *[jax.ShapeDtypeStruct(a.shape, a.dtype) for a in args], mxu_edge=edge, gen=gen)
    except Exception as e:
        row["lint"] = [dict(error=repr(e)[:300])]
    t0 = time.time()
    try:
        c = jax.jit(fn).lower(*args).compile()
    except Exception:
        row["compile_error"] = traceback.format_exc()[-1500:]
        return row
    row["compile_s"] = round(time.time() - t0, 1)
    txt = c.as_text()
    hp = outdir / "hlo" / f"{k['name']}.{cfg_name}.{gen}.txt"
    hp.write_text(txt)
    ca = c.cost_analysis()
    ca = ca[0] if isinstance(ca, list) else ca
    row["cost_analysis"] = {kk: ca.get(kk) for kk in ("flops", "bytes accessed", "optimal_seconds")}
    ma = c.memory_analysis()
    row["memory"] = {a: getattr(ma, a) for a in ("argument_size_in_bytes", "output_size_in_bytes",
                                                    "temp_size_in_bytes", "generated_code_size_in_bytes")}
    hbm_need = sum(row["memory"][a] for a in ("argument_size_in_bytes", "output_size_in_bytes", "temp_size_in_bytes"))
    row["fits_hbm"] = hbm_need <= g["hbm_bytes"]
    ins = inspect(txt, mxu_edge=edge)
    row["inspect"] = {kk: ins[kk] for kk in ("summary", "est_cycles_entry", "scoped_vmem_max", "async_prefetch",
                                             "n_instructions", "entry_fusions")}
    row["inspect"]["findings_head"] = ins["findings"][:12]
    # Mosaic (Pallas) custom calls carry no estimated_cycles: the compiler estimate then omits the kernel itself
    row["compiler_est_s"] = (ins["est_cycles_entry"] / g["clock_hz"]
                             if ins["est_cycles_entry"] and ins["compiler_estimate_covers_mosaic"] else None)
    if row["compiler_est_s"]:
        row["bound_over_compiler_est"] = row["bound"]["bound_s"] / row["compiler_est_s"]
    return row


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--gens", nargs="*", default=["v5e", "v6e"])
    ap.add_argument("--only", nargs="*")
    ap.add_argument("--out", default="static-out")
    a = ap.parse_args()
    out = pathlib.Path(a.out)
    (out / "hlo").mkdir(parents=True, exist_ok=True)
    rows = []
    for gen in a.gens:
        dev = topologies.get_topology_desc(platform="tpu", topology_name=GEN[gen]["topology"]).devices[0]
        for name, k in KERNELS.items():
            if a.only and name not in a.only:
                continue
            for cfg_name, p in k["cfgs"].items():
                if cfg_name == "mac":
                    continue
                r = check_one(k, cfg_name, p, gen, dev, out)
                rows.append(r)
                b = r["bound"]
                est = r.get("compiler_est_s")
                print(f"{gen} {name:22s} {cfg_name:14s} bound {b['bound_s']*1e6:10.1f} us ({b['unit']:4s})  "
                      f"compiler est {est*1e6 if est else float('nan'):10.1f} us  "
                      f"{'COMPILE ERROR' if 'compile_error' in r else r['inspect']['summary']}", flush=True)
                (out / "static.json").write_text(json.dumps(rows, indent=1, default=str))


if __name__ == "__main__":
    main()
