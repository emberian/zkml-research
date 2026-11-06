"""%-of-bound table from a Kaggle results.json (profile.py), with bounds recomputed here from the current
counts.py and the MEASURED calibration (VPU rate, HBM bandwidth) as well as the published peaks.

    python -m tpuperf.report RESULTS.json  > table.md
"""
import json
import sys

import jax

from . import counts as C
from .hw import GEN
from .registry import KERNELS


def main(path):
    R = json.load(open(path))
    cal = R["sections"].get("calib", {})
    vpu = cal.get("vpu_int32_ops_per_s_reduction_mix")
    hbm = max(cal.get("hbm_copy_GBps", 0), cal.get("hbm_read_GBps", 0)) * 1e9 or None
    print(f"device {R.get('device_kind')} jax {R.get('jax')}\n")
    print("| calibration | measured | published / assumed |\n|---|---|---|")
    g = GEN["v5e"]
    rows = [("HBM copy (r+w) GB/s", cal.get("hbm_copy_GBps"), g["hbm_bw"] / 1e9),
            ("HBM read GB/s", cal.get("hbm_read_GBps"), g["hbm_bw"] / 1e9),
            ("VPU int32 ops/s (mul-add-shift-xor)", cal.get("vpu_int32_ops_per_s"), g["vpu_ops"]),
            ("VPU int32 ops/s (reduction mix)", vpu, g["vpu_ops"]),
            ("grid step s (1024 / 8192 steps)", (cal.get("grid_step_s_1024"), cal.get("grid_step_s_8192")), "0.35e-6 [INFERRED]"),
            ("XLA int8 1024^3 TOPS", cal.get("xla_int8_1024_TOPS"), g["int8"] / 1e12),
            ("XLA int8 4096^3 TOPS", cal.get("xla_int8_4096_TOPS"), g["int8"] / 1e12),
            ("XLA int8 8192^3 TOPS", cal.get("xla_int8_8192_TOPS"), g["int8"] / 1e12),
            ("Pallas int8 8192^3 TOPS", cal.get("pallas_int8_8192_TOPS"), g["int8"] / 1e12),
            ("XLA bf16 8192^3 TFLOPS", cal.get("xla_bf16_8192_TFLOPS"), g["bf16"] / 1e12)]
    for name, m, p in rows:
        print(f"| {name} | {m} | {p} |")
    print("\n| kernel | config | exact | measured us | bound us (unit), published peaks + measured VPU | % of bound |"
          " bound us with measured HBM | % |\n|---|---|---|---|---|---|---|---|")
    for r in R["sections"].get("kernels", []):
        if "error" in r:
            print(f"| {r['kernel']} | {r['cfg']} | ERROR | {r['error'].strip().splitlines()[-1][:80]} | | | | |")
            continue
        k = KERNELS[r["kernel"]]
        cf, cs = k["count"](**r["params"])
        cnt = C.counts(cf, *[jax.ShapeDtypeStruct(s, d) for s, d in cs])
        b = C.bound(cnt, "v5e", vpu_ops=vpu)
        t = r["t_meas_s"]
        b2 = dict(b["per_unit_s"])
        if hbm:
            b2["hbm"] = (cnt["hbm_in"] + cnt["hbm_out"]) / hbm
        u2 = max(b2, key=b2.get)
        print(f"| {r['kernel']} | {r['cfg']} | {r.get('exact')} | {t*1e6:.1f} | {b['bound_s']*1e6:.1f} ({b['unit']}) | "
              f"{100*b['bound_s']/t:.1f} | {b2[u2]*1e6:.1f} ({u2}) | {100*b2[u2]/t:.1f} |")
    x = R["sections"].get("xla", {})
    if x:
        print(f"\nXLA formulations: NTT {x.get('ntt_xla_s', 0)*1e6:.0f} us, sumcheck {x.get('sumcheck_xla_s', 0)*1e6:.0f} us")


if __name__ == "__main__":
    main(sys.argv[1])
