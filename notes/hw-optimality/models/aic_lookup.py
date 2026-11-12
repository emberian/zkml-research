"""Measured GEMM tables from NVIDIA aiconfigurator (ai-dynamo/aiconfigurator @6cd6f96, Apache-2.0):
aic-core/src/aiconfigurator_core/systems/data/<sku>/gemm/trtllm/<ver>/gemm_perf.parquet, latency in ms,
collected on real H100 SXM / B200 / B300 / A100 SXM by NVIDIA (TRT-LLM torch_flow kernels).
Not a model: silicon numbers on a grid. We interpolate log(latency) multilinearly in log(m), log(n), log(k).
usage: python aic_lookup.py <aiconfigurator checkout> <models dir>"""
import sys, json, math, itertools, pathlib
import pandas as pd
root, here = pathlib.Path(sys.argv[1]), pathlib.Path(sys.argv[2])
P = root / "aic-core/src/aiconfigurator_core/systems/data"
TABLES = {"A100": ("a100_sxm", "1.0.0", ["sq", "bfloat16"]),         # sq = SmoothQuant W8A8 INT8 GEMM
          "H100": ("h100_sxm", "1.3.0rc20", ["fp8", "bfloat16"]),
          "B200": ("b200_sxm", "1.3.0rc20", ["fp8", "nvfp4", "bfloat16"]),
          "B300": ("b300_sxm", "1.3.0rc20", ["fp8", "nvfp4", "bfloat16"])}
shapes = [s for s in json.load(open(here / "shapes.json"))["gemm"] if s["batch"] == 1 and not s["name"].startswith("xla")]

def bracket(vals, x):
    lo = max([v for v in vals if v <= x], default=None); hi = min([v for v in vals if v >= x], default=None)
    return [lo] if lo == hi else [v for v in (lo, hi) if v is not None]

out = []
for sku, (d, ver, dtypes) in TABLES.items():
    df = pd.read_parquet(P / d / "gemm/trtllm" / ver / "gemm_perf.parquet")
    df = df[df.kernel_source != "deepgemm"]
    for dt in dtypes:
        t = df[df.gemm_dtype == dt]
        lat = {(r.m, r.n, r.k): r.latency for r in t.itertuples()}
        best = max(((m * n * k) / (l * 1e-3), (m, n, k)) for (m, n, k), l in lat.items())
        row0 = dict(sku=sku, dtype=dt, best_grid_mac_per_s=best[0], best_at=best[1])
        print(json.dumps(row0, default=int)); out.append(row0)
        ms, ns, ks = sorted(t.m.unique()), sorted(t.n.unique()), sorted(t.k.unique())
        for s in shapes:
            bm, bn, bk = bracket(ms, s["M"]), bracket(ns, s["N"]), bracket(ks, s["K"])
            acc, wsum, ok = 0.0, 0.0, True
            for m, n, k in itertools.product(bm, bn, bk):
                if (m, n, k) not in lat:
                    ok = False; break
                w = 1.0
                for v, b, x in ((m, bm, s["M"]), (n, bn, s["N"]), (k, bk, s["K"])):
                    if len(b) == 2:
                        f = (math.log(x) - math.log(b[0])) / (math.log(b[1]) - math.log(b[0]))
                        w *= f if v == b[1] else 1 - f
                # interpolate log of (latency / MACs) so the grid's shape differences cancel to first order
                acc += w * math.log(lat[(m, n, k)] * 1e-3 / (m * n * k)); wsum += w
            if not ok:
                continue
            sec = math.exp(acc / wsum) * s["M"] * s["N"] * s["K"]
            row = dict(sku=sku, dtype=dt, shape=s["name"], measured_interp_s=sec, mac_per_s=s["M"] * s["N"] * s["K"] / sec,
                       grid=[bm, bn, bk])
            print(json.dumps(row, default=int)); out.append(row)
json.dump(out, open(here / "out/aiconfigurator_gemm.json", "w"), indent=1, default=int)
