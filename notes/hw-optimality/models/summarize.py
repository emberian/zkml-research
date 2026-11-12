"""Join every tool's output with our measurements; print the comparison tables (out/summary.txt).
usage: python3 -I summarize.py <models dir>"""
import json, sys, pathlib
here = pathlib.Path(sys.argv[1]); sys.path.insert(0, str(here))
from devices import DEV
sh = {s["name"]: s for s in json.load(open(here / "shapes.json"))["gemm"]}
tpu_static = json.load(open(here / "shapes.json"))["tpu_static"]
L = {(r["device"], r["shape"], r["dtype"]): r for r in json.load(open(here / "out/llmcompass.json"))}
N = {(r["device"], r["variant"], r["shape"]): r for r in json.load(open(here / "out/neusight.json"))}
A = {(r["sku"], r["dtype"], r["shape"]): r for r in json.load(open(here / "out/aiconfigurator_gemm.json")) if "shape" in r}

def roof(dev, s, dtype, bw=None):
    """Clean roofline: compulsory bytes (operands once, int32/f16 output once) and dense datasheet peak."""
    d = DEV[dev]; ib = 2 if dtype == "fp16" else 1; ob = 2 if dtype == "fp16" else 4
    b, M, Nn, K = s["batch"], s["M"], s["N"], s["K"]
    macs = b * M * Nn * K; byts = b * (ib * (M * K + K * Nn) + ob * M * Nn)
    peak = d.get(dtype) if dtype in d else d.get("int8")
    if dev.startswith("v") and dtype == "fp16": peak = d["bf16"]
    if not peak: return None, None
    tc, mem = macs / peak, byts / (bw or d["hbm"])
    return max(tc, mem), ("tc" if tc > mem else "hbm")

f = lambda x: "-" if x is None else f"{x * 1e3:.4g}"
r = lambda a, b: "-" if (a is None or not b) else f"{a / b:.2f}"
lines = ["== T4: predicted / measured (ms; ratio = predicted/measured) ==",
         f"{'shape':22} {'meas':>8} {'roof@DS':>8} {'r':>5} {'roof@copy':>9} {'r':>5} {'LLMC sim':>9} {'r':>5} {'NeuS fp32':>9} {'r':>5} {'NeuS tcpk':>9} {'r':>5}"]
for n, s in sh.items():
    if "t4_measured_s" not in s: continue
    m = s["t4_measured_s"]; dt = s["dtype"]
    a, _ = roof("T4", s, dt); c, _ = roof("T4", s, dt, 242e9)
    l = L.get(("T4", n, dt), {}).get("sim_s"); nf = N.get(("T4", "fp32_config", n), {}).get("pred_s")
    nt = N.get(("T4", "tensor_peak_as_SingleFLOPs", n), {}).get("pred_s")
    lines.append(f"{n:22} {f(m):>8} {f(a):>8} {r(a, m):>5} {f(c):>9} {r(c, m):>5} {f(l):>9} {r(l, m):>5} {f(nf):>9} {r(nf, m):>5} {f(nt):>9} {r(nt, m):>5}")
lines.append("  (LLMCompass on T4@copy-bandwidth:) " + ", ".join(
    f"{n} {r(L.get(('T4@copy', n, sh[n]['dtype']), {}).get('sim_s'), sh[n]['t4_measured_s'])}" for n in sh if "t4_measured_s" in sh[n]))

lines += ["", "== Paid SKUs: predictions (ms). roof = clean roofline at datasheet peak; LLMC = LLMCompass heuristic-GPU;",
          "   NVIDIA-measured = aiconfigurator silicon table (TRT-LLM torch_flow, interpolated; fp8 rows include its quant path) ==",
          f"{'sku':5} {'shape':22} {'dtype':6} {'roof':>8} {'bound':>5} {'LLMC':>8} {'aic meas':>9} {'LLMC/aic':>8} {'roof/aic':>8}"]
for dev in ("A100", "H100", "B200", "B300"):
    for n, s in sh.items():
        if n.startswith("xla") or n == "cublas_f16_8192": continue
        for dt in ("int8", "fp8"):
            if dt == "fp8" and dev == "A100": continue
            a, u = roof(dev, s, dt); l = L.get((dev, n, dt), {}).get("sim_s")
            aic = A.get((dev, {"int8": "sq", "fp8": "fp8"}[dt], n), {}).get("measured_interp_s")
            if dev != "A100" and dt == "int8": aic = None    # no W8A8 INT8 table for H100/B200/B300
            lines.append(f"{dev:5} {n:22} {dt:6} {f(a):>8} {u or '-':>5} {f(l):>8} {f(aic):>9} {r(l, aic):>8} {r(a, aic):>8}")

lines += ["", "== TPU: LLMCompass vs the libtpu compiler (deviceless, hbox) and tpuperf's bound (ms) ==",
          f"{'gen':4} {'shape':22} {'LLMC roof':>9} {'LLMC sim':>9} {'clean roof':>10} {'tpuperf bnd':>11} {'compiler opt_s':>14}"]
for g in ("v5e", "v6e"):
    for n in ("xla_i8_1024", "gptoss_gateup_T2048", "gptoss_down_T2048", "gptoss_gateup_T256"):
        lr = L.get((g, n, "int8"), {}); a, _ = roof(g, sh[n], "int8")
        ts = tpu_static.get(n, {}).get(g, {})
        opt = sh[n].get("tpu_v5e_optimal_seconds") if (n.startswith("xla") and g == "v5e") else ts.get("optimal_seconds")
        lines.append(f"{g:4} {n:22} {f(lr.get('roofline_s')):>9} {f(lr.get('sim_s')):>9} {f(a):>10} {f(ts.get('tpuperf_bound_s')):>11} {f(opt):>14}"
                     + ("   <- Pallas custom call: compiler does not cost it" if ts else ""))
out = "\n".join(lines); print(out); (here / "out/summary.txt").write_text(out + "\n")
