#!/usr/bin/env python3
"""mma_t4_model.py -- the F3 counts model (notes/construction-search/mma_counts.py) rescaled to a Kaggle T4 and
compared with the T4 dry-run measurements (initiative 17, workload 3).  stdlib only.

    python3 -I notes/accelerator-readiness/mma_t4_model.py runs/accel-mma-t4-dry-02/results.json [...]

T4 rates are datasheet values [A: NVIDIA T4 datasheet, not re-read here] except the clock, which the env probe
read from nvidia-smi (clocks.max.sm 1590 MHz) [MEASURED].  The model is imported, not copied: inner_product()
and floor_s() are mma_counts.py's own.  Acceptance (degg-research mma-accumulator-probe README): within 1.5x of
the floor; refuted if a primitive the model calls HBM-bound runs more than 2x above copy bandwidth.
"""
import importlib.util
import json
import pathlib
import sys

HERE = pathlib.Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("mma_counts", HERE.parent / "construction-search" / "mma_counts.py")
mc = importlib.util.module_from_spec(spec)
spec.loader.exec_module(mc)

T4 = dict(int8=130e12 / 2, fp8=None, fp4=None, b1=None, fp16=65e12 / 2, bw=320e9, simt=40 * 64 * 1.59e9,
          src="[A: T4 datasheet dense 130 TOPS INT8, 65 TFLOPS FP16, 320 GB/s GDDR6; 40 SM x 64 INT32 lanes x "
              "1.59 GHz (clocks.max.sm MEASURED by accel-env-probe-t4-01); b1 rate unpublished]")
mc.SKUS["T4"] = T4


def floor_ms(sku, c, bw=None):
    s = dict(mc.SKUS[sku])
    if bw:
        s["bw"] = bw
    terms = {"hbm": c["bytes"] / s["bw"], "simt": c["simt"] / s["simt"], "tc": c["macs"] / s["int8"]}
    b = max(terms, key=terms.get)
    return terms[b] * 1e3, b, {k: v * 1e3 for k, v in terms.items()}


def main(paths):
    for p in paths:
        r = json.loads(pathlib.Path(p).read_text())
        cp = r.get("copy", {})
        bw_copy, bw_read = cp.get("copy_rw_bytes_per_s"), cp.get("read_bytes_per_s")
        print(f"\n== {p}: {r.get('device')} ({r.get('arch')}), checks {r.get('n_checks')} failed {r.get('n_failed')}")
        print(f"  copy (read+write) {bw_copy / 1e9:.1f} GB/s = {bw_copy / T4['bw']:.2f} of the 320 GB/s datasheet; "
              f"streaming read {bw_read / 1e9:.1f} GB/s")
        rates = r.get("rates_sm75", {})
        peak = r.get("peak", {})
        if rates:
            u8 = rates["u8"]["macs_per_s"]
            print(f"  mma.sync u8 {u8:.3e} MAC/s = {u8 / T4['int8']:.2f} of datasheet INT8; "
                  f"cuBLAS i8 8192^3 {peak.get('i8', {}).get('macs_per_s', 0):.3e} MAC/s; "
                  f"f16 mma.sync {rates['f16']['macs_per_s']:.3e} = {rates['f16']['macs_per_s'] / T4['fp16']:.2f} of datasheet")
            print(f"  b1 / u8 = {rates['b1']['macs_per_s'] / u8:.2f} (A100 published binary/INT8 = 8.00); "
                  f"u4 / u8 = {rates['u4']['macs_per_s'] / u8:.2f} (datasheet 2.00); "
                  f"lop3 {rates['lop3']['lop3_per_s']:.3e}/s = {rates['lop3']['lop3_per_s'] / T4['simt']:.2f} of the model's SIMT rate")
        print("  BabyBear^8 inner product V^T U (INT8 limbs, 32 x 32768 x 32 per batch), model vs measured:")
        print(f"  {'N':>6} {'floor ms':>9} {'bound':>5} {'tc ms':>7} {'floor@copy':>10} {'measured':>9} "
              f"{'x floor':>8} {'x copy':>7} {'verdict':>9}")
        for x in r.get("i8ip", []):
            if x.get("status") != "SUCCESS":
                continue
            N = 1 << x["logn"]
            c = mc.inner_product("BabyBear^8", "int8", N)
            f, b, t = floor_ms("T4", c)
            fc, _, _ = floor_ms("T4", c, bw_copy)
            ms = x["ms"]
            verdict = "within" if ms <= 1.5 * f else ("refuted" if ms > 2 * fc else "outside")
            print(f"  2^{x['logn']:<4} {f:9.3f} {b:>5} {t['tc']:7.3f} {fc:10.3f} {ms:9.3f} {ms / f:8.2f} {ms / fc:7.2f} {verdict:>9}")
        for x in r.get("ltip", []):
            if x.get("status") != "SUCCESS":
                continue
            N = 1 << x["logn"]
            by = x["bytes_read"]
            f = by / T4["bw"] * 1e3
            fc = by / bw_copy * 1e3
            print(f"  f16 limbs 2^{x['logn']}: {by / 2**30:.2f} GiB read, floor {f:.3f} ms (copy {fc:.3f}), measured "
                  f"{x['ms']:.3f} ms = {x['ms'] / f:.2f}x floor, {x['ms'] / fc:.2f}x copy")
    print("\nModel predictions on the paid SKUs (mma_counts.py, unchanged), inner product at 2^25:")
    c = mc.inner_product("BabyBear^8", "int8", 1 << 25)
    for sku in ("H100", "B200", "B300"):
        f, b, t = floor_ms(sku, c)
        print(f"  {sku}: floor {f:.3f} ms ({b}); tc term {t['tc']:.3f} ms; acceptance <= {1.5 * f:.3f} ms")


if __name__ == "__main__":
    main(sys.argv[1:] or [str(HERE / "runs" / "accel-mma-t4-dry-02" / "results.json")])
