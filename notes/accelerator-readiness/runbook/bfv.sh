#!/usr/bin/env bash
# Workload 1 (dark-learning BFV, initiative 17): RNS NTT tuning sweep + he_outer / he_matvec return pipeline,
# bit-exact against bfv_ref, on a fresh H100 / H200 / B200 box. Lane w1-bfv, 2026-11-06. Notes: ../BFV.md.
#
#   bash bfv.sh [--sku H100|H200|B200] [--any-gpu] [--shrink] [--no-venv]
#
#   --shrink   exactly the Kaggle T4 dry run (accel_bfv_run.py --shrink: quick sweep, 2 checked returns,
#              smaller batches); the full run sweeps every shape and checks 3 returns per (N, L).
#   --no-venv  use python3 on PATH as is (Kaggle, where cupy is preinstalled and there is no internet).
# Needs: NVIDIA driver, python3 (+ venv), internet for pip. No CUDA toolkit: cupy compiles with NVRTC from
# the pinned wheels. Writes $OUT/{box.json,env.txt,log.txt,results.json,src/,job.pid}; OUT defaults to
# ~/accel-results/bfv-<utc>. Wall: 3000 s full (< 1 h with setup), 1200 s shrink; stall 600 s.
HERE=$(cd "$(dirname "$0")" && pwd)
. "$HERE/common.sh"
accel_init bfv "$@"
SKU=H100; NOVENV=0
args=("$@")
for ((i = 0; i < ${#args[@]}; i++)); do
  case ${args[$i]} in
    --sku) SKU=${args[$((i + 1))]} ;;
    --no-venv) NOVENV=1 ;;
  esac
done
SRC=$(cd "$HERE/../../../research/dark_learning_2026_11_06" && pwd)
FILES="accel_bfv_run.py accel_bench_cuda.py accel_he_bench.py accel_rns_ref.py accel_rns_ntt.cu bfv_ref.py he_matvec.py he_outer.py spdz.py"
accel_hw_check "$SKU"

if [[ $NOVENV == 0 ]]; then
  CUDA_MAJOR=$(nvidia-smi | sed -n 's/.*CUDA Version: *\([0-9]*\).*/\1/p' | head -1)
  accel_venv "$OUT/venv"
  # Pins: cupy 14.0.1 (the version measured on Kaggle, cupy-cuda13x) with its CUDA components from PyPI ([ctk]:
  # NVRTC + headers, no system toolkit needed); numpy 2.1.3 as on Kaggle. cuda12x for CUDA-12 drivers.
  if [[ ${CUDA_MAJOR:-12} -ge 13 ]]; then CUPY="cupy-cuda13x[ctk]==14.0.1"; else CUPY="cupy-cuda12x[ctk]==14.0.1"; fi
  "${PIP[@]}" install -q "numpy==2.1.3" "$CUPY" 2>&1 | tail -5
else
  PY=python3
fi
"$PY" - > "$OUT/env.txt" 2>&1 <<'PYEOF' || { cat "$OUT/env.txt"; echo "cupy smoke test failed"; exit 2; }
import sys, numpy, cupy
print("python", sys.version.split()[0], "numpy", numpy.__version__, "cupy", cupy.__version__)
print("cuda runtime", cupy.cuda.runtime.runtimeGetVersion(), "driver", cupy.cuda.runtime.driverGetVersion())
k = cupy.RawKernel(r'extern "C" __global__ void f(unsigned long long* x){ x[0] = __umul64hi(x[0], x[0]); }', "f")
x = cupy.array([2**63 + 12345], dtype=cupy.uint64); k((1,), (1,), (x,))
assert int(x.get()[0]) == ((2**63 + 12345) ** 2) >> 64, "umul64hi"
print("nvrtc compile + umul64hi OK")
PYEOF
cat "$OUT/env.txt"

mkdir -p "$OUT/src"
for f in $FILES; do cp "$SRC/$f" "$OUT/src/"; done
(cd "$OUT/src" && sha256sum $FILES > SHA256SUMS)
cd "$OUT/src"
if [[ $SHRINK == 1 ]]; then WALL=1200; RUNARGS="--shrink"; else WALL=3000; RUNARGS=""; fi
rc=0
ACCEL_RESULTS="$OUT/results.json" accel_run $WALL 600 "$PY" -u accel_bfv_run.py $RUNARGS || rc=$?
"$PY" - "$OUT/results.json" <<'PYEOF' || true
import json, sys
r = json.load(open(sys.argv[1]))
print("device", r.get("device"), "all_exact", r.get("all_exact"), "elapsed_s", round(r.get("elapsed_s", 0)))
for k, v in r.get("he", {}).items():
    b = v["shape"]
    print("%-10s check %-5s NTT %.2f us (%s E=2^%d th=%d G=%d)  return %.1f us  step %.2f s (per party %.2f s)" % (
        k, v["check"]["ok"], v["us_per_ntt"], b["mode"], b["logE"], b["threads"], b["G"],
        v["outer"]["us_per_return"]["return_total"], v["step"]["step_s"], v["step"]["per_party_step_s"]))
PYEOF
echo "results in $OUT (rc $rc)"
exit $rc
