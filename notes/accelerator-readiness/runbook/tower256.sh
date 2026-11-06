#!/usr/bin/env bash
# Workload 2 (initiative 17): the Tower256 additive-FRI prover (minidregg work 9104) on one GPU box.
#
# Run from an unpacked bundle (tower256-bundle.sh makes it from the minidregg lane branch
# lane/accel-tower256-gpu): tower256.sh, common.sh, cuda/, lean/, prover/ (standalone crate) or bin/.
#
#   bash tower256.sh [--shrink] [--offline] [--rust-bin PATH] [--sku H100] [--any-gpu]
#
# --shrink   the T4 dry-run parameters (what ran on Kaggle): ell 10..20, batch 64 words at ell 14.
# --offline  no venv, no pip, no rustup: system python3 must have cupy + numpy; needs --rust-bin.
# Full run (default): ell 14..22, batch 512 words at ell 14 and 64 at ell 18; CPU reference and
# CPU timings on this box's cores (1 thread and all of them).
#
# Steps: hardware check; Python env (pinned); Rust toolchain (pinned) and the CPU prover; CPU
# reference receipts + CPU timings (tower256_fri_fast_bench --emit, plus the conformance kernel
# at ell 8 and 10); nvcc (or NVRTC) build for this GPU's arch; the GPU run with every bit-exact
# check; results.json in $OUT. Wall limit 3000 s, no-output limit 600 s.
HERE=$(cd "$(dirname "$0")" && pwd)
. "$HERE/common.sh"
accel_init tower256 "$@"
OFFLINE=0; RUST_BIN=""; SKU=H100
while (( $# )); do
  case $1 in
    --offline) OFFLINE=1;;
    --rust-bin) RUST_BIN=$2; shift;;
    --sku) SKU=$2; shift;;
  esac
  shift
done
if (( SHRINK )); then
  ELLS=10,12,14,16,18,20; BATCH=64; BATCH_ELL=14; BATCH2=0; REPS=3; [[ $SKU == H100 ]] && SKU=T4
else
  ELLS=14,16,18,20,22; BATCH=512; BATCH_ELL=14; BATCH2=64; REPS=3
fi
accel_hw_check "$SKU"
cd "$OUT"
echo "out $OUT shrink $SHRINK ells $ELLS"

# Python.
if (( OFFLINE )); then
  PY=python3
else
  python3 -m venv "$OUT/venv"
  PY="$OUT/venv/bin/python"
  CUDA_MAJOR=$(nvidia-smi | sed -n 's/.*CUDA Version: \([0-9]*\).*/\1/p' | head -1)
  CUPY=cupy-cuda12x==13.6.0; [[ ${CUDA_MAJOR:-12} -ge 13 ]] && CUPY=cupy-cuda13x==14.0.1
  "$PY" -m pip install -q --upgrade pip==25.2
  "$PY" -m pip install -q numpy==2.1.3 pycryptodome==3.23.0 "$CUPY"
fi
# Test hook: ACCEL_TOWER256_EMU_LIB=<host-emulation build of cuda/tower256_fri.cu> runs the same
# host code on the CPU emulation (no GPU); only for checking this script off-GPU.
EMU_LIB=${ACCEL_TOWER256_EMU_LIB:-}
if [[ -z $EMU_LIB ]]; then
  "$PY" -c "import cupy, numpy; print('cupy', cupy.__version__, 'numpy', numpy.__version__)"
fi
"$PY" -c "import Crypto; print('pycryptodome', Crypto.__version__)" || echo "pycryptodome absent: host Python Keccak is the hash reference"

# Rust: the CPU prover (reference receipts and CPU timings).
if [[ -z $RUST_BIN ]]; then
  if (( OFFLINE )); then echo "--offline needs --rust-bin"; exit 2; fi
  export RUSTUP_HOME="$OUT/rustup" CARGO_HOME="$OUT/cargo"
  curl -sSf https://sh.rustup.rs | sh -s -- -y -q --profile minimal --default-toolchain 1.89.0 --no-modify-path
  export PATH="$CARGO_HOME/bin:$PATH"
  ( cd "$HERE/prover" && RUSTFLAGS="-C target-cpu=native" CARGO_TARGET_DIR="$OUT/target" \
      cargo build --release --locked --bin tower256_fri_fast_bench )
  RUST_BIN="$OUT/target/release/tower256_fri_fast_bench"
fi
NPROC=$(nproc)
mkdir -p "$OUT/data"
cp "$HERE/lean/tower256_fri_vectors.json" "$OUT/data/"
echo "== CPU reference and timings"
accel_run 3000 600 bash -c "'$RUST_BIN' --ell 8,10 --threads 1 --reps 1 --emit '$OUT/data' --reference-max-ell 10 > '$OUT/rust_reference.jsonl' && '$RUST_BIN' --ell $ELLS --threads 1,$NPROC --reps 2 --emit '$OUT/data' > '$OUT/rust_cpu.jsonl'"
cat "$OUT/rust_reference.jsonl" "$OUT/rust_cpu.jsonl"

# GPU build.
CC=$(nvidia-smi --query-gpu=compute_cap --format=csv,noheader | head -1 | tr -d .)
NVCC=$(command -v nvcc || true); [[ -z $NVCC && -x /usr/local/cuda/bin/nvcc ]] && NVCC=/usr/local/cuda/bin/nvcc
if [[ -n $EMU_LIB ]]; then
  GPU_SRC=(--backend emu --lib "$EMU_LIB")
elif [[ -n $NVCC ]]; then
  "$NVCC" --version | tail -2
  "$NVCC" -arch=sm_$CC -O3 -cubin -Xptxas -v -o "$OUT/tower256_fri.cubin" "$HERE/cuda/tower256_fri.cu" > "$OUT/ptxas.txt" 2>&1
  tail -n 60 "$OUT/ptxas.txt"
  GPU_SRC=(--cubin "$OUT/tower256_fri.cubin")
else
  echo "no nvcc: NVRTC through cupy"
  GPU_SRC=(--source "$HERE/cuda/tower256_fri.cu")
fi

echo "== GPU"
accel_run 3000 600 "$PY" "$HERE/cuda/tower256_gpu.py" --data "$OUT/data" --ells "$ELLS" --reps $REPS \
  --batch $BATCH --batch-ell $BATCH_ELL "${GPU_SRC[@]}" --out "$OUT/results.json"
if (( BATCH2 )); then
  accel_run 3000 600 "$PY" "$HERE/cuda/tower256_gpu.py" --data "$OUT/data" --ells "" --reps $REPS \
    --batch $BATCH2 --batch-ell 18 "${GPU_SRC[@]}" --out "$OUT/results_batch18.json"
fi

# One results file: GPU checks and timings, the CPU timings and reference agreement, ptxas.
"$PY" - "$OUT" <<'PYEOF'
import json, pathlib, sys
out = pathlib.Path(sys.argv[1])
res = json.loads((out / "results.json").read_text())
res["rust_cpu"] = [json.loads(l) for l in (out / "rust_cpu.jsonl").read_text().splitlines() if l.startswith("{")]
res["rust_reference"] = [json.loads(l) for l in (out / "rust_reference.jsonl").read_text().splitlines() if l.startswith("{")]
if (out / "results_batch18.json").exists():
    res["batch_ell18"] = json.loads((out / "results_batch18.json").read_text()).get("batch")
p = out / "ptxas.txt"
res["ptxas"] = [l.strip() for l in p.read_text().splitlines() if "registers" in l or "spill" in l][:80] if p.exists() else "nvrtc"
res["box"] = json.loads((out / "box.json").read_text())
res["cpu_model"] = next((l.split(":", 1)[1].strip() for l in open("/proc/cpuinfo") if l.startswith("model name")), "?")
res["nproc"] = len([l for l in open("/proc/cpuinfo") if l.startswith("processor")])
ref_ok = all(r.get("identical") for r in res["rust_reference"] if r.get("kind") == "reference")
res["cpu_reference_identical"] = ref_ok
res["all_bit_exact"] = bool(res.get("all_bit_exact")) and ref_ok
(out / "results.json").write_text(json.dumps(res, indent=1))
print("ALL_BIT_EXACT", res["all_bit_exact"])
PYEOF
echo "done in $(( $(date +%s) - T0 )) s; results $OUT/results.json"
