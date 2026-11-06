#!/usr/bin/env bash
# Workload 3 (initiative 17): the tensor-core exactness probe and the one-hour GPU protocol of
# degg-research experiments/mma-accumulator-probe/README.md, on one paid box.
#
# Run from an unpacked bundle (mma-bundle.sh makes it from a degg-research commit): mma.sh, common.sh,
# src/ (probe.cu, probe_sm75.cu, probe_sm80.cu, gemm_probe.cu, mma_run.py + MANIFEST with sha256s).
#
#   bash mma.sh [--sku B300|B200|H100|T4] [--shrink] [--any-gpu] [--toolkit auto|system|conda]
#               [--no-cutlass] [--gpu N]
#
# --shrink   exactly the Kaggle T4 dry-run parameters (mma_run.py --shrink): copy 2 GiB, inner products to
#            2^25 (INT8) and 2^24 (FP16 limbs), 10 reps.  Without it: copy 8 GiB, 2^20..2^25 for every kind, 20 reps.
# --toolkit  auto (default): the system nvcc if it is new enough for this GPU (12.0 for sm_90a, 12.8 for
#            sm_100a, 12.9 for sm_103a), else a pinned conda-forge CUDA 12.9 env (micromamba 2.3.3-0,
#            sha256-checked; no root).  conda: always that env.  system: never download a toolkit.
# --no-cutlass  skip the pinned CUTLASS v4.8.1 step (the probe's own kernels still give the b1 rate).
#
# Protocol steps (README) and where they run:
#   1 hardware, driver, toolkit, builds, compile check for sm_75..sm_103a with a SASS census  -> mma_run.py
#   2 u8/s8 wrap (every boundary), probe.cu as written                                          -> mma_run.py
#   3 accumulator widths: mma.sync fragments (sm_75/80/89), wgmma QGMMA/HGMMA (sm_90a), cuBLASLt
#     f16/e4m3 (fast accum on and off)/e2m1 (sm_100+) gap and count probes; on sm_100/103 also the
#     CUTLASS tcgen05 example GEMMs (fp8, nvfp4) for rate and their own verification              -> mma_run.py, cutlass
#   4 copy bandwidth                                                                            -> gemm_probe copy
#   5 BabyBear^8 inner product: INT8 batched GEMM (every output checked), FP16/FP8 limb GEMMs     -> gemm_probe i8ip/ltip
#   6 b1 rate: own mma.sync (and wgmma on sm_90a) kernels; cutlass_profiler b1 GEMM on sm_75..90a  -> mma_run.py, cutlass
#   7 Keccak-f rate: NOT here.  Workload 2's tower256.sh measures it (results key keccak_f_per_s).
# Wall limit 3300 s (accel_run), no-output limit 600 s.  Results: $OUT/results.json (+ cutlass/*.csv, log.txt).
HERE=$(cd "$(dirname "$0")" && pwd)
. "$HERE/common.sh"
accel_init mma "$@"
SKU=B300; TOOLKIT=auto; CUTLASS=1; GPU=0
while (( $# )); do
  case $1 in
    --sku) SKU=$2; shift;;
    --toolkit) TOOLKIT=$2; shift;;
    --no-cutlass) CUTLASS=0;;
    --gpu) GPU=$2; shift;;
  esac
  shift
done
(( SHRINK )) && [[ $SKU == B300 ]] && SKU=T4
accel_hw_check "$SKU"
SRC="$HERE/src"
cd "$OUT"
echo "out $OUT sku $SKU shrink $SHRINK toolkit $TOOLKIT cutlass $CUTLASS"

# The sources must be the ones that dry-ran: MANIFEST holds their sha256 (written by mma-bundle.sh).
( cd "$SRC" && sha256sum -c MANIFEST )
cp "$SRC/MANIFEST" "$OUT/MANIFEST"

nvidia-smi -q > "$OUT/nvidia-smi-q.txt" 2>&1 || true
CC=$(nvidia-smi -i "$GPU" --query-gpu=compute_cap --format=csv,noheader | tr -d ' .')
DRIVER=$(nvidia-smi -i "$GPU" --query-gpu=driver_version --format=csv,noheader | tr -d ' ')
case $CC in
  75) NEED=11.0; ARCH=75;; 80) NEED=11.0; ARCH=80;; 89) NEED=11.8; ARCH=89;; 90) NEED=12.0; ARCH=90a;;
  100) NEED=12.8; ARCH=100a;; 103) NEED=12.9; ARCH=103a;; *) NEED=12.9; ARCH=$CC;;
esac
echo "compute capability $CC (sm_$ARCH), driver $DRIVER, needs nvcc >= $NEED"

# ---------------------------------------------------------------------------------------------- toolkit
ver_ge() { [[ "$(printf '%s\n%s\n' "$2" "$1" | sort -V | head -1)" == "$2" ]]; }
NVCC=""; NVCC_FLAGS=""; PY=python3
SYS_NVCC=$(command -v nvcc || true); [[ -z $SYS_NVCC && -x /usr/local/cuda/bin/nvcc ]] && SYS_NVCC=/usr/local/cuda/bin/nvcc
if [[ -n $SYS_NVCC ]]; then
  SYS_VER=$("$SYS_NVCC" --version | sed -n 's/.*release \([0-9.]*\).*/\1/p')
  echo "system nvcc $SYS_NVCC $SYS_VER"
fi
if [[ $TOOLKIT != conda && -n $SYS_NVCC ]] && ver_ge "$SYS_VER" "$NEED"; then
  NVCC=$SYS_NVCC
  # python with numpy >= 2, cmake and ninja for CUTLASS: pinned wheels in a venv when the system lacks them
  if ! python3 -c "import numpy; assert int(numpy.__version__.split('.')[0]) >= 2" 2>/dev/null \
     || ! command -v cmake >/dev/null || ! command -v ninja >/dev/null; then
    python3 -m venv "$OUT/venv"
    "$OUT/venv/bin/pip" install -q numpy==2.1.3 cmake==3.31.6 ninja==1.11.1.4
    PY="$OUT/venv/bin/python"; export PATH="$OUT/venv/bin:$PATH"
  fi
elif [[ $TOOLKIT == system ]]; then
  echo "TOOLKIT: no system nvcc >= $NEED (have '${SYS_VER:-none}') and --toolkit system"; exit 4
else
  # pinned rootless toolkit: micromamba 2.3.3-0 (sha256) + conda-forge packages at exact versions; cached
  # under $ACCEL_CACHE so a rerun on the same box does not download again.
  CACHE=${ACCEL_CACHE:-$HOME/accel-cache}; mkdir -p "$CACHE"
  MM="$CACHE/micromamba-2.3.3-0"
  if [[ ! -x $MM ]]; then
    curl -fsSL -o "$MM.part" https://github.com/mamba-org/micromamba-releases/releases/download/2.3.3-0/micromamba-linux-64
    echo "9496f94a8b78c536573c93d946ec9bba74bd9ff79ee55aaa4b546e30db8f511b  $MM.part" | sha256sum -c -
    chmod +x "$MM.part"; mv "$MM.part" "$MM"
  fi
  ENVD="$CACHE/mma-cuda129"
  if [[ ! -x $ENVD/bin/nvcc || ! -x $ENVD/bin/python || ! -e $ENVD/include/curand_kernel.h ]]; then
    t=$(date +%s)
    MAMBA_ROOT_PREFIX="$CACHE/mamba" "$MM" $([[ -d $ENVD ]] && echo install || echo create) -y -q -p "$ENVD" -c conda-forge --override-channels \
      cuda-nvcc=12.9.86 cuda-cudart-dev=12.9.79 libcublas-dev=12.9.1.4 cuda-cuobjdump=12.9.82 \
      cuda-nvdisasm=12.9.88 libcurand-dev=10.3.10.19 gxx_linux-64=13.3.0 python=3.12.16 numpy=2.1.3 cmake=3.31.8 ninja=1.13.2 make=4.4.1
    echo "conda toolkit env in $(( $(date +%s) - t )) s"
  fi
  MAMBA_ROOT_PREFIX="$CACHE/mamba" "$MM" list -p "$ENVD" > "$OUT/toolkit-packages.txt"
  export PATH="$ENVD/bin:$PATH"
  NVCC="$ENVD/bin/nvcc"; NVCC_FLAGS="-ccbin $ENVD/bin/x86_64-conda-linux-gnu-g++"; PY="$ENVD/bin/python"
fi
"$NVCC" --version | tail -2
export NVCC NVCC_FLAGS

# ---------------------------------------------------------------------------------------------- steps 1-6 (own kernels)
ARGS=(--out "$OUT/probe" --sku "$SKU" --gpu "$GPU")
(( SHRINK )) && ARGS+=(--shrink)
set +e
accel_run 3300 600 "$PY" -u "$SRC/mma_run.py" "${ARGS[@]}"
RC_PROBE=$?
set -e
cp "$OUT/probe/results.json" "$OUT/results.json" 2>/dev/null || true

# ---------------------------------------------------------------------------------------------- CUTLASS (steps 3, 6)
CUT="$OUT/cutlass"; mkdir -p "$CUT"
cutlass_step() {
  local tag=v4.8.1 sha=2c85f497547eb441f0fe80bfb0fb2e6f9add1719 cache=${ACCEL_CACHE:-$HOME/accel-cache}
  mkdir -p "$cache"
  if [[ ! -d $cache/cutlass-$tag ]]; then
    git clone -q --depth 1 --branch $tag https://github.com/NVIDIA/cutlass.git "$cache/cutlass-$tag.part"
    mv "$cache/cutlass-$tag.part" "$cache/cutlass-$tag"
  fi
  [[ $(git -C "$cache/cutlass-$tag" rev-parse HEAD) == "$sha" ]] || { echo "CUTLASS sha mismatch"; return 5; }
  local cx="${NVCC_FLAGS#-ccbin }"; [[ -z $cx ]] && cx=$(command -v g++)
  local cmk=(cmake "$cache/cutlass-$tag" -G Ninja -DCUTLASS_NVCC_ARCHS=$ARCH -DCUTLASS_ENABLE_TESTS=OFF
             -DCUTLASS_LIBRARY_OPERATIONS=gemm -DCUTLASS_ENABLE_CUBLAS=OFF -DCUTLASS_ENABLE_CUDNN=OFF -DCMAKE_CUDA_COMPILER="$NVCC" -DCMAKE_CUDA_HOST_COMPILER="$cx"
             -DCMAKE_CXX_COMPILER="$cx")
  local jobs=$(( $(nproc) > 32 ? 32 : $(nproc) ))
  local t0=$(date +%s)
  # a heartbeat while single long translation units compile (ninja itself is bounded by timeout 1500);
  # stopped through its PID file
  ( while sleep 60; do echo "cutlass heartbeat $(( $(date +%s) - t0 )) s"; done ) & echo $! > "$CUT/heartbeat.pid"
  case $ARCH in
    75|80|89|90a)
      # b1 GEMMs exist in CUTLASS only as sm_75 (88128, xor) and sm_80 (168256, and up to sm_90) mma.sync kernels
      local pat="cutlass_tensorop_*168256andgemm*"; [[ $ARCH == 75 ]] && pat="cutlass_tensorop_*88128xorgemm*"
      mkdir -p "$CUT/build" && cd "$CUT/build"
      "${cmk[@]}" -DCUTLASS_ENABLE_EXAMPLES=OFF -DCUTLASS_LIBRARY_KERNELS="$pat" > cmake.log 2>&1
      timeout 1500 ninja -j $jobs cutlass_profiler > build.log 2>&1; local rc=$?
      kill "$(cat "$CUT/heartbeat.pid")"
      echo "cutlass_profiler build rc $rc in $(( $(date +%s) - t0 )) s"; tail -3 build.log
      grep -m 20 -B 2 -E "error|fatal" build.log > "$CUT/build_errors.txt"; tail -40 build.log > "$CUT/build_tail.txt"
      (( rc == 0 )) || return $rc
      local mnk=16384; (( SHRINK )) && mnk=8192
      local prof=./tools/profiler/cutlass_profiler
      # a small verified problem first (CUTLASS's own reference), then the rate at size without verification
      timeout 600 $prof --operation=Gemm --A=b1:row --B=b1:column --C=s32:column --m=1024 --n=1024 --k=8192 \
        --verification-enabled=true --profiling-iterations=2 --output="$CUT/b1_verify" > "$CUT/profiler_b1_verify.txt" 2>&1
      timeout 900 $prof --operation=Gemm --A=b1:row --B=b1:column --C=s32:column \
        --m=$mnk --n=$mnk --k=$(( mnk * 8 )) --verification-enabled=false --profiling-iterations=20 --output="$CUT/b1" \
        > "$CUT/profiler_b1.txt" 2>&1
      grep -E "Operation:|Disposition|Runtime|GFLOPs|Math:" "$CUT/profiler_b1_verify.txt" "$CUT/profiler_b1.txt" | head -60
      ;;
    100a|103a)
      # tcgen05 example GEMMs: rate and their own reference check (Disposition); no b1 kind exists on sm_100+
      mkdir -p "$CUT/build" && cd "$CUT/build"
      "${cmk[@]}" -DCUTLASS_ENABLE_EXAMPLES=ON -DCUTLASS_ENABLE_LIBRARY=OFF -DCUTLASS_ENABLE_PROFILER=OFF \
        > cmake.log 2>&1
      timeout 1500 ninja -j $jobs 70_blackwell_fp8_gemm 72a_blackwell_nvfp4_bf16_gemm > build.log 2>&1; local rc=$?
      kill "$(cat "$CUT/heartbeat.pid")"
      echo "examples build rc $rc in $(( $(date +%s) - t0 )) s"; tail -3 build.log
      grep -m 20 -B 2 -E "error|fatal" build.log > "$CUT/build_errors.txt"; tail -40 build.log > "$CUT/build_tail.txt"
      (( rc == 0 )) || return $rc
      for ex in 70_blackwell_fp8_gemm 72a_blackwell_nvfp4_bf16_gemm; do
        local bin; bin=$(find . -name "$ex" -type f -perm -u+x | head -1)
        timeout 300 "$bin" --m=8192 --n=8192 --k=8192 --iterations=20 > "$CUT/$ex.txt" 2>&1 || true
        echo "$ex:"; grep -E "Disposition|GFLOPS|Avg runtime" "$CUT/$ex.txt"
      done
      ;;
    *) echo "no CUTLASS step for sm_$ARCH";;
  esac
}
if (( CUTLASS )); then
  set +e
  accel_run 3300 900 bash -c "$(declare -f cutlass_step); ARCH=$ARCH NVCC=$NVCC NVCC_FLAGS='$NVCC_FLAGS' SHRINK=$SHRINK CUT=$CUT ACCEL_CACHE=${ACCEL_CACHE:-} cutlass_step"
  RC_CUTLASS=$?
  set -e
else
  RC_CUTLASS=skipped
fi

# ---------------------------------------------------------------------------------------------- one results file
"$PY" - "$OUT" "$RC_PROBE" "$RC_CUTLASS" <<'EOF'
import json, pathlib, re, sys
out, rc_probe, rc_cut = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3]
p = out / "results.json"
res = json.loads(p.read_text()) if p.exists() else {}
res["runbook"] = {"rc_probe": rc_probe, "rc_cutlass": rc_cut, "box": json.loads((out / "box.json").read_text())}
cut = {}
for f in sorted((out / "cutlass").glob("*.csv")) + sorted((out / "cutlass").glob("*.txt")):
    cut[f.name] = f.read_text()[-6000:]
res["cutlass"] = cut
res["keccak_f"] = "not measured here: workload 2 (runbook/tower256.sh) reports keccak_f_per_s"
p.write_text(json.dumps(res, indent=1))
print("results", p, "checks", res.get("n_checks"), "failed", res.get("n_failed"), "errors", list(res.get("errors", {})))
EOF
echo "done in $(( $(date +%s) - T0 )) s; results $OUT/results.json"
[[ $RC_PROBE == 0 ]]
