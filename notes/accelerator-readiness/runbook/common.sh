#!/usr/bin/env bash
# Shared preamble for the accelerator-readiness paid-box scripts (initiative 17). Source it:
#   . "$(dirname "$0")/common.sh"; accel_init <workload> "$@"
# Gives: $OUT (results dir), accel_hw_check <sku-substring>, accel_run <timeout_s> <stall_s> <cmd...>
# (wall + no-output watchdog, PID file, tee to $OUT/log.txt). Never kills by pattern.
set -euo pipefail
accel_init() {
  WORKLOAD=$1; shift
  SHRINK=0; SKU_OVERRIDE=""; for a in "$@"; do case $a in --shrink) SHRINK=1;; --any-gpu) SKU_OVERRIDE=1;; esac; done
  OUT=${ACCEL_OUT:-$HOME/accel-results/$WORKLOAD-$(date -u +%Y%m%dT%H%M%SZ)}
  mkdir -p "$OUT"; T0=$(date +%s)
  { echo "{"; echo "\"workload\": \"$WORKLOAD\", \"shrink\": $SHRINK,"; echo "\"start_utc\": \"$(date -u +%FT%TZ)\","
    echo "\"host\": \"$(hostname)\", \"kernel\": \"$(uname -r)\","
    echo "\"gpu\": \"$(nvidia-smi --query-gpu=name,memory.total,driver_version,compute_cap --format=csv,noheader 2>&1 | tr '\n' ';')\""
    echo "}"; } > "$OUT/box.json"
  export OUT SHRINK
}
accel_hw_check() {  # $1: required substring of the GPU name (H100, H200, B200, T4)
  local name; name=$(nvidia-smi --query-gpu=name --format=csv,noheader | head -1)
  if [[ -z "$SKU_OVERRIDE" && "$name" != *"$1"* ]]; then echo "HARDWARE: want $1, got '$name' (pass --any-gpu to override)"; exit 3; fi
  echo "HARDWARE OK: $name"
}
accel_run() {  # timeout_s stall_s cmd...
  local wall=$1 stall=$2; shift 2
  setsid "$@" >> "$OUT/log.txt" 2>&1 & local pid=$!   # own process group: the watchdog stops the whole job by its PID
  tail -n +1 -f "$OUT/log.txt" --pid=$pid &
  echo $pid > "$OUT/job.pid"
  while kill -0 $pid 2>/dev/null; do
    sleep 5
    local now; now=$(date +%s)
    local age=$(( now - $(stat -c %Y "$OUT/log.txt" 2>/dev/null || echo $now) ))
    if (( now - T0 > wall )); then echo "WATCHDOG wall $wall s" | tee -a "$OUT/log.txt"; kill -TERM -- -$pid; wait $pid || true; return 124; fi
    if (( age > stall )); then echo "WATCHDOG no output $stall s" | tee -a "$OUT/log.txt"; kill -TERM -- -$pid; wait $pid || true; return 125; fi
  done
  wait $pid
}
accel_venv() {  # DIR: a venv at DIR; sets PY and PIP (array). Falls back when python3 has no ensurepip
  # (nvidia/cuda images: apt python3-venv when root; Kaggle's conda python: --without-pip venv with the
  # base interpreter's pip driving it through --python). Fails the script if neither works.
  local d=$1
  if python3 -m venv "$d" >>"$OUT/venv.log" 2>&1; then PY="$d/bin/python"; PIP=("$PY" -m pip); return 0; fi
  rm -rf "$d"
  if [[ $(id -u) == 0 ]] && command -v apt-get >/dev/null && [[ $(command -v python3) == /usr/bin/python3 ]]; then
    apt-get update -qq >>"$OUT/venv.log" 2>&1 && DEBIAN_FRONTEND=noninteractive apt-get install -y -qq python3-venv >>"$OUT/venv.log" 2>&1 \
      && python3 -m venv "$d" >>"$OUT/venv.log" 2>&1 && { PY="$d/bin/python"; PIP=("$PY" -m pip); return 0; }
    rm -rf "$d"
  fi
  python3 -m venv --without-pip "$d"
  PY="$d/bin/python"; PIP=(python3 -m pip --python "$PY")
  "${PIP[@]}" --version
}
