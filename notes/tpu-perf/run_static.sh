#!/bin/sh
# One command: static-check every workload kernel against the real TPU compiler on hbox (deviceless libtpu).
#   notes/tpu-perf/run_static.sh [extra static_check args, e.g. --only mxfp4_w4a8 --gens v5e]
# Needs: ssh hbox; ~/lanes/tpu-perf/.venv with jax[tpu] (GROUNDING section 0). Results: notes/tpu-perf/results/static/
set -eu
HERE=$(cd "$(dirname "$0")" && pwd)
REMOTE=lanes/tpu-perf
STAMP=$(date -u +%Y%m%dT%H%M%SZ)
ssh hbox "mkdir -p $REMOTE/src"
rsync -a --delete --exclude __pycache__ "$HERE/tpuperf/" "hbox:$REMOTE/src/tpuperf/"
ssh hbox "cd $REMOTE/src && rm -rf out-$STAMP && TPU_ACCELERATOR_TYPE=v5litepod-1 nice -n 15 timeout 3600 \
  ../.venv/bin/python -m tpuperf.static_check --out out-$STAMP $* 2> out-$STAMP.stderr; rc=\$?; \
  df -h / | tail -1; exit \$rc"
mkdir -p "$HERE/results/static"
rsync -a "hbox:$REMOTE/src/out-$STAMP/static.json" "$HERE/results/static/static-$STAMP.json"
cp "$HERE/results/static/static-$STAMP.json" "$HERE/results/static/latest.json"
echo "results: $HERE/results/static/static-$STAMP.json  (HLO stays on hbox: ~/$REMOTE/src/out-$STAMP/hlo)"
