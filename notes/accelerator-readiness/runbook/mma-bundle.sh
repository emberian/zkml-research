#!/usr/bin/env bash
# Make the workload-3 bundle for a paid box: mma-bundle.sh DEGG_RESEARCH_CHECKOUT [REV] [OUT.tar.gz]
# Exports experiments/mma-accumulator-probe/ at REV (default HEAD; committed content only, never the
# working tree) into src/, writes src/MANIFEST (sha256) and src/COMMIT, and adds mma.sh, common.sh and
# the Kaggle entry.  On the box: tar xzf mma-bundle.tar.gz && bash mma/mma.sh --sku B300
set -euo pipefail
REPO=$(cd "$1" && pwd); REV=${2:-HEAD}; TAR=${3:-$PWD/mma-bundle.tar.gz}
HERE=$(cd "$(dirname "$0")" && pwd)
STAGE=$(mktemp -d); trap 'rm -rf "$STAGE"' EXIT
B="$STAGE/mma"; mkdir -p "$B/src"
cp "$HERE/mma.sh" "$HERE/common.sh" "$HERE/mma_kaggle_entry.py" "$B/"
D=experiments/mma-accumulator-probe
for f in probe.cu probe_fixed.cu probe_sm75.cu probe_sm80.cu gemm_probe.cu mma_run.py README.md; do
  git -C "$REPO" show "$REV:$D/$f" > "$B/src/$f"
done
( cd "$B/src" && sha256sum probe.cu probe_fixed.cu probe_sm75.cu probe_sm80.cu gemm_probe.cu mma_run.py > MANIFEST )
git -C "$REPO" rev-parse "$REV" > "$B/src/COMMIT"
( cd "$STAGE" && tar czf "$TAR" mma )
echo "$TAR $(cat "$B/src/COMMIT")"
