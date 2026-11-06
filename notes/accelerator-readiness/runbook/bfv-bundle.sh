#!/usr/bin/env bash
# Make the workload-1 bundle for a paid box: bfv-bundle.sh ZKML_RESEARCH_CHECKOUT [REV] [OUT.tar.gz]
# Exports committed content at REV (default HEAD; never the working tree) in the layout bfv.sh expects
# (runbook/ three levels below the repo root, research/dark_learning_2026_11_06/ beside it), with a
# sha256 MANIFEST. On the box: tar xzf bfv-bundle.tar.gz && bash bfv/notes/accelerator-readiness/runbook/bfv.sh --sku H100
set -euo pipefail
REPO=$(cd "$1" && pwd); REV=${2:-HEAD}; TAR=${3:-$PWD/bfv-bundle.tar.gz}
STAGE=$(mktemp -d); trap 'rm -rf "$STAGE"' EXIT
B="$STAGE/bfv"; R=notes/accelerator-readiness/runbook; S=research/dark_learning_2026_11_06
mkdir -p "$B/$R" "$B/$S"
for f in bfv.sh common.sh; do git -C "$REPO" show "$REV:$R/$f" > "$B/$R/$f"; done
FILES=$(sed -n 's/^FILES="\(.*\)"$/\1/p' "$B/$R/bfv.sh")
for f in $FILES; do git -C "$REPO" show "$REV:$S/$f" > "$B/$S/$f"; done
( cd "$B" && find . -type f ! -name MANIFEST | sort | xargs shasum -a 256 > MANIFEST )
git -C "$REPO" rev-parse "$REV" > "$B/COMMIT"
( cd "$STAGE" && tar czf "$TAR" bfv )
echo "$TAR $(cat "$B/COMMIT")"
