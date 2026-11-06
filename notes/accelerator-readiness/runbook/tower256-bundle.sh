#!/usr/bin/env bash
# Make the workload-2 bundle for a paid box: tower256-bundle.sh MINIDREGG_CHECKOUT [OUT.tar.gz]
# MINIDREGG_CHECKOUT is a checkout of lane/accel-tower256-gpu. The bundle holds this directory's
# tower256.sh and common.sh, the CUDA kernels and host, the Lean vectors, and the prover crate
# made standalone (its own [workspace] table, the workspace Cargo.lock) so cargo builds it alone.
set -euo pipefail
SRC=$(cd "$1" && pwd); TAR=${2:-$PWD/tower256-bundle.tar.gz}
HERE=$(cd "$(dirname "$0")" && pwd)
STAGE=$(mktemp -d); trap 'rm -rf "$STAGE"' EXIT
B="$STAGE/tower256"; mkdir -p "$B/cuda" "$B/lean" "$B/prover"
cp "$HERE/tower256.sh" "$HERE/common.sh" "$B/"
cp "$SRC/prover/cuda/tower256_fri.cu" "$SRC/prover/cuda/tower256_gpu.py" "$B/cuda/"
cp "$SRC/prover/testdata/tower256_fri_vectors.json" "$B/lean/"
( cd "$SRC/prover" && tar cf - --exclude target Cargo.toml src testdata generated ) | ( cd "$B/prover" && tar xf - )
cp "$SRC/Cargo.lock" "$B/prover/"
printf '\n[workspace]\n' >> "$B/prover/Cargo.toml"
( cd "$STAGE" && tar czf "$TAR" tower256 )
echo "$TAR $(git -C "$SRC" rev-parse HEAD)"
