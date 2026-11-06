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
# The workspace lock lists ~200 packages this crate does not use, so `cargo build --locked` refused it on the
# H100 (accel-h100-all-02). Prune it offline (removals only, no version changes; checked below) and prove
# the bundle builds --locked before it leaves the Mac.
cp "$B/prover/Cargo.lock" "$STAGE/lock.workspace"
( cd "$B/prover" && cargo update --workspace --offline -q )
python3 - "$STAGE/lock.workspace" "$B/prover/Cargo.lock" <<'PYEOF'
import re, sys
pk = lambda p: set(re.findall(r'name = "([^"]+)"\nversion = "([^"]+)"', open(p).read()))
a, b = pk(sys.argv[1]), pk(sys.argv[2])
assert b <= a, ("lock prune changed versions", sorted(b - a))
print("lock pruned:", len(a), "->", len(b), "packages, no version changes")
PYEOF
( cd "$B/prover" && cargo metadata --locked --offline --format-version 1 > /dev/null )
( cd "$STAGE" && tar czf "$TAR" tower256 )
echo "$TAR $(git -C "$SRC" rev-parse HEAD)"
