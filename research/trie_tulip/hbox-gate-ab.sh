#!/usr/bin/env bash
set -euo pipefail
# Interleaved single-block release gate, old and new engines, separate target dirs.
L=${TRIE_BENCH_ROOT:-/home/hbox/lanes/trie-tulip}
export CARGO_PROFILE_RELEASE_DEBUG=0 RUSTFLAGS="-D warnings" RAYON_NUM_THREADS=4
for tree in old new; do
  (cd $L/$tree/native && CARGO_TARGET_DIR=$L/target-$tree swarm-build cargo test --release -p resident_custody --lib --no-run 2>&1 | tail -1)
done
uptime
for round in 1 2 3 4; do
  for tree in old new; do
    (cd $L/$tree/native && CARGO_TARGET_DIR=$L/target-$tree swarm-build cargo test --release -p resident_custody --lib authenticated_release_gate -- --ignored --nocapture --test-threads=1 2>&1 | grep medians | sed "s/^/$tree /")
  done
done
uptime
echo done
