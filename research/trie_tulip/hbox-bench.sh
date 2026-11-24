#!/usr/bin/env bash
set -euo pipefail
# A/B of the old and new resident_custody engines on hbox, separate target dirs.
L=${TRIE_BENCH_ROOT:-/home/hbox/lanes/trie-tulip}
export CARGO_PROFILE_RELEASE_DEBUG=0 RUSTFLAGS="-D warnings"
uptime
for tree in old new; do
  export CARGO_TARGET_DIR="$L/target-$tree"
  echo "=== $tree"
  cd "$L/$tree/native" || exit 1
  swarm-build cargo test --release -p resident_custody --lib --no-run 2>&1 | tail -2
  for i in 1 2 3; do
    RAYON_NUM_THREADS=4 swarm-build cargo test --release -p resident_custody --lib authenticated_release_gate -- --ignored --nocapture --test-threads=1 2>&1 | grep -E "medians|panicked"
  done
  swarm-build /usr/bin/time -v cargo test --release -p resident_custody --lib full_field_prefix_proof -- --ignored --nocapture --test-threads=1 2>&1 | grep -E "260-bit|Maximum resident|Elapsed|User time|panicked"
  uptime
done
cd "$L/new/native"
swarm-build cargo test --release -p resident_custody --lib trie_opening::deployed::tests::depth_ -- --ignored --nocapture --test-threads=1 2>&1 | grep -E "prefix|panicked"
RESIDENT_MESH_DIR=$L/mesh swarm-build cargo test --release -p resident_custody --test tulip_crash_house_move -- --nocapture --test-threads=1 2>&1 | grep -E "^test result|Before|After|zombie|panicked"
RESIDENT_MESH_DIR=$L/mesh swarm-build cargo test --release -p resident_custody --test full_resident_house_move --test resident_house_move_and_cshake_open -- --test-threads=1 2>&1 | grep -E "^test result|panicked"
uptime
echo done
