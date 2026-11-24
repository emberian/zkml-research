#!/usr/bin/env bash
# Run from (or pass) a clean baseline checkout. Timings include the cargo launcher.
set -euo pipefail
cd "${1:-.}"
cd "$(git rev-parse --show-toplevel)/native"
[[ $(git rev-parse HEAD) == 691c42f61a27c92a48ce38fec2630d1b96384b91 ]]
git diff --quiet HEAD -- resident_custody
export RUSTFLAGS="-D warnings"
cargo test --release -p resident_custody --lib --no-run
RAYON_NUM_THREADS=4 /usr/bin/time -l cargo test --release -p resident_custody --lib authenticated_release_gate -- --ignored --nocapture --test-threads=1
/usr/bin/time -l cargo test --release -p resident_custody --lib full_field_prefix_proof -- --ignored --nocapture --test-threads=1
