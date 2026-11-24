#!/bin/sh
# Run each fixture in its own process so the RSS high-water mark belongs to that fixture.
set -eu
cd "$(dirname "$0")/../../native"
export RUSTFLAGS="-D warnings"
export RAYON_NUM_THREADS="${RAYON_NUM_THREADS:-12}"
binary=$(cargo test --release -p resident_custody --lib --no-run --message-format=json |
    python3 -c 'import json,sys; print(next(m["executable"] for m in map(json.loads,sys.stdin) if m.get("executable") and m["target"]["kind"] == ["lib"]))')
case $(uname -s) in
    Darwin) timer=-l ;;
    Linux) timer=-v ;;
    *) exit 1 ;;
esac
for fixture in full_field_prefix_proof depth_8_member depth_8_empty depth_16_member depth_16_empty; do
    /usr/bin/time "$timer" "$binary" --exact "trie_opening::deployed::tests::$fixture" --ignored --nocapture --test-threads=1
done
