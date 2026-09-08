#!/bin/sh
set -eu
cd "$(dirname "$0")"
cargo build --manifest-path native/Cargo.toml --release --offline --locked -j2
cargo build --manifest-path proof/Cargo.toml --release --offline --locked -j2
