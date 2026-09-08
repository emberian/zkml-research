#!/bin/sh
set -eu
cd "$(dirname "$0")"
cargo build --release --locked --offline --lib --target wasm32-unknown-unknown -j 2
wasm-bindgen --target web --out-dir web/pkg --out-name ring_browser_verifier \
  target/wasm32-unknown-unknown/release/ring_browser_verifier.wasm
