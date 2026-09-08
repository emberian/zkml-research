[EXECUTED] Completed result-producing entrypoints, using the existing Python environment at `../../adaptation_utility/.venv/bin/python` and the owned Rust adapter:

| Entrypoint | Retained output | Scope |
|---|---|---|
| `evaluate.py` | `evaluate.log`, `plaintext_result.json` | One law, same fixed128/320 fixture, no encoder execution |
| `basic_crypto.py` | `basic_crypto.log`, `basic_crypto_result.json` | Nine teachings, one expiry, one actual square |
| `encrypted_evaluate.py` | `encrypted_evaluate.log`, `encrypted_result.json`, `encrypted_predictions.json` | 128 Learn/64 expiry,48 queries,320 actual squares |
| `live_demo.py plain` and `live_demo.py bfv` | `live_plain.json`, `live_bfv.json`, `live_result.json` | Exact subprocess argv, requests, stdout/stderr and timing saved in JSON |
| `check_cached_002.py` | `check_cached_002.log`, `cached_replay_002/result.json` | Same final query inputs, nine byte-identical outputs, public-only |
| `crypto/src/scaler_constants.rs` | `public_trace/native_scaler_constants.json` | Public constructor constants only |

[SOURCE] These batch entrypoints create fixed output/model paths and are not restart scripts. Preserve the completed runs; use the documented `model.py init` and `session.py` interface with a new model directory for new work. Build logs are retained under `crypto/`. The first compiler error was corrected before any cryptographic execution; `build_002.log` records the successful baseline. The cache-only successor is `build_cached_002.log` and preserves the baseline executable.

[EXECUTED] `runtime/main_operations.jsonl` and `runtime/basic_operations.jsonl` retain exact crypto argv arguments, exit status and public timings/results. Reader result values are omitted from these operation logs and separately compared in the aggregate result files. Public host requests in `cached_replay_002/result.json` have complete input/output hashes. The live sessions used inline receiving; the batch explicitly delayed receiving until `public_complete.json`.
