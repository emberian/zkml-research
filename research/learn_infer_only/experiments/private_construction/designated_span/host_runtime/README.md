# Persistent designated public host

[DERIVED] This adapter retains the designated journal's existing public
ciphertext inspection dictionary across proposals. The copied `roles.propose`,
`CAS.get`, authorization/state validation and transition bodies are unchanged.
Every CAS get still reads and hashes the full blob. The adapter and normal
paired experiment are specified in [PROTOCOL.md](PROTOCOL.md). The completed
[paired result](reports/RESULTS.md) matched all eight proposals and reduced
inspections from 51 to 14 while retaining equal full read/hash counts.

```sh
python3 host.py serve --config /absolute/public/host_config.json --cas /absolute/public/host_cas
```

[DERIVED interface] The worker emits one ready JSON line containing `ok`,
`ready`, `source_pins_sha256`, `context_id` and zero `inspection_cache_entries`.
Send canonical, compact, key-sorted JSON lines with exactly:

```json
{"authorization":"/absolute/public/authorization.json","head":"/absolute/public/head.json","out":"/absolute/public/request.json"}
```

[DERIVED interface] Each successful response contains `ok`, the original
proposal function's `result` JSON, `elapsed_ns`, `request_stats`,
`cumulative_stats` and `inspection_cache_entries`. The generated request file
is the original journal's canonical request. Closing stdin exits the worker
normally. To discard inspection metadata after one proposal:

```sh
python3 host.py once --config HOST_CONFIG --cas CAS \
  --head HEAD --authorization AUTHORIZATION --out REQUEST
```

[DERIVED pinned inputs] `source_pins.json` inventories eight byte-identical
designated journal/service files in `frozen_source/`; its digest is a constant
in `host.py`. Those bytes are checked before import and again before each
proposal. The caller must pin the host adapter itself. The nine public config
fields are listed in the protocol. The whole config, genesis, context identity,
crypto sources/native dependency and CAS root are fixed for the worker's
lifetime. The successful uncached validation record must be
`context_validation.json` beside the configured genesis file and match the
hash in genesis. This is a trusted setup record, not a standalone proof.
No recipient scalar path, plaintext vector argument or release command is
accepted by the worker's public config and crypto-call interface.

[DERIVED measurements] `cas_get_calls`, `full_blob_sha256_calls` and
`full_blob_sha256_bytes` count the actual unchanged get/body operations.
`crypto_calls` counts subprocess requests by command. Source, native-library,
context and other metadata hashes occur outside the CAS counters. A one-shot
wrapper uses the same instrumentation as the persistent wrapper. The cache
contains only `inspect` result metadata keyed by ciphertext digest; it has no
eviction or new continuity authority and disappears on exit.

[OPEN boundary] This adapter is a performance experiment within trusted
source/configuration and content-address assumptions. The file-read/crypto-CLI
time-of-check boundary is inherited. Process inputs and logs demonstrate a
keyless role, not OS isolation. The journal authority and verified recipient
remain responsible for independent recomputation and history acceptance.
No recipient decryption or authority acceptance is part of the paired host
test, and it provides no new utility, privacy or adversarial-security result.

```sh
python3 paired_driver.py \
  --runtime runtime/paired_002 --reports reports/paired_002
```

[DERIVED reproduction] The normal fixture uses the public context and zero
ciphertext retained from `../crypto/runtime/positive_001/public/`, pinned by
that run's public report. It copies no recipient keys, performs a fresh full
context validation, encrypts six publicly specified deterministic vectors
with fresh OS randomness, and compares eight actual proposals in isolated
CAS directories. The first event is also checked against the original journal
CLI. Actual ciphertext hashes vary on a rerun; compared ciphertext inputs are
identical between its two modes. Use fresh output directories. The test has
no adverse, malformed-input, routing or extraction controls.
