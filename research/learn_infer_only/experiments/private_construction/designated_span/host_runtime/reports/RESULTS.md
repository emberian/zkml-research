# Normal paired public-host result

[EXECUTED] Eight actual designated-DDH proposals passed byte-for-byte
comparison between a one-shot host and a persistent host: six Learn and two
fixed-query Infer events. Every canonical request and result ciphertext was
identical. The first event also matched the original, unchanged `roles.py
propose` entry point. The fixture used publicly specified vectors and no
recipient scalar, recipient decode or authority process.

[EXECUTED] The paired result is
[`paired_001/report.json`](paired_001/report.json), SHA256
`f24bdf11746242b2b0dc32d607b3db08640d108c7672dc174a2cce721392ed42`.
The frozen adapter is `host.py`, SHA256
`70bbb6338c7600d7e6e5609524d146f9af21bfc01a94d4dfd725933fc5931916`.
Its eight unmodified journal/service sources and four crypto source identities
are pinned by `source_pins.json`, SHA256
`17402dba697bd73da8aac4e519e6f7cbaeca25ecfce824d8f8cf45004e743bc7`.
The predeclaration, per-event replies and crypto command logs are retained in
the result directory. Sources and native dependency hashes were unchanged.

| [EXECUTED] Measurement | One-shot | Persistent |
| --- | ---: | ---: |
| Host caller wall time, eight proposals | 78.519873625 s | 29.494690958 s |
| Time inside original proposal function/wrapper | 77.884874209 s | 29.487845751 s |
| Ciphertext `inspect` subprocesses | 51 | 14 |
| Actual `host-learn` / `host-infer` calls | 6 / 2 | 6 / 2 |
| CAS get calls | 112 | 112 |
| Full-blob SHA256 calls | 112 | 112 |
| Full-blob bytes hashed | 15712908 | 15712908 |

[EXECUTED] The observed paired caller-wall ratio is 2.66216973545548. The
single persistent worker took 66.197958 ms to start, retained 14 public
ciphertext-inspection metadata entries across eight requests, and exited
normally after stdin closed. Its startup is reported separately from its
proposal total. The cache has no eviction and is discarded on exit. The first
accumulator equals its fresh ciphertext under the public zero identity, so
that shared object needs only one cache entry.

[EXECUTED] The entire harness took 124.494282500 seconds. It includes public
fixture preparation, full context validation, fresh encryption, both host
paths, the extra original-CLI comparison and instrumentation. This is not a
full end-to-end improvement measurement, a utility result or a statistical
performance claim. The fixture contains six publicly known deterministic
vectors and actual original row-0/row-1 queries, with capacity 32 and no expiry.
All compared paths received the same encrypted bytes, signatures and heads;
execution order alternated by event. No model or prior experiment was rerun.

[DERIVED scope] The existing `CAS.inspected` cache is the only retained
validation state. All `CAS.get` full reads/hashes and the original proposal,
authorization, state and transition bodies remain in use. Additional source,
configuration, native-library and context hashes lie outside the CAS counters.
The public validation record is trusted setup configuration, not a standalone
cryptographic proof. Source/configuration and SHA256 assumptions, the existing
file-read/CLI time-of-check boundary and all designated-recipient construction
limits remain. No adversarial, malformed-input, routing or extraction test was
performed, and no integration or authority claim follows from this host-only
comparison.

```sh
python3 research/learn_infer_only/experiments/private_construction/designated_span/host_runtime/paired_driver.py \
  --runtime research/learn_infer_only/experiments/private_construction/designated_span/host_runtime/runtime/paired_002 \
  --reports research/learn_infer_only/experiments/private_construction/designated_span/host_runtime/reports/paired_002
```

[DERIVED reproduction] The public context and zero are read from the completed
crypto positive run named in the predeclaration. Recipient/master files are
never copied. Ciphertexts use fresh OS randomness, so a rerun changes their
hashes while comparing exactly the same new ciphertext inputs across modes.
