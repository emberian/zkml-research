# Encrypted representation-window integration

[EXECUTED] **Both preregistered held-out histories pass:** 384 Learn events,
256 expiries of the original ciphertext objects, 80 encrypted signed-score
readouts and 16 public empty-route zeros. All 96 scores equal an exact integer
rolling-window reference derived from the frozen representation study.
`results.json`, `run_01.jsonl` and `audit.log` retain the evidence. This bounded
tranche is complete; no model was executed, trained or downloaded.

## Fixed inputs and original learner

[EXECUTED] `PREREGISTRATION.md` was written before generating fixture scores or
running BFV. Its SHA256 is
`1d6c88d6e42adba24240fd6450fffed93f1b739fea89ef14cd920fcfc85b35e7`.
The test histories are 63000 and 63001; each learns 64 skill-0 observations,
64 independent skill-1 observations, then 64 observations with skill 0's rule
reversed. Queries are the two lowest test IDs per `(skill,a,b)` group, evaluated
after each phase: IDs 256, 257, 272, 273, 288, 289, 304, 305, 320, 321, 336, 337,
352, 353, 368, 369. These choices use metadata, never query outcomes.

[SOURCE: local implementation and persisted selection] The frozen study chose
`mean_10/model_window_routed` with total capacity 64, hence **32 per skill**.
`../representation_controls.py:26` implements that update and
`../representation_selection.json` records its selection. Cached features come
from SmolLM2-135M revision `93efa2f097d58c2a74874c7e644dbc9b0cee75a2`;
`../representation_model_manifest.json` identifies `mean_10` as masked mean of
block 9 output. This experiment reuses that cache, not the model runtime.

[EXECUTED] `build_fixture.py` imports the original feature and label functions
(`../text_transfer_data.py:51`, `:81`), using teacher-only public-skill
centering/scaling, a bias coordinate, then
`clip(rint(feature * 127), -127, 127).astype(int8)`. The issuer multiplies each
577-coordinate vector by its original label. Every generated state matches
`representation_controls.train`, and each selected query's sign matches
`predict`. `audit.py` independently replays the issued vectors using Python
integers. The fixture is 721,807 bytes, SHA256
`41978a10b974a3e8b7f30d5f9c66f7d396fdf7df83b723b3f14dc00359cdb4c0`.
It is sufficient to rerun BFV without the feature cache or any model download.

## Actual encrypted interface

[SOURCE: local implementation] `probe/src/main.rs` adapts the existing real
`../../he_closure_costs/sliding_window_83_probe/src/main.rs`, with its unchanged
Cargo manifest and lock. It imports the read-only library at
`/Users/ember/dev/breadstuffs/vendor/fhe-dregg`. `results.json` pins the library
source files and their aggregate manifest, Rust toolchain, dependency lock and
the original HE probe. No companion source was edited.

[EXECUTED] Parameters are polynomial degree 4096, plaintext modulus
4,294,828,033, ciphertext primes 2,199,023,190,017 and 4,398,046,486,529 (83-bit
product), and library CBD variance 10. Each history has its own test key pair.
ChaCha20 coin bytes 201 and 202 are public reproducibility fixtures.

[DERIVED; implemented and tested] The issuer encodes and publicly encrypts a
signed contribution modulo the plaintext modulus. `HostRoute` contains only
an encrypted accumulator and a ciphertext queue. Learn adds the received
ciphertext, retains it, and subtracts the **same stored object** after 32 later
positions on that route. Plaintext labels, reference state and the key are
outside that struct. The test harness does not feed decrypted values into it.

[EXECUTED] At 10 nonempty phase/route checkpoints, the accumulator serialization
is byte-identical to a fresh sum of the retained ciphertexts. All 4,096 decrypted
coefficients equal the reference (the first 577 are the state; the rest are zero).
Two empty phase/route checkpoints are explicitly structural checks. The
library's empty `Ciphertext::zero` is not serialized or decrypted: its serializer
uses `ct.len()-1` (`fhe-dregg/src/bfv/ciphertext.rs:170`). The 16 corresponding
queries return publicly known zero and **are not counted as encrypted readouts**.

[DERIVED; checked] For each nonempty public query, reverse its coefficients and
split them into nonnegative positive/negative plaintext polynomials. Two
ciphertext/plaintext products followed by subtraction put the exact dot product
at coefficient 576. Maximum product degree 1152 is below 4096, so that
coefficient has no negacyclic wrap. The declared signed-score bound is
`577 * 32 * 127^2 = 297,805,856 < floor(t/2) = 2,147,414,016`.
The actual selected queries reach absolute score 45,158; largest checkpoint
state coefficient is 369. These are measured fixture maxima, not universal
parameter estimates.

## Cost and measured latency

[EXECUTED] Per history, 192 inputs consume 16,324,224 serialized bytes; 40
encrypted answers consume 3,400,880 bytes. Every nonempty ciphertext is 85,022
serialized bytes; the public key is 42,547 bytes. At peak, 64 queued ciphertexts
and 2 accumulators retain **5,611,452 serialized bytes** (8,650,752 raw RNS payload
bytes). During an update before expiry there can be 67 named live ciphertexts;
the stable retained count is 66. This excludes query temporaries, allocator,
parameter/NTT tables, keys, plaintext issuer/oracle and the cached model features.
These payload counts are not process RSS or a complete deployed memory bill.

[EXECUTED] Across both histories: 384 ciphertext additions, 256 expiry
subtractions, 160 ciphertext/plaintext products, and 80 readout subtractions.
There are no ciphertext/ciphertext products, rotations, relinearizations or
special key-switching primes in this fixture.

[EXECUTED] One release-mode run on a shared Apple M2 Max produced the following
per-event medians and nearest-rank p95s. These are illustrative local timings,
not benchmark confidence intervals. Raw nanoseconds and totals are retained in
the JSONL log and `results.json`.

| Stage | Samples | Median | p95 |
| --- | ---: | ---: | ---: |
| Issuer encode + public encrypt | 384 | 0.561458 ms | 0.596250 ms |
| Host Learn addition + optional expiry | 384 | 0.013458 ms | 0.014876 ms |
| Public query encode + two products + subtraction | 80 | 0.208917 ms | 0.223084 ms |
| Two products + subtraction alone | 80 | 0.059125 ms | 0.062500 ms |
| Whole-polynomial test decrypt + decode | 80 | 0.332542 ms | 0.352458 ms |
| Input serialization | 384 | 0.322333 ms | 0.344000 ms |
| Answer serialization | 80 | 0.317687 ms | 0.337542 ms |

## Validation and reproduction

[EXECUTED] The first build caught a Rust cast/comparison parentheses error;
`build_01.log` preserves that failure. The corrected source built offline and
locked with exit 0 (`build_02.log`), and the single primary run exited 0.
The independent Python audit verifies all fixture/reference/log mappings and
unchanged source hashes. A control changes only the first expected score by +1;
the real decrypted-score comparator then fails with exit 101. The original
query, encryption and host state are unchanged. This establishes a nonvacuous
test comparator, **not** a gate rejecting malicious plaintext or ciphertext.

Run from `/Users/ember/dev/zkml-research`:

```sh
CARGO_TARGET_DIR=research/learn_infer_only/experiments/adaptation_utility/encrypted_window/target cargo build --offline --locked --release --manifest-path research/learn_infer_only/experiments/adaptation_utility/encrypted_window/probe/Cargo.toml
research/learn_infer_only/experiments/adaptation_utility/encrypted_window/target/release/resident-bfv-window-83-probe research/learn_infer_only/experiments/adaptation_utility/encrypted_window/fixture.txt
```

`python3 .../encrypted_window/audit.py` audits the saved primary log and executes
the comparator control. To regenerate the issuer artifact, use the utility
study's existing `.venv/bin/python` on `build_fixture.py`; this needs its pinned
cached NPZ, never new model execution. Exact commands, exits, sources and output
hashes are kept in `results.json` and `artifact_hashes.json`.

## Limits and next seam

[OPEN] This establishes actual BFV arithmetic compatibility for two declared
histories, not a new population utility estimate or a protected model encoder.
The issuer and oracle have plaintext; the test retains a full secret key and
public deterministic encryption coins. The test reader decrypts the **whole
polynomial**, not only a sign. There is no restricted release, authentic-input
enforcement, receipt/descriptor binding, continuity gate or no-master-read claim.
No post-quantum security bit level is asserted, and the independent noise proof
has not been treated as a complete refinement of this Rust implementation.

[OPEN] The next meaningful integration is to bind this fixed public route,
original-ciphertext expiry, query and source feature/label policy to the existing
receipt/continuity boundary. The present issuer-file validation is not such a
binding. Frozen integer-certificate and AirSimplify artifacts remain unchanged;
root integrates this directory without changing their proofs or the shared
VERDICTS/STATUS/NEXT files. This tranche used zero metered searches.
