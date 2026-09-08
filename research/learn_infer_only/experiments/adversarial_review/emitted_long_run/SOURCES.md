# Source locations inspected

[SOURCE] Repository-relative paths below share the prefix
`research/learn_infer_only/experiments/end_to_end/private_ema/`.
Exact hashes for each frozen file are retained in `results.json`; no external
search, Scry call or PDF download was used.

| Path and location | What was inspected |
| --- | --- |
| `emitted_long_run/CONTRACT.md` | Fixed two-history workload, 480 pairs, authorized 484 primary opens, six-hour/15:00 cutoff, separate post-drain seal. |
| `emitted_long_run/common.py` | Fixed role/key/descriptor paths; SHA256 metadata, fsynced append and atomic JSON save; envelope header checks. |
| `emitted_long_run/run_public.py:40` | One fresh timed child per operation; before/after public-input and binary hashes; sequential waits; deadline/first-failure stop. |
| `emitted_long_run/run_public.py:86` | Same tuple evaluated twice; complete-byte equality; selected parent updated only after success. |
| `emitted_long_run/verify_public.py` | Full source/fixture/parent/query/plan/storage/replay checks before public seal. |
| `emitted_long_run/pipeline.py` | Sequential successful-exit prerequisites for public verification, drain and final provenance seal. |
| `emitted_long_run/drain.py:12` | Public closure/hash prerequisites, exact primary-only reader sequence and fixture comparison; private outputs remain private. |
| `emitted_long_run/seal.py` | Post-drain read-only provenance checks and cost aggregation; no crypto invocation. |
| `emitted_long_run/collect_public_provenance.py` | Later public-only recheck is distinct from original prerequisite seal. |
| `src/bin/issuer.rs:10` | Public-key encryption of fresh zero states, 2-bit addresses and signed 8-bit inputs; public metadata stdout. |
| `src/bin/reader.rs:9` | Unrestricted client-key decrypt, little-endian signed-byte decoding, private report and public metadata stdout. |
| `emitted_fixed_fft/src/lib.rs:101` | Exact descriptor dimensions/schema/reference validity and increasing gate outputs; generic XOR/AND interpretation. |
| `emitted_fixed_fft/src/main.rs:39` | Public server-key/parent/request-only host branch, descriptor evaluation and encrypted output requirement. |
| `emitted_fixed_fft/src/ciphertext.rs:31` | Actual TFHE gate calls/counts; canonical bincode decoding, typed envelope and Encrypted variant validation, create-new fsynced output. |
| `emitted_fixed_fft/src/plan_observation.rs:16` | Move/restore same public server-key components; actual factory/cache plan Debug observation at that key's polynomial size. |
| `emitted_fixed_fft/build_pins.json` | Saved compiler-feature/binary/source evidence; no independent rebuild. |

[SOURCE] Cached primary source prefix:
`/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/`.
All four files were independently rehashed against build pins.

| Cached primary file | Exact inspected source locations |
| --- | --- |
| `tfhe-1.6.3/Cargo.toml` | 75–98: Boolean and fixed-Dif4 feature declarations. |
| `tfhe-1.6.3/src/core_crypto/fft_impl/fft64/math/fft/mod.rs` | 77–118: public views and shared plan cache; 161–197: feature-selected UserProvided Dif4 factory versus measured branch, cache lookup. |
| `tfhe-1.6.3/src/boolean/engine/bootstrapping.rs` | 94–163: public server-key raw-parts inverse construction; 447–475: Boolean bootstrap calls `Fft::new` at the actual bootstrapping-key size. |
| `tfhe-fft-0.10.1/src/unordered.rs` | 495–536: plan Debug fields and UserProvided/Measure methods; 654–676: supplied algorithm/size validation and function selection; 775–777: algorithm accessor. |

[SOURCE] Exact formal JSON/Lean snapshot identities are checked through the
original freeze. The two JSON descriptors are also independently evaluated on
480 public fixture rows by the standard-library checker. No new formal build,
full source-dependency closure proof, or crypto correctness proof is claimed.
