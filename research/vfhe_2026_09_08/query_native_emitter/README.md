# Native execution of a Lean-generated query witness plan

[EXECUTED] The complete actual 8192-row query witness now emits in **0.468 seconds**: 0.014 seconds setup and 0.454 seconds executing/writing. All **82,214,912 trace bytes** and **553,870 template bytes** exactly match the frozen, already-proved query artifacts. Four complete constructed rows also match. No encryption, proof or verifier run was repeated. `RESULTS.json`, `results/full001.stdout` and `results/full001.stderr` retain the observation.

[EXECUTED] The earlier same-case interpreted emitter measurements were 102.784 seconds (frozen) and88.168 seconds (cached). These timings are separate observations on the same shared host, not a new matched distribution. The native process includes plan/input parsing and complete trace/template writing. One-time Lean plan generation is excluded from each-query timing because its selected output is reused. `/usr/bin/time -l` reported30,244,864 bytes maximum resident set size.

## Construction and scope

[SOURCE] A bounded inventory found zero `.o` or `.a` files in `/Users/ember/dev/minidregg/.lake/build`, its Mathlib build, and the frozen query build overlay. Their generated-C counts were600,8105 and0 respectively. No linkable native closure was present; compiling the full dependency closure would have defeated the targeted implementation scope.

[DERIVED] `Compiler/BfvQueryWitnessPlan.lean` instead compiles the existing public-input witness algorithm into **7985 sequential instructions** over7985 registers. The builder imports the frozen query module's actual group/multiplication/subtraction wire functions and primes. It decomposes words, computes product quotients/remainders, emits range witnesses and signed carries, and assigns each trace column. Constant arithmetic is folded during plan generation. The selected program assigns every register exactly once; the finite generated-program census checked that property.

[DERIVED] The small Rust executor in `native/src/main.rs` interprets copies, input reads, checked i128 addition/multiplication/subtraction, saturating natural subtraction, Euclidean division/remainder and conversion to nonnegative integers. It serializes canonical proof-field residues through buffered little-endian u32 output. It does **not** construct or simplify any AIR. `EmitQueryWitnessPlan.lean` produces the template through the same Signature.fold over the frozen Lean-derived `emittedSystem`; the native executor copies its bytes unchanged.

[DERIVED] This producer and its instructions are **untrusted witness generation**, not a new soundness theorem or a formal proof of native implementation equivalence. The existing proof backend continues to check the unchanged relation. A bad producer can cause proof failure; it receives no permission to replace constraints or public output. Future proofs retain all existing correctness/security checks. i128 operations fail on overflow or invalid division; public rows retain the existing width/index/radix preflight. Query encoding/NTT, decryption, service/model/request binding and the source-to-native reader boundary retain their existing explicit scopes.

[EXECUTED] The source plan module compiled successfully (`results/build-plan03.log` empty). The isolated serde_json-only Rust crate built offline in3.23 seconds (`results/build-native01.log`), without copying a prover target or rebuilding Lean/Mathlib. `results/generate01.log` records plan generation and frozen source controls. `results/samples001/trace.leu32` equals the entire four-row Lean baseline; `results/wrapper-samples001/` checks the public wrapper. The one real native run equals the previous full trace byte-for-byte.

## Opt-in interfaces

[EXECUTED] The selected sources, binary, generated plan and unchanged template are frozen in `SOURCE_PINS.json`. The unchanged full trace hash is `8f1d1a0ab009f41756e2164c4a0a833494f1d76ad07992f58b767fb495e78cc5`; the unchanged template hash is `f42c5efcaa994656b0c9ef2d1270aa2d6eb7dae0e5ba85938d23dbb3dc46c10d`. Existing query/learner cohorts remain untouched.

```sh
# Witness emission only; checks selected pins and refuses existing output:
python3 query_native_emitter/emit.py NEW_OUT_DIR PUBLIC_ROWS_JSON

# Additive complete public query pipeline, same API as the frozen runner:
python3 query_native_emitter/run.py ACC_CT QUERY_JSON OUTPUT_CT NEW_RUN_DIR
```

[DERIVED] `run.py` is the frozen query runner with only its emission subprocess changed. Its native public export, input-hash checks, unchanged prover call, fresh verifier, cancellation inheritance and no-private-reader behavior remain. `PIPELINE.json` selects the additive producer and existing query backend. This new complete wrapper is implemented and syntax-checked; it has **not** been used to relabel or rerun the old two-class service demonstration. The complete byte equality is the basis for avoiding a redundant proof of the frozen input.

[EXECUTED] Rebuild the native consumer with `cargo build --manifest-path native/Cargo.toml --release --offline -j2`. The retained `build/Compiler` overlay supports a one-module Lean check and `lean --run EmitQueryWitnessPlan.lean NEW_PROGRAM_DIR`; full commands are in the task logs. The generated plan is reusable, so normal queries launch no Lean interpreter. New future cases must use new output directories.
