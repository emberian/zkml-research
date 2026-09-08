# Native Lean-plan witness generation for the actual BFV update

[EXECUTED] Complete event66 expiry/update witness emission took **0.197 seconds** (0.186 seconds execute/write). Every **33,325,056-byte trace** byte and **268,925-byte template** byte matches the already-proved production artifact in `update_pipeline/runs/event66_fast/emitted/`. The recorded production interpreter emission took38.504 seconds. This is one native observation against that retained same-case artifact, not a rerun of the old timing or proof. No new crypto execution was performed.

[DERIVED] The source relation is exactly the existing `BfvExpiry.system`: two actual primes, canonical accumulator/fresh/old/output words, and `output = (acc + fresh + q - old) % q` for each serialized NTT coefficient. Neither the source terms, emitted template, prover/backend settings nor public reader changed. This generator does not authorize FIFO selection, model changes, keys, recipients or private reading.

[DERIVED] `Compiler/BfvExpiryWitnessPlan.lean` imports the frozen query witness-plan builder and the actual expiry layout. It emits2993 sequential instructions/registers, using the same instruction schema and **the exact same native binary** as query emission. It compiles public-word reads, canonical slack/bit witnesses, quotient computation and offset signed carries into the imported wire positions. `EmitExpiryWitnessPlan.lean` generates the unchanged template by the existing Signature.fold. The instruction format retains its original query-named schema string for binary compatibility; its header supplies the operation's1017-column layout and57-entry public input arity.

[DERIVED] These instructions and their native executor are untrusted witness generation. There is no new AIR or universal native implementation-equivalence theorem. All future actual proofs still check the existing relation; a defective witness generator causes refusal without weakening those constraints. The executor uses checked i128 arithmetic and buffered LE-u32 writing. The actual update masses fit this executor; the separate large-RNS rescale lane needs its own BigInt successor.

[EXECUTED] The plan module built with an empty `results/build-plan01.log`. Plan generation checked all four original constructed Lean cases. Both direct and wrapped native execution produce their complete witness arrays byte-for-byte. A finite census checks that all2993 registers are assigned exactly once. `RESULTS.json` and `results/event66.{stdout,stderr}` record the complete8192-row native execution and byte comparison. There was no whole-row interpreter recheck and no redundant proof run.

[EXECUTED] Selected hashes:

- trace: `e118a52e777dbab4b88a309505c74161d7fe837f7b7f26174fdcfb0219e5f1ac`
- unchanged approved template: `1afc2b3a120f59fdd79d273c6d32887373c5718225cb6e94b82a7231010c3aa7`
- update plan: `328544d069866f9b23571e8b2338ea21c01bdec404dc0ba08df9afd2f09dd88e`
- shared native witness binary: `15102c5f9ae90e30755fb23c4b8091ba4c28b48e0c15a908115c0b0b88991093`

[EXECUTED] `SOURCE_PINS.json` pins the selected implementation and shared dependencies. `expiry-native-plan.patch` adds the two Lean producer files for later integration; existing companion trees and frozen packages remain read-only. There are no new theorem/lemma declarations: the same existing arithmetic theorem remains selected.

## Additive interfaces

```sh
# Only witness emission; verifies pins and refuses existing output directories:
python3 update_native_emitter/emit.py NEW_OUT_DIR PUBLIC_ROWS_JSON

# Complete public update pipeline, compatible positional case/job API:
python3 update_native_emitter/run.py CASE_DIR NEW_RUN_DIR --threads 4

# Complete public query pipeline from the separate frozen native successor:
python3 query_native_emitter/run.py ACC_CT QUERY_JSON OUTPUT_CT NEW_RUN_DIR
```

[DERIVED] The update wrapper is an additive copy of the existing public pipeline with its emitter replaced. It preserves case staging, public export, approved-template check, actual prove-update and fresh verify-update calls, result recording and no-private-reader scope. It pins the approved native update runtime. The query wrapper likewise preserves its original reader/prover/verifier and cancellation behavior. These native pipeline wrappers are implemented and syntax-checked; this package does not claim a new complete live-service run. The service owner selected them for a fresh instance, with fresh proofs and its own proof-before-receive gate; old instances/configurations remain unchanged.

[EXECUTED] This makes both untrusted witness-generation stages small in the retained cases: update0.197 seconds and query0.468 seconds. It does not yet measure the new combined service latency. The existing protocol, reader, decryption and classification limitations remain explicit in their owning packages.
