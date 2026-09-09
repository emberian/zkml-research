# Actual untagged leaf hash: one cross-shape alias

[EXECUTED] One tiny native executable constructs two distinct canonical BabyBear payloads of lengths 20 and 24 with the same actual deployed leaf hash. It links the unchanged Plonky3 hash/permutation crates at revision `82cfad73cd734d37a0d51953094f970c531817ec`; the shared backend instantiates precisely `PaddingFreeSponge<default_babybear_poseidon2_16,16,8,8>`. No full proof, opening, key, PBS, transcript or private data was generated.

The 20-word payload is `[1,2,…,20]`. The 24-word payload appends:

```
[1538770609, 1042332825, 1628922041, 1590154732]
```

Both actual hashes, displayed as canonical field representatives, are:

```
[164944249, 644035534, 1060062985, 1741835111,
 1309747756, 333652885, 1764165391, 1250509816]
```

[DERIVED] After absorbing the first 16 words, let the actual permutation state be S. The 20-word input overwrites lanes 0–3 of the rate and leaves lanes 4–7 as S[4..8]. The longer input explicitly overwrites those latter lanes with the same values. The final permutation receives identical states. The constructor calls the real hash separately on both messages and checks equality; it does not substitute a handwritten hash. All reported integers are canonical field values, not the Montgomery words in native serde.

[EXECUTED] Exact inputs, intermediate state and hashes are in `results/result.json`, SHA256 `5306d6386501718d9928c634093085b2ee27dae8b6753b2712bbb872850fd76f`. `SOURCE_PINS.json` was written before the one constructor invocation and all 13 watched sources/binary inputs remained unchanged. Command and 5.609 ms process duration are retained in `results/command.json`; this is not a throughput benchmark. A path-resolution error occurred before source pins or execution, was fixed, and the native constructor then ran once.

[SOURCE / DERIVED] Shape compatibility in the explicit `fixed-ir2-whole-query-canonical-v1` admission mode:

| Expected root/leaf role | Required payload | 20-word input | 24-word input |
|---|---:|---|---|
| Final FRI round, arity 4 | 4×4 base coefficients + 4 salt words = 20 | Compatible | Incompatible |
| First four FRI rounds, arity 8 | 8×4 + 4 = 36 | Incompatible | Incompatible |
| Input batch 0 or 4, two width-8 base matrices | (8+4)+(8+4) = 24 | Incompatible | Compatible |

These are shape facts, not statements that these arbitrary payloads form accepted proofs. The 24-word interpretation uses another root role. Under the final FRI interpretation it has the same 16 data words and eight salt words, violating canonical admission's four-word salt requirement.

[EXECUTED pure public data] `shape_check.py` imports the existing canonical checker without running its main/verifier. It rechecks the retained `canonical001` public log, extends one arity-4 FRI salt vector from four to eight words in memory, and observes canonical refusal. No cryptographic verifier runs and no saved log is modified. `results/shape.json` records the exact checker/log hashes and results.

[SOURCE] Exact read-only source boundaries:

- Shared backend `research/vfhe_2026_09_08/proved_operation/backend/src/lib.rs:20–43`: deployed permutation, leaf hash dimensions and four-word hiding MMCS configuration.
- Cached Plonky3 `symmetric/src/sponge.rs:126–203`: overwrite-mode implementation and its explicit fixed-length-only security warning.
- Cached Plonky3 `merkle-tree/src/hiding_mmcs.rs:117–178`: salt proofs are vectors; the unmodified verifier concatenates them without imposing a length of four. This is distinct from the stronger canonical mode.
- `query_runtime/acceptance_bridge/run.py:11–40`: fixed template, schedule, width and salt admission; `:60–90` collects exact input widths and salt lengths.
- Vendored FRI `src/verifier.rs:403–450`: arity/sibling checks and extension-row reconstruction before MMCS verification.

[DERIVED] A global collision event over arbitrary unequal untagged leaf byte/field strings includes this trivial constructor and cannot receive a generic collision-resistance bound. The extraction residual must constrain both competing preimages to the same expected root role and leaf shape, or quotient irrelevant encoding aliases explicitly. This pair alone does not require an encoding repair for the fixed canonical profile: its two lengths are never simultaneously admitted for the same leaf role. It also does not establish overall profile soundness or exclude other collision mechanisms. A future variable-length domain would need separate justification or an explicit encoding change; no backend/proof changes are made here.

Reproduce the native constructor once in a fresh copy of this directory (the runner refuses to overwrite its retained result):

```sh
cargo build --release --offline
python3 -B run_once.py
```

The public shape-only check is `python3 -B shape_check.py`. Work stops after this constructor and its shape analysis.
