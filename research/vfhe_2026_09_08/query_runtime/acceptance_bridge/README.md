# Actual IR2 acceptance bridge

[EXECUTED] `replay001` accepts the saved `fast_live_successor` class-0 query proof
through an instrumented copy of the actual native IR2 verifier. The bridge does
not prove again, read a private key, or modify the original runtime or companion
sources. The input proof remains
`53ac28c1c9bd281f33bf1b8ddf7e54cb2ec4ba499d7685a79f56de1992b611bf`.

The mathematical handoff is [replay001/fri_view.json](replay001/fri_view.json):
canonical field values, all transcript operations in their actual order, every
input matrix/root/opening, all 38 query indices, and all 190 packed fold rows,
points, challenges, results, carried values and terminal checks. Its SHA256 is
`54603401e8b4271d191800897fae65165c29afb0a8bca43c16317ebf1c0adc41`.
The exact native serde stream is [replay001/events.jsonl](replay001/events.jsonl),
SHA256 `14954ea9148d78da52f6e40baf21d493378f2c2cc8363cf1b85762dabc061d5d`.

## Run

From the repository root, build the isolated overlay once:

```sh
python3 -B research/vfhe_2026_09_08/query_runtime/acceptance_bridge/build.py
```

The overlay is under the already ignored `query_runtime/target/acceptance_bridge/`.
The build refuses to overwrite it. `build.log` retains the completed offline build;
`instrumentation.patch` is the exact generated source delta. The original query
parser, statement construction, backend, proof schema, arithmetic and verifier
remain copied or delegated; only the new executable's entry point restricts it
to verification. Its challenger delegates observations/samples to the original
DuplexChallenger. A clone reveals the raw word for `sample_bits`, and an equality
assertion checks that its masking agrees with the original real-state operation.

```sh
python3 -B research/vfhe_2026_09_08/query_runtime/acceptance_bridge/run.py \
  TEMPLATE CASE PROOF NEW_REPLAY_DIR
python3 -B research/vfhe_2026_09_08/query_runtime/acceptance_bridge/project.py \
  NEW_REPLAY_DIR
```

The first command performs actual strict-postcard native verification and retains
the ordered trace only as accepted after exit zero, exact input/source rechecks,
and correspondence checks. The second reads that saved trace and converts field
representations, checking all decoded Lagrange folds and carried-index chains.
No second native verification occurs in projection.

`run.py --canonical TEMPLATE CASE PROOF NEW_REPLAY_DIR` is the explicitly stronger
mode agreed with the theorem owner. It only supports the approved query template
`f42c5efc…`, height 17, the five declared batch/point/width shapes below, four
hiding columns except zero for public preprocessing, canonical scheduling, and
four-word salts. Unknown profiles or failed predicates stop before an accepted
artifact is written. Python `-O` is rejected. This mode **always** launches fresh
native verification on the supplied statement/proof; it has no log-input mode.
`project.py` is only a saved-evidence converter and never a submit gate.

[EXECUTED] The final canonical predicate function passes on the original retained
invocation (`replay001/canonical_observed.json`). After that implementation,
the explicitly authorized `--canonical` CLI ran once on the same saved proof in
the separate [canonical001/accepted.json](canonical001/accepted.json). Native
verification returned `verified:true`; the stronger admission separately returned
`passed:true` with `fresh_native_verification_in_this_invocation:true`. All source
and input posthashes match. The command took 8.596553 s wall time, including event
logging. Its event stream is byte-identical to the original replay, so the same
canonical field projection applies. The original replay files remain unchanged;
no negative grid or further native replay was run.

## What this proof actually uses

[EXECUTED] The parameters are BabyBear `p=2013265921`, extension
`F_p[X]/(X^4-11)`, blowup 8, final polynomial length 1, 38 queries, commit PoW 0
and query PoW 16. The input LDE height is `2^17`; the actual log-arities are
`[3,3,3,3,2]`, taking heights `17→14→11→8→5→3`. All 23 input matrices have the
same height. This record has **no cross-height injection**, so it does not
demonstrate a nonzero `beta^arity * reduced_opening` injection.

Input widths after the hiding PCS merge are `[8,8]`, `[2513,5]`, sixteen
width-8 matrices, `[59]`, and `[8,8]` in the five respective batches. The first,
third and fourth batches have one opening point per matrix; the other two have
two. This ordering is randomization, main trace, quotient chunks, public
preprocessing, permutation, respectively. See the exact source at
`p3-batch-stark/src/verifier/mod.rs:302–502`, revision `82cfad73` in Cargo.lock.

[SOURCE] `ExtensionMmcs::verify_batch` flattens each extension element into its
four ordered base coefficients. `MerkleTreeHidingMmcs::verify_batch` appends a
supplied salt vector to each matrix row. The inner MMCS concatenates rows of
equal height in matrix order into the leaf hash, then verifies its Merkle path;
shorter matrix groups would be injected at their corresponding tree heights.
For the FRI batches here, each leaf is one row of 8 or 4 extension elements,
flattened to 32 or 16 base words, followed by 4 salt words. All caps have one
8-word root. The input paths have length 17; the FRI paths have lengths
14, 11, 8, 5 and 3. These are salted packed openings, not individual scalar leaves.

[SOURCE/EXECUTED] The batch-STARK prefix observes instance structure, main and
preprocessing commitments; samples lookup challenges; observes permutation and
lookup sums; samples the constraint-combination challenge; observes quotient and
randomization commitments; then samples the out-of-domain point. The PCS observes
all opened evaluations, including merged random-codeword values. FRI then samples
its separate batching `alpha`, observes each FRI root and samples its `beta`,
observes the final coefficient, **then** observes the arities, checks query PoW,
and samples the 38 indices. Commit PoW 0 absorbs nothing. The trace records both
the semantic FRI milestones and each actual challenger operation.

[SOURCE/EXECUTED] Native serde stores BabyBear in Montgomery form, `x·2^32 mod p`;
its Ext4 object holds four such words in ascending power basis. `fri_view.json`
converts them with `(2^32)^(-1) mod p`. `sample_bits.raw_base_word` was already
canonical and is not converted again. The initial summary encoding label was
corrected during interpretation; the executed runner is retained as
`replay001/run.executed.py`. The final runner also adds the separate stronger
canonical mode described above; the native binary and event bytes are unchanged.
All 190 decoded interpolation results and 38 carried-index chains agree.

The input quotient is evaluated at `31·g17^reverse17(index)`. FRI folding uses
the unshifted subgroup fibre points recorded in `xs`. Query transport repeatedly
takes the low `log_arity` bits as the packed-row position and shifts those bits
off to obtain the next row index. The raw index is a canonical base word modulo
`2^17`, not a rejection-sampled uniform integer. Under a hypothetical uniform
base word, index zero has probability `15361/p` and every other index `15360/p`.
This statement does not establish Fiat–Shamir independence.

## Boundary for the theorem

[EXECUTED] This proof matches the public-height canonical scheduler, all 1,064
salt rows have length four, and all opened widths match their claimed values.
These are additional observed predicates. **The original verifier does not
enforce canonical scheduling before beta sampling or fixed salt lengths.** Its
inner MMCS also ignores the supplied width field. The bridge does not silently
repair those rules or infer a general acceptance-to-scalar theorem from this
honest proof. A theorem over arbitrary accepted proofs must model those choices
or be attached to an explicitly strengthened verifier.

[EXECUTED] The single instrumented replay took 8.983159 s wall time and peaked at
83,247,104 bytes RSS. This includes writing 20.84 MB of event JSON and is not a
performance measurement of the ordinary verifier. Exact argv, resources, input
pins and native acceptance are retained in `replay001/command.json` and
`stdout.jsonl`. Source inputs and original proof bytes were unchanged across it.
