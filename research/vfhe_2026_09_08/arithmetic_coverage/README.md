# Generated arithmetic for complete BFV linear operations

[EXECUTED] This package emits the relation and witness consumed by `../proved_operation/`: the complete three-modulus `3A + 5B` ciphertext operation, then the actual learner's two-modulus `acc + fresh − old` expiry operation. The arithmetic constraints are a `Signature.fold` of proved Lean source terms. Rust supplies the public coefficient table, loads the emitted witness, and invokes its existing prover. No arithmetic AIR or carry producer was authored in Rust in this lane.

[DERIVED] This closes integer arithmetic coverage for these linear operations. It does not close VERDICTS §7.5's ciphertext-multiplication rescale, convolution or relinearization hole. In particular, no integer rounding is silently replaced by a field equality here.

## Code and mathematical claim

- `Compiler/BfvLinearCombination.lean`: reusable modulus-parameterized whole-word law. For every wire assignment and every `0 < q < 64^7`, accepting the generated relation forces canonical A, B, O and `O = (3*A + 5*B) % q`.
- `Compiler/BfvExpiry.lean`: reuses the same canonical-word gadget. Acceptance forces canonical accumulator, fresh, old, output and `out = (acc + fresh + q - old) % q`. The extra q makes the numerator nonnegative. The quotient is retained in the relation.
- Both `*Layout.lean` modules instantiate the actual moduli and public-column layouts. `wholeRowSound`, `simplifiedSource_sound`, and `descriptor_sound` connect their complete row to the source system, simplified system used by IR2, and existing CSE/flattened descriptor respectively.
- `Compiler/BfvOperationWitness.lean` supplies kernel-checked inhabited q=31 examples: `3*1+5*2=13` and `(17+23+31-9)%31=0`. Universal falsifiers rule out outputs 14 and 1 for those respective inputs, regardless of auxiliary values.

[DERIVED] Canonicality uses the existing `AirBignum.addGadget` and a pinned q−1 word: value + ranged slack = q−1. Seven radix 64 digits retain the entire word. Signed carries are offset into small unsigned ranges and have pinned endpoints; `radix_balance` telescopes every digit equation to an integer identity. The proof derives bounds on both sides before lifting a BabyBear equality to equality over naturals. The theorem needs q positive and within capacity; it does not assume or prove primality of the BFV moduli.

[EXECUTED] All five final modules compile separately with Lean 4.30.0 and their 23 exact guarded axiom reports. Every report is `[propext, Classical.choice, Quot.sound]`; no `sorry`, new axiom, `native_decide`, or guard-only mathematical claim is used. The small witnesses use kernel computation. `results/checked_modules.json` records exact commands, source hashes, elapsed times and output files. Prebuilt dependency oleans are reused through a local overlay; this is not a whole-tree build. The existing read-only companion import-boundary script passes. No `Theory/` or `Selvage/` source is changed.

## Executable handoff

| Operation | Public row | Moduli | Trace width |
|---|---|---|---:|
| Weighted ciphertext | rowID, A[3][7], B[3][7], O[3][7] | 68719403009, 68719230977, 137438822401 | 1234 |
| Learner expiry | rowID, acc[2][7], fresh[2][7], old[2][7], out[2][7] | 2199023190017, 4398046486529 | 1017 |

[EXECUTED] Each public word is little-endian radix 64. The first public tuple is 64 columns and the second 57. Public table11 uses the backend's existing `exact_public_rows` mechanism. Its row ID is part of the lookup tuple. Both traces contain 8192 rows, covering both components of the N4096 ciphertexts. The expiry input is `../proved_operation/results/learner_expiry001/public_ntt_rows.json`: directly decoded stored NTT slots, without an inverse transform. The weighted input is `../proved_operation/results/case001/public_rows.json`.

- `EmitBfvLinearCombination.lean` produces `artifacts/template_ir2.json`, `artifacts/trace.leu32`, `artifacts/minidregg_descriptor.json`, and `artifacts/emission.json`.
- `EmitBfvExpiry.lean` produces the corresponding files under `artifacts_expiry/`.
- Each exporter constructs canonicality, quotient and carry witnesses in Lean from the supplied actual input/output digits. It checks the generated source constraints for every output row before writing it. The external output is never chosen by the witness producer.
- The primary runtime trace is row-major, flat little-endian u32, with one canonical BabyBear element per trace column. The standard minidregg descriptor is emitted separately through the existing emitter; its flattened auxiliary wires are not needed in the direct degree-two IR2 trace.

[EXECUTED] The weighted export completed with 1698 arithmetic constraints per row, four constructed source/standard-descriptor positives, changed-output and radix 64 negatives, and all 8192 actual source rows checked. The trace is 40,435,712 bytes. The strict existing Rust parser accepted its template. See `results/export_004.log` and the runtime lane's results for actual proof execution. The expiry export also completed: 1456 arithmetic constraints per row, all 8192 actual stored-NTT rows checked, four positive controls and both negative controls passed; its trace is 33,325,056 bytes (`results/expiry_export_002.log`). `artifact_pins.json` identifies both complete handoffs and their exact public inputs.

[EXECUTED] Failures were retained: an inferred field-valued mutable carry caused the first producer to perform field division; the source relation rejected it, and the variable is now explicitly `Nat`. The existing parser requires discriminator-first JSON tags; serialization now uses an ordered String fold. Two large finite-witness kernel probes were stopped at 120 seconds each; the final proposal uses the small q31 witnesses instead. Those probes are not a claim of kernel infeasibility. Their abandoned source/data are under `results/` and are not in the patch.

## Apply and reproduce

[EXECUTED] `proposal.patch` adds only the five Compiler modules and two exporters. Its application to an empty isolated scratch directory passes and yields byte-identical sources (`results/patch_application.json`). `source_pins.json` identifies proposal files, relevant reused source files, and exact direct dependency oleans. No companion source was modified. Root owns integration and commits.

[SOURCE] Required predecessor modules are the existing `Compiler.IntegerCertificateEmission` from `research/learn_infer_only/formal/integer_certificate_emission/Compiler/IntegerCertificateEmission.lean`, and `Compiler.AirSimplify` from that package's `optimization/Compiler/AirSimplify.lean`, together with their existing compiler dependencies. After applying those and this patch, `import Compiler.BfvOperationWitness` imports the complete five-module proposal. Build that module before running either exporter.

```
lake env lean --run EmitBfvLinearCombination.lean OUT_DIR PUBLIC_ROWS_JSON
lake env lean --run EmitBfvExpiry.lean OUT_DIR PUBLIC_NTT_ROWS_JSON
```

[OPEN] The Lean result is source arithmetic soundness and its existing emitter refinement. It is not a formal refinement of JSON serialization, the Rust parser/trace loader, ExactPublic's complete implementation, the proof protocol, or the BFV library. Witness generation completeness for arbitrary valid inputs is not proved; a bad producer can fail to provide a witness. The actual prover independently checks the supplied witness. The coefficient-reader connection, public preprocessing commitments, prover/verifier execution and adversarial proof controls belong to `../proved_operation/`. Cryptographic security, noise/decryption correctness, useful learning, and a whole encrypted-learner theorem are not established by this arithmetic package.
