# Descriptor execution seam

[DERIVED] `Compiler/EmittedScheduleExecution.lean` replaces the gate-equations premise
of the existing emitted EMA proof with a structural-check premise. It reuses
`Compiler.DescriptorEval.fillAux` as the executor. It defines no gate evaluator,
Boolean circuit or learner arithmetic. `execute` only reads the descriptor's output
roots from the existing evaluator's array.

[DERIVED] `ForwardValid` checks the schema's execution shape: the input prefix is
initialized, each gate reads initialized references, each output is a fresh auxiliary
wire within the allocation, outputs strictly increase, and final output references
are initialized. Constants are always available. Sparse allocation holes are allowed.
The descriptor field `zeros` is used here as output references, as in the frozen source;
there is no requirement that these values equal zero. `nPublic` is zero in the emitted
JSON source; the generic predicate merely requires its ordinary nested bound.

[DERIVED] The new proof chain is
`validCheck = true → ForwardValid → SSA ∧ WellFormed → fillAux input preservation
and gate equations → existing shared term-output theorem → EMA Learn/Infer outputs`.
`execution_soundness` quantifies over every finite F2 descriptor and every correctly
sized input array satisfying the structural checker. `shared_execution_correctness`
quantifies over every finite source term list and input. The application theorems
retain a structural validity premise for the actual CSE-produced schedule; they
contain no assumed gate-value or output-value equations. They inherit the full signed
byte and private address range of the frozen EMA theorem, not a handful of fixture rows.

[DERIVED] `decoded_gate_operations` reuses the frozen encoding lemmas to identify F2
addition/multiplication with Boolean XOR/AND. The sparse nonconstant subject has two
inputs, two gates, two unused slots and a constant output. Its kernel-checked witness,
wrong answer, forward read, unused-hole read, input overwrite and decreasing-output
falsifiers test separate obligations. The predicate is inhabited without assuming any
semantic result.

[SOURCE] The reused universal executor laws are
`/Users/ember/dev/minidregg/Compiler/DescriptorEval.lean:191`
(`fillAux_gates_hold`) and `:212` (`fillAux_getD_of_lt`). The original source-to-output
seam is the frozen `private_address_ema/emitted_schedule/Compiler/PrivateAddressEmaSchedule.lean:126`
(`shared_output_correctness`), with EMA corollaries at lines 432 and 439.
The frozen Rust implementation's structural validation is at
`experiments/end_to_end/private_ema/emitted_runtime/src/lib.rs:99` and its generic
`Schedule::evaluate` loop at line 177. This is a source correspondence audit, not a
Rust semantics proof.

[EXECUTED bounded negative result] Direct `decide +kernel` attempts to prove the
actual computed descriptors structurally valid were stopped at the 1 GiB sampled RSS
cap. Infer stopped after 12.34 s with maximum sampled RSS 1,064,624 KiB; Learn after
7.24 s with 1,175,216 KiB. Sampling was once per second, so the stop can overshoot the
cap. Neither attempt produced a proof. Exact probe sources, commands and samples are
in `results/kernel_infer.*` and `results/kernel_learn.*`; the larger configured time
caps were not reached. No `native_decide` or compiled check was turned into a theorem.
An empty file with the identical imports/open declarations/options also stopped at the
cap (8.22 s, maximum sampled RSS 1,085,200 KiB; `results/kernel_baseline.*`). Consequently,
these attempts do **not** establish that kernel reduction itself is impractical:
dependency loading alone exhausts this cap.

[EXECUTED follow-on probes] Root authorized one sequential 3 GiB / 120 s attempt per
descriptor after measuring machine headroom. Infer exited with an elaboration error
after 10.12 s (maximum sampled RSS 2,947,312 KiB): `decide +kernel` could not reduce
the proposition's decidable instance. Lean's diagnostic then printed `sorryAx` for
that failed elaboration; this is retained failure output, not a theorem in the checked
patch. Learn was resource-stopped after 14.41 s (3,220,976 KiB sampled). No further
attempt or cap escalation was made. See `results/kernel_infer_3g.*`,
`results/kernel_learn_3g.*` and `results/probe_summary.json`.

[SOURCE / INFERRED] Lean's `Init/Prelude.lean:4645` declares `mixHash` opaque. The
existing `EmitShare` DWire and product hashing path uses it. This identifies a
kernel-normalization obstacle on the CSE path; the Infer diagnostic alone does not
isolate it as the only obstacle. A structural theorem avoids computing these hashes.

[OPEN] A general CSE structural-preservation theorem, or a feasible kernel certificate
for the two concrete CSE results, would remove the remaining structural premise of the
actual EMA corollaries. A compiled check of that premise is executed evidence only.

[OPEN runtime TCB] This is a Lean execution model built from an existing evaluator,
not a refinement of Rust execution. JSON serialization/parsing, schema tags and resource
caps, serde, Rust `Vec<Option<_>>` allocation and indexing, compiled Lean and Rust,
the generic backend implementation, TFHE gate correctness/noise, encryption, ciphertext
serialization and replay-byte determinism remain outside the kernel proof. The model's
zero-filled unused slots are harmless under the proved initialized-reference discipline;
that does not prove Rust's option-valued storage implements the model. No crypto run or
teacher utility evaluation is performed by this package.

[EXECUTED isolation] All new sources and reports live in this directory. Frozen EMA
sources, emission runner, schema, JSON and verification records are read-only inputs.
Checks compile fresh copies of the two proposed dependency modules into an owned olean
overlay, reusing cached companion/Mathlib dependencies. Root owns the full umbrella
build and integration. Failed iterations are retained.

[EXECUTED result] All 19 theorem declarations have exact axiom pins; the final clean
single-file run is `results/lean_006.json`. `results/verification.json` records successful
patch application, source equality, import boundary checks, compiled validity of both
actual descriptors, and byte-exact reproduction of both frozen JSON files in a separate
directory. All 41 previously frozen package files and the companion HEAD/status were
unchanged. The report preserves all five bounded probe records separately from the
successful package checks. Source SHA-256:
`37d9b62f5a0b0b3b80fa7b2de2f8322e71c92b4635710f64eb848f573bffb077`.
Patch SHA-256: `057672fd7654df79812d5071bd0c00497ef7c462b53c0314a62c97fcc219d72c`.
