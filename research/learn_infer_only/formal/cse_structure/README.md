# CSE structure and total emitted execution

[DERIVED] `Compiler/CseStructure.lean` proves that the existing CSE pass preserves
`SSA` and `WellFormed`. The theorem is generic over the constant type with its existing
`DecidableEq` and `Hashable` instances. It has no field-operation, native-computation,
gate-equation or output-equation assumption. No compiler pass, evaluator or Boolean
circuit is defined in this package.

[DERIVED] `cseGo_good` proves preservation by induction over the original gate list.
Its state invariant says that substitution representatives never increase their
original wire indices; signature hits name kept gates; kept gates retain operand and
allocation bounds; and kept outputs are in decreasing order before reversal. A separate
induction premise places every kept output before every remaining gate output. The
signature-hit case therefore inserts a smaller representative. The miss case keeps the
original output and rewrites operands through a non-increasing substitution. Existing
HashMap lookup/insert laws handle both cases without evaluating opaque hashes.

[DERIVED] `raw_premises_inhabited` supplies both hypotheses for every emitted source
term list using the existing `emit_ssa` and `emit_wellFormed` theorems.
`shared_structure` applies the new CSE theorem. `shared_execution_total` then uses the
existing `DescriptorEval.fillAux` input-preservation and gate-satisfaction laws and the
frozen `shared_output_correctness` theorem. It proves the evaluator's output list is
the source terms' evaluation for **every source list and every input**, with no
structural-check or gate-value premise.

[DERIVED] `learn_execution_total` and `infer_execution_total` instantiate the exact
frozen source schedules. Learn covers every four-register signed-byte state, every
two-bit address and every signed-byte label. Infer covers every such state and address.
They decode the existing F2 evaluator's outputs to the existing `PrivateAddressEma`
word operation and sign selection. These statements require neither a compiled
structural verdict nor kernel normalization of the fixed CSE expression. They remove
the open structural premise of the prior EMA execution corollaries.

[DERIVED nonvacuity and teeth] Premise inhabitation is universal for source emission.
The actual Learn subject at zero state, address three and label 120 changes its selected
byte, and the actual schedule's output cannot remain the all-zero state. Two separate
single-gate counterexamples show why the generic structural theorem cannot drop either
hypothesis: a bounded self-read violates SSA, while an SSA gate writing an input violates
allocation bounds. `singleton_cse` proves the existing pass keeps each singleton using
map laws, so these are counterexamples about the CSE result itself.

[SOURCE reused] The pass is `Compiler/EmitShare.lean:125` (`cseGo`) and `:136` (`cse`)
in `/Users/ember/dev/minidregg`; emission shape is `EmitShare.lean:552` (`emit_ssa`)
and `Emit.lean:446` (`emit_wellFormed`). Execution reuses `DescriptorEval.lean:191`
(`fillAux_gates_hold`) and `:212` (`fillAux_getD_of_lt`). These exact source hashes are
recorded in `results/verification.json`. The frozen dependency sources are recorded
in `results/environment.json` and freshly compiled into the owned overlay.

[OPEN precise boundary] This proves the SSA/allocation conditions consumed by the
existing Lean array evaluator. It does not prove the stronger initialized-reference
predicate `EmittedScheduleExecution.ForwardValid` for all CSE-produced descriptors.
That stronger predicate corresponds to the Rust validator's option-valued storage;
the frozen package already retains compiled checks for the actual JSON descriptors.
This new package proves total Lean execution correctness for the actual source, not
a refinement of Rust parsing, `Vec<Option<_>>`, serde, compiled Lean/Rust, TFHE Boolean
gates, noise, ciphertext serialization or replay-byte determinism. The frozen JSON
emission/byte reproduction remains executed evidence from the predecessor package.
No crypto or teacher-utility run is performed here.

[EXECUTED scope] This is an isolated source patch with single-file checks and exact
axiom pins. It imports the three frozen proposal dependencies, freshly compiled against
cached companion/Mathlib oleans; it does not claim a fresh build of that entire external
dependency closure. Root owns the full umbrella build and independent review. All
predecessor packages and long-run inputs are left unchanged.

[EXECUTED final check] All 18 theorem declarations have exact `#print axioms` pins.
`results/lean_005.json` is the clean final single-file run; all printed dependencies are
drawn from `propext`, `Classical.choice` and `Quot.sound`. `results/verification.json`
records successful patch application, source equality and both isolated and companion
import-boundary checks. All 81 frozen predecessor files and companion HEAD/status are
unchanged. Source SHA-256:
`9828878c2ac7b175c9d9928348b0a858573ad951a569a90997684732e0289608`.
Patch SHA-256: `ca0d13b93fba0e685800535c5f84ffa64f4d74c276fd6ec40a8c4cba315a155d`.

[DERIVED next] Integrate this module after `PrivateAddressEma`,
`PrivateAddressEmaSchedule` and `EmittedScheduleExecution`. Use the unconditional
execution corollaries for the emitted EMA source. Any stronger Rust-language or
initialized-reference refinement remains a separate proof obligation.
