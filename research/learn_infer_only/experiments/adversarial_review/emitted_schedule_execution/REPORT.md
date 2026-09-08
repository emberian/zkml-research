# Independent review of emitted schedule execution

[DERIVED verdict] **Accept the selected conditional Lean execution theorem. No blocking source defect found.** The structural predicate proves the hypotheses of the existing executor, whose input preservation and gate equations feed the existing frozen source-output theorem. Concrete CSE descriptor validity remains a premise of both EMA application theorems. Compiled validity checks do not remove it. This review does not certify a Rust parser, Rust execution, serde or TFHE refinement.

[SOURCE exact target] The reviewed module is `research/learn_infer_only/formal/emitted_schedule_execution/Compiler/EmittedScheduleExecution.lean`, SHA-256 `37d9b62f5a0b0b3b80fa7b2de2f8322e71c92b4635710f64eb848f573bffb077`. The patch is `minidregg-emitted-schedule-execution.patch` in that package, SHA-256 `057672fd7654df79812d5071bd0c00497ef7c462b53c0314a62c97fcc219d72c`. Below, **E** denotes this module; **S** denotes the frozen `research/learn_infer_only/formal/private_address_ema/emitted_schedule/Compiler/PrivateAddressEmaSchedule.lean`; **T** denotes the frozen `research/learn_infer_only/formal/private_address_ema/Theory/PrivateAddressEma.lean`. Companion paths refer to `/Users/ember/dev/minidregg/`.

## The complete proof chain

| Step | Exact source | Review finding |
|---|---|---|
| A boolean structural check reflects a proposition | E:49 `ForwardValid`, E:58 `validCheck`, E:75 `validCheck_iff` | [DERIVED] No gate values, expected outputs or evaluator equations occur in the predicate. |
| Initialized references and increasing outputs give existing shape hypotheses | E:84 `forwardGates_shape`, E:117 `valid_implies_shape` | [DERIVED] The induction maintains every available wire below the next output lower bound; it proves operand bounds, allocated auxiliary outputs and pairwise strictly increasing outputs. |
| Existing shape hypotheses give actual executor equations | E:135 `execution_soundness`; `Compiler/DescriptorEval.lean:191` `fillAux_gates_hold`, `:212` `fillAux_getD_of_lt` | [DERIVED] The result is about the existing `fillAux` array. Input size is required; every initial input is preserved and every gate holds on the final array. No abstract gate witness is substituted for execution. |
| Executed inputs and gates imply term outputs | E:141 `executed_inputs`, E:149 `shared_execution_correctness`; S:126 `shared_output_correctness` | [DERIVED] The valuation supplied to the frozen theorem is exactly `fillAux (shared es) (Array.ofFn inputs)`. The conclusion covers every finite F2 term list and typed input vector, conditional on that descriptor passing `validCheck`. |
| Exact frozen EMA source expressions give the intended word outputs | E:157 `learn_execution_correct`, E:166 `infer_execution_correct`; S:410 `learn_source_outputs`, S:421 `infer_source_outputs` | [DERIVED] Learn returns the 32 state bits; Infer returns the selected sign bit. Both application theorems retain `validCheck ... = true`. |

[SOURCE / DERIVED] The matched existing definitions are `Compiler/EmitShare.lean:317`, `ConstraintDescriptor.SSA`, and `Compiler/Emit.lean:427`, `ConstraintDescriptor.WellFormed`. SSA requires operands below their own gate output and output order; WellFormed gives nested header bounds, auxiliary output allocation and bounded output references. E:117 supplies these actual definitions. The proof neither introduces an unrelated SSA predicate nor assumes the executor result.

[DERIVED] Constants are always ready. Inputs are exactly `List.range d.nVars`; a gate output becomes ready only after its operands are checked. Output lower bounds advance to the preceding output plus one, so outputs cannot overwrite inputs or prior gates. Unallocated holes are permitted but are absent from the ready set. The final output references must be inputs, written gate outputs or constants. This is stronger than SSA plus allocation bounds: SSA alone could read a lower-numbered hole. The stronger predicate is sufficient, not claimed necessary, for the executor theorem.

[SOURCE / DERIVED] E:61 `execute` only projects descriptor `zeros` through `readArr (fillAux ...)`. In this frozen source, `zeros` stores output references; the new theorem does **not** assert that they evaluate to zero. `Compiler/DescriptorEval.lean:223` separately characterizes `descriptorHolds`, including zero-check values, and is not used to smuggle a zero-check conclusion into this patch. The witness's output `[1,1]` makes this distinction concrete.

[SOURCE / DERIVED] E:176 `decoded_gate_operations` handles all `a b : F2`, reusing the frozen encoding inverse and XOR/AND lemmas. It identifies field addition and multiplication with Boolean operations; it is not a backend implementation theorem. The theorem family is specialized to F2 descriptors, not arbitrary field descriptors. The EMA inputs quantify over all `State = Fin 4 → BitVec 8`, all two-bit addresses and all eight-bit labels (T:25–27); no `Within120` or restricted-label premise is silently added. The exact selected-slot signed EMA and sign-query meanings are T:30 `numerator`, T:33 `candidate`, T:42 `learn`, T:45 `infer`, with the frozen word-level correctness statement at T:50. The new patch reuses that source semantics rather than proving a new arithmetic circuit.

## Witnesses, refusals and remaining premise

| Control | Exact source | What it establishes |
|---|---|---|
| Sparse structural premise and correct input size | E:184 `sparseSubject`, E:188 `sparse_premises_inhabited` | [SOURCE / DERIVED] Two inputs, outputs at wires 3 and 5, allocation size 6, unused slots 2 and 4, and a constant output; the actual `ExecutionSoundness` premises are inhabited. |
| Positive output and nonconstant dependence | E:192 `sparse_subject`, E:194 `sparse_nonconstant` | [SOURCE / DERIVED] Inputs `[1,0]` yield `[1,1]`; inputs `[1,1]` yield `[0,1]`. The subject is not a constant-output tautology. |
| Wrong semantic answer | E:196 `wrong_answer_refused` | [SOURCE / DERIVED] The false answer `[0,1]` is rejected for `[1,0]`. |
| Forward reference | E:198 `forward_read_refused` | [SOURCE / DERIVED] Reading wire 5 before its definition fails structural validation. |
| Hole output | E:203 `hole_read_refused` | [SOURCE / DERIVED] Reading never-written slot 2 as a final output fails. |
| Input overwrite | E:206 `input_write_refused` | [SOURCE / DERIVED] A gate output at input wire 1 fails. |
| Decreasing outputs | E:212 `decreasing_output_refused` | [SOURCE / DERIVED] Writing wire 5 followed by wire 3 fails. |

[SOURCE / DERIVED] These are theorem declarations using `decide +kernel`, with exact axiom pins, rather than compiled boolean assertions. They demonstrate the intended obligations but are not a comprehensive parser-fuzzing suite. Generic correctness comes from E:135 and E:149, not from enumeration of these examples.

[SOURCE / OPEN] E:158 and E:167 explicitly require structural validity for the actual Learn and Infer CSE schedules. The existing S:142 `shared_premises_inhabited` and S:446 `learn_premises_inhabited` construct a gate-satisfying valuation using the raw emitted descriptor and CSE faithfulness. They do not establish `ForwardValid (shared es)` and cannot discharge this new premise. This package does not export an unconditional actual-schedule execution theorem.

[SOURCE reported execution] The author's pinned `results/verification.json` records compiled structural acceptance for Learn `(42 inputs, 11,562 wires, 538 gates, 32 outputs)` and Infer `(34 inputs, 46 wires, 9 gates, 1 output)`. It explicitly sets `actual_validity_kernel_proved` to false. Its byte-exact JSON reproduction is compiled emission evidence linking the fixed descriptor values to the frozen artifacts; no parser/serialization equivalence is kernel-proved here. This review checked the exact retained records and artifact hashes without repeating emission or execution.

[SOURCE bounded negative evidence] `README.md:44–68` and the pinned probe records correctly distinguish failed proof attempts from checked declarations. The 1 GiB cap also stopped the same-import empty baseline, so those runs do not isolate kernel reduction as impractical. The 3 GiB Infer run returned a failed decidable reduction; Learn hit the sampled cap. The failed Infer diagnostic's `sorryAx` is outside the selected module and is not an admitted theorem. The reported opaque `mixHash` path is a normalization obstacle, not evidence that it was the sole cause of failure. No additional probe or cap increase was needed for this review.

[SOURCE / OPEN] `CSE_FOLLOWUP.md:13–20` proposes a separate proof of CSE preservation of SSA and WellFormed. That would be sufficient to apply the existing `fillAux` laws and frozen output theorem directly, even without proving the stronger initialized-reference checker. It is a prospective successor, not an accomplishment of this selected patch, and does not by itself prove a Rust storage refinement.

## Runtime correspondence and scope

[SOURCE] The reviewed Rust source is `research/learn_infer_only/experiments/end_to_end/private_ema/emitted_runtime/src/lib.rs`. `Schedule::parse` starts at line 102; it marks the input prefix initialized at lines 123–124, checks output bounds/order and ready operands at lines 126–141, and validates final references at lines 143–145. `validate_reference` at line 206 accepts constants and requires a present initialized wire. Those conditions correspond to E:26–52 under the ordinary descriptor translation. The explicit duplicate-output check is redundant under the input lower bound and strict output order, so its absence as a separate Lean conjunct is not a structural mismatch.

[SOURCE / DERIVED] Rust `Schedule::evaluate` at line 177 checks input length, initializes `Vec<Option<B::Bit>>`, resolves gate operands, invokes backend XOR/AND and writes outputs. Lean `fillAux` uses a zero-filled `Array F2`. Readiness prevents the intended execution from observing unused holes, but the patch proves no relation between the two representations. Backend constants, gate implementation and ciphertext behavior require their own correspondence laws. The only runtime activity here was source reading.

[OPEN scope] Rust/JSON parsing, operation/schema tags, allowed dimension and resource caps, serde decoding, machine-size integer behavior, allocation/indexing, `Vec<Option<_>>`, compiler semantics, the concrete backend, TFHE correctness/noise, encryption and serialization remain outside the theorem. No new privacy or security bound, practical runtime guarantee, teacher utility result or deployment claim follows from this patch.

## Independent checks and provenance

[EXECUTED] Command: `python3 research/learn_infer_only/experiments/adversarial_review/emitted_schedule_execution/check.py`. Exact results and subprocess outputs are retained in `RESULTS.json`. The script uses only local hashes, JSON/text inspection and isolated `git apply`; it runs no Lean compiler, circuit execution, cryptography or network query. All checks passed:

- Source and patch match the two requested hashes; all 39 manifest-listed package files match.
- All 41 pinned frozen EMA inputs and all five directly reused/dependency source files still match the author records.
- A comment-aware source census finds exactly 19 theorem/lemma declarations and 19 matching guarded axiom outputs, including helpers and refusal controls. All pins contain only `propext`, `Classical.choice`, `Quot.sound`, or no axioms. The selected source contains no `sorry`, `sorryAx`, `axiom`, `admit`, `native_decide` or `unsafe` token outside comments/strings.
- The sole module import is the existing proposed `Compiler.PrivateAddressEmaSchedule`; the patch changes only `Compiler.lean` and adds `Compiler/EmittedScheduleExecution.lean`.
- Independent patch application in a temporary directory seeded with `Compiler.lean` from companion commit `6937394e1dc2c2aaff986c7d4b3a258aca5d16fd` reproduces the exact module bytes and only adds its umbrella import.
- The author's exact-source final check `results/lean_006.json` has exit code 0 and empty output, with matching before/after source hashes. This is checked retained evidence; root owns the independent fresh full project closure build.

[EXECUTED review harness correction] The first local checker attempt passed the newline-terminated recorded Git revision to `git show`, which refused the object name before patch replay. Stripping that record's trailing whitespace repaired the review harness; the successful rerun is the retained result. No target bytes changed.

[DERIVED maintenance] Safe integration wording is: “A generic structural validator now suffices for execution correctness of the existing Lean descriptor evaluator, and conditional EMA application theorems reuse the exact frozen circuit.” Keep concrete schedule validity, compiled artifact correspondence and runtime refinement graded separately until their own proofs are checked.
