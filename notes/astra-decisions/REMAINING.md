# Other decisions and stale permission barriers

2026-11-06. Read-only review. Tags: [READ] inspected source; [INFERRED] recommendation or consequence. No builds, remote machine actions, or publication changes were made. This section supplements decisions 1–12; it is not a new backlog.

## 13. Which remaining choices need a policy, and which are already engineering work?

**Options.** Leave the handoff’s “ember” queue intact; accept every lane’s revised bar; or adopt specific claim boundaries and return already-authorized repairs to their owners.

**Recommendation [INFERRED].** Choose the third. Complete the content-binding and schema repairs without another approval cycle; publish only claims that describe what the accepted receipt actually establishes. Preserve the original end-to-end ambition while naming intermediate demonstrations precisely.

### A. Complete the binding changes; do not promote a log claim into an execution claim

[READ] `breadstuffs/docs/automata/HANDOFF.md:40` says Dyck gates, the table/weld routing chain, and public trace length are already approved. Current `metatheory/Dregg2/Circuit/Emit/AttestedAutomatonBound.lean:30–46` still gives a two-word/same-public-input falsifier and calls for all eight route lanes plus length. `DfaRoutingTableBound.lean:16–46` establishes a transition multiset/trail, not an arbitrary public word. Meanwhile, the row-opening-heap witness repair is present in the current weld theorem (`rowHeaps_nonempty`, line 215); that old blocker should not be blindly reassigned.

[INFERRED] Finish the approved route/length work and test it against a spliced word before calling these content-bound certificates. For streaming, keep the label “complete relative to this committed prefix.” An MMR proves that no position was removed from the committed log; it cannot show that every real event entered it. `breadstuffs/docs/stream/GROUNDING.md` §§1,3,5 already specifies genesis/checkpoint trust and finite-prefix liveness limits. Use “pending obligation” for unanswered prompts, never “liveness proved” on a finite run. Coupling the logger to the chokepoint is the higher rung, not a reason to discard the current receipt.

**Change my mind / wrong-cost.** An audited capture theorem and the deployed enforcement path would justify stronger non-omission language. Getting this boundary wrong makes a valid proof certify the wrong universe of events.

### B. Correct two “production findings” at their actual scope

[READ] The alleged production descriptor drift is inside `#[cfg(test)] mod tests` (`breadstuffs/circuit/src/lean_descriptor_air.rs:2065–2066`). `TRANSFER_VM_DESCRIPTOR_JSON` at line 7617 is explicitly a frozen IR-v1 parser fixture; lines 7628–7636 explain its historical 42 public inputs. All references found by `rg -n TRANSFER_VM_DESCRIPTOR_JSON` in that file are in this test module. However, the differential-test commentary at lines 7797–7802 still calls it byte-identical to the live Lean emit.

[INFERRED] Retain it as an explicitly historical parser fixture, correct that differential’s claim, and test the served descriptor separately against the generated artifact. Do not rotate a production verification key merely because a historical fixture differs. This does not establish that every production consumer is correct.

[READ] The schema discrepancy is real at source: `persist/src/lib.rs:958` is epoch 27; `docs/VK-REGEN-LOG.md`’s schema ledger ends at 26, while its header says the ledger remains live. The epoch-27 format is described at `persist/src/lib.rs:882–903`.

[INFERRED] Repair the ledger from the actual epoch-change commit and repair the stale self-test; then consolidate redundant checks only if the retained check rejects every existing failure fixture. This is maintenance, not a decision to bless an unknown state migration.

**Change my mind / wrong-cost.** A served path using the old literal would escalate it to a production defect. Misclassification either wastes a flag day or leaves the real consumer untested.

### C. Close the indexed-tree representation gap

[READ] `circuit/src/heap_root.rs:71,433–456` reserves address zero; the served weld test (`circuit/tests/weld8_served.rs:21–25`) consequently requires `step(0,0)=0`, unlike its dense Lean model.

[INFERRED] Use an explicit injective edge-address encoding that avoids sentinels, and prove the dense-to-indexed representation adapter. Price its lookup/range changes and rotate affected roots together. Restricting all automata to `step(0,0)=0` is a defensible temporary domain restriction, not the general interface I recommend.

**Change my mind / wrong-cost.** An existing canonical sink-state transformation with proved language preservation and cheaper deployed checks could replace the offset encoding. An unchecked remapping silently binds another automaton.

### D. Adopt the model-identity and deletion boundaries; keep aggregation topology explicit

[READ] `research/model_identity_receipt_2026_11_06/GROUNDING.md` §§2–4 separates checked integer conversion from unrecomputed GPU commitment construction and a demonstration eval signer. `notes/unlearning/GROUNDING.md` §3 distinguishes exact state replacement, approximate influence bounds, and irrevocable historical roots/releases; public content-key absence also enables guessing low-entropy records.

[INFERRED] Keep strict model identity fail-closed on the unrecomputed edge; call the signed eval illustrative until an evaluator actually runs that exact quantized node. For unlearning, certify “every copy removed from the current committed dataset and prescribed state recomputed,” not erased history or recalled outputs. Public demos should use public/synthetic records; a production deletion-key design must hide guessable content.

[READ] `notes/holography-accumulation-verdict.md` §5 exposes another genuine design choice: stateful aggregation versus stateless handoff. [INFERRED] Prototype stateful aggregation for one operator, but do not assume its private witness state can pass between mutually distrusting aggregators. Preserve that distributed requirement as a separate experiment. Keep the existing hbox automata checkout warm for scoped gates; deletion has no demonstrated benefit here and remains outside this run.

**Change my mind / wrong-cost.** A real evaluator, recomputed commitment, hiding deletion-key construction, or distributed-aggregator requirement changes the corresponding recommendation. The risk is overstating provenance/privacy or optimizing a topology the product cannot use.
