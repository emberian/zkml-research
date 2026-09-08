# Review: deterministic supplied-opening checkpoint adapter

[DERIVED verdict, 2026-09-08] **Accept the frozen 20-theorem package within its deterministic finite-log scope.** The conclusion concerns the actual supplied BinaryMerkle value/path and the word extracted from its fixed prefix. The executable `Bad` event is finite, and the new `Far_E` refers to that word. No blocking correctness finding remains. This review supplies no probability bound, computational binding, protocol timing, Fiat–Shamir, QROM, or implementation refinement.

[SOURCE freeze] Reviewed [author README](../efficient_root_opening/README.md) and [source](../efficient_root_opening/src/Selvage/EfficientRootOpening.lean). Frozen identities:

| Artifact | SHA256 |
| --- | --- |
| Author `manifest.json` | `9b18d46259b37570d073999589ed06daee9e1cbbe57dbed232c2dc8c24a9b7ef` |
| `Selvage/EfficientRootOpening.lean` | `defd19242e66118333d477cd14bcb1b108c4d517b1e55861dee66f35647dafe6` |
| `efficient-root-opening.patch` | `c1d7aebabd8d755192d38c3628b266e1351a3703b03fa66f0dd042fef645d5b2` |

## Exact subject and finite condition

[SOURCE / DERIVED] `Query` distinguishes semantic leaf values from ordered node inputs. `Log` aliases the existing `OracleLog`; `preimage` is a computable first reverse lookup. `preimage_eq_answerOf` at line 125 proves equality with the existing first-answer lookup after swapping cells. The implementation does not call `Classical.choose` or enumerate possible digest preimages. The imported noncomputable `OracleLog.answerOf` is used in that equality proof, not as the new lookup implementation.

[SOURCE / DERIVED] `pathLog` uses the actual `BinaryMerkle.recompute` result for each child; `openingLog` records the supplied value's leaf and those ordered node records. `word` uses the same `binaryAddressBits k i` as `BinaryMerkle.openingScheme.verifyOpen`. Both therefore share the existing LSB-first address interpretation and exact path-length convention. A missing reverse lookup or wrong query constructor returns the fixed public default.

[SOURCE] `SuppliedOpeningSound` at line 96 states the contract before proof work. For explicit `P`, `middle`, default, depth, root, index, value and path, its premises are:

1. `¬Bad P (P ++ middle ++ openingLog H v (binaryAddressBits k i) path) root`.
2. The existing `BinaryMerkle.openingScheme H k` accepts that very `root,i,v,path`.

Its conclusion is `v = word P default k root i`. The supplied witness is retained throughout; no existential alternative opening, global perfect binding, or honest-root-image premise is substituted.

[SOURCE / DERIVED] `Bad` is exactly a disjunction of (a) two entries in the final finite log with equal responses and different typed queries, and (b) an entry in that log absent from `P` whose response equals the root or a child digest of a node entry in `P`. `badCheck_eq_true_iff` proves the nested finite Boolean tests decide this predicate with decidable value/digest equality. Duplicate identical cells are not collisions and do not become late entries merely because they occur again. Cross-type response collisions are included.

[DERIVED] The induction in `extractedAt_eq_of_logged` is sound. The accepted path supplies its final node record. If that record were absent from the checkpoint it would hit the fixed root target, contradicting `¬Bad`. Absence of response collisions makes its reverse lookup unique. Its selected child is now a checkpoint target, so the same argument applies down the actual path, ending at the supplied leaf record. The depth-zero case explicitly handles the leaf and rejects a nonempty path. `suppliedOpeningSound` at line 223 supplies the required containment facts from the literal concatenated log.

[DERIVED boundary] The deterministic theorem even permits arbitrary or inconsistent prefix/middle lists; its implication does not require a probability distribution or an oracle-consistency premise. That strength does not certify such lists as actual runtime histories. Any probabilistic application must separately generate a faithful shared-oracle log, account for its queries, and prove that the checkpoint and root precede the relevant challenges. This package does not identify its `Bad` with the earlier semantic `BadRoots`, or with an already priced fresh-query event.

## Witnesses, farness and costs

[SOURCE / DERIVED] `Far_E` at line 69 is `¬close radius C (word P default k root)`, using the existing `close` definition. It is a new mathematical farness event; it is not an executable farness test or the old canonical-choice event. The field-five witness extracts `(0,1)` at depth one, with an actually accepted opening of value one and `Bad` absent. Its distance from the zero submodule is `1/2`, exceeding radius `2/5`; `all_premises_inhabited` conjoins farness, actual acceptance and the good-log condition. This inhabits the stated generic contract, not a PCS-to-Reed–Solomon farness reduction or the full BabyBear experiment.

| Witness/falsifier | What it establishes |
| --- | --- |
| `adapter_inhabited` | Fires the named soundness theorem on an actual accepted depth-one opening. |
| `late_root_falsifier` | An empty checkpoint cannot resolve a later accepted leaf opening merely because the final root matches. |
| `response_collision_falsifier` | Two recorded leaf values with one response can disagree with first lookup even when there is no late target. |
| `child_target_falsifier` | A previously recorded root query is insufficient when its selected leaf response is missing; no response collision or late root exists, but the late child causes the mismatch. |
| `full_log_is_not_prefix` | Replacing the checkpoint with the later verification log can change the extracted word. |

[SOURCE / DERIVED] The child-target falsifier was added during review and is included in the final guarded freeze. It isolates the root/child distinction: `P=[(node 10 11,2011)]`, while an opening of value one at index one with sibling ten accepts at root 2011. The root record is old, but leaf response 11 is a late child target, and checkpoint extraction returns default zero.

[DERIVED cost boundary] `openingLog_length_of_accepted` proves exactly `k+1` **recorded entries** for an accepted depth-`k` opening. It does not count execution work of the log constructor. `pathLog` recomputes child suffixes, so a direct evaluation may repeat hash-function applications. The final README now makes this distinction explicit. Nor is the finite `badCheck` a proved runtime/resource bound: it compares pairs and performs membership scans. No oracle query advantage or security bits follow from these length facts.

## Independent controls and frozen evidence

[EXECUTED] [controls.py](controls.py) independently implements the finite tuple/log predicates and bounded BinaryMerkle recurrence. It checks all 64 two-value/two-digest hash tables, 157 arbitrary prefixes of length zero through two, zero or one intermediate recorded query, and every depth-zero/one opening and root: 1,406,720 cases. Of 703,360 accepted cases, 6,400 have `Bad` absent; none of those disagree with checkpoint extraction. All 351,680 mismatches flag `Bad`. [CONTROLS.json](CONTROLS.json) retains exact counts. This is finite falsifier search, not a new proof of the general theorem.

[EXECUTED / DERIVED] Separate controls confirm the child-target case, a cross-type response collision, and four malformed path lengths. A further control shows the acceptance premise matters: the good prefix extracting `(0,1)` still has `Bad` absent for the supplied value-zero/index-one/path-ten record, but its recomputed root is 2010 rather than 2011; dropping acceptance would permit the wrong conclusion. The extracted two-element word also gives the stated `1/2` zero-code distance directly.

[EXECUTED] [verify_packet.py](verify_packet.py) verified all 23 author artifact pins, four dependency source pins against both the companion and isolated copies, three prior audit/review pins, and the retained root-census script hash. Independently checked the 20 theorem names against all 20 exact guarded messages, the declaration list and integration census. All listed axioms are standard (`propext`, `Classical.choice`, `Quot.sound`); the new source contains no `sorry`, new `axiom`, `admit`, `native_decide`, `unsafe`, `noncomputable` definition or `Classical.choose` call.

[SOURCE / EXECUTED] The retained final check has exit zero, an empty output log, the exact final source hash and `source_unchanged=true`. The source is 412 lines. This review inspected that evidence and did not rerun Lean. The four named dependencies are `BinaryMerkle.lean`, `OracleLogExtraction.lean`, `BinaryLookup.lean`, and `CorrelatedAgreement.lean`; these pins are not a fresh build or complete attestation of the transitive cached dependency closure.

[EXECUTED] Independent `git apply --check` and patch replay in this review's temporary directory reproduced the exact source bytes. The patch adds only `Selvage/EfficientRootOpening.lean`; no existing proof body or umbrella file changes. The source imports only `Selvage.BinaryMerkle` and `Selvage.OracleLogExtraction`; the retained import-boundary check passed. [VERIFICATION.json](VERIFICATION.json) and [INPUTS.json](INPUTS.json) retain the verification details.

[DERIVED handoff] Root can select this deterministic seam for clean integration. Because the patch contains no umbrella import, explicitly wire it into any selected umbrella closure. Future work must connect faithful oracle execution, immutable checkpoint timing, actual supplied-proof acceptance across the protocol, and the new farness event before applying any probability theorem. Multiple roots, concrete typed-leaf/MMCS refinement and Fiat–Shamir/QROM remain outside this package.

[EXECUTED scope] Only this sibling review directory was written. No author, companion, shared-ledger or microsite edits; no new Lean build, Rust/crypto run, probability/FS extension, private/stopped-runtime access, publication or network search. External queries: zero web, zero Scry, zero Kagi. Earlier p3 review seal was checked against its eight saved artifact hashes only, with no rerun. All absence statements here concern the inspected module/patch and use the retained source scan; no broader absence claim is made.
