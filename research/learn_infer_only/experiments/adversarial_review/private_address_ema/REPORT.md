# Independent review of the frozen private-address EMA theorem

[DERIVED / decision] **Accept the frozen first patch for its stated word arithmetic, address-selection, invariant, and conditional ripple-trace claims.** No mathematical or source-level mismatch was found in the reviewed scope. The proof does not establish that the actual Rust array loop realizes the relational trace, or that serialization/execution preserves the words being proved about. The emitted-schedule successor was not reviewed.

[EXECUTED / fixed target] The assigned source SHA256 `0b148bff8a53447bc9f30950948771a4b0f53edeb1110cc78f44e85a960d562d` and patch SHA256 `9fabd5d64ab3280dde1bbb1affab9ced9d5835f248f984dd4bb9d0488622ebae` match. The original runtime library matches its recorded SHA256 `fad1864642ff6c0036cdfed66b93bc7e21bb2720572d0ddd30b6effa2c65c880`. See `source_manifest.json`. All source references below concern these frozen files.

## Exact source correspondence

[SOURCE / proof and implementation] Lean references are to `research/learn_infer_only/formal/private_address_ema/Theory/PrivateAddressEma.lean`; Rust references are to `research/learn_infer_only/experiments/end_to_end/private_ema/src/lib.rs`.

| Property | Lean declaration / location | Original Rust location | Review |
| --- | --- | --- | --- |
| Eleven-bit numerator | `numerator`:30; `numerator_eq`:115; `numerator_exact`:129 | `candidate`:82–96 | [DERIVED] Matches the source's sign-extension, complement-plus-one and two modular additions. |
| Shift representation | `eight_s_encoding`:96 | Low zero bits followed by the original byte:90–92 | [DERIVED] The LSB-first array represents `s ++ 0₃`, equal to the eleven-bit shifted sign-extension. |
| Signed floor extraction | `extract_signed_floor`:108; `candidate_exact`:142 | `numerator[3..]`:97 | [DERIVED] High eight bits give floor division for every signed eleven-bit word. |
| Selected register | `selected`:38; `selected_exact`:146; `learn_selected`:149 | Public bin loop and address conjunction:108–116 | [DERIVED] The low address bit is first; exactly the public bin equal to the encoded address is selected. |
| Unselected registers | `learn_untouched`:153; `infer_untouched`:236 | MUX `(select,new,old)`:115–116 | [DERIVED] The word specification preserves every other register. |
| Sign inference | `infer`:45; `infer_selected`:157; `infer_negative`:163 | Three MUX calls:127–129 | [DERIVED] Selects bits 7,15,23,31 in address order; output is true exactly for a negative selected word. |
| Ripple arithmetic | `RippleTrace`:68; `full_adder_identity`:183; `ripple_correctness`:188; `ripple_bitvec`:207 | `add`:64–79 | [DERIVED] The local Boolean equations match. Their realization by the Rust loop is still an unproved bridge. |

[SOURCE / API argument order] In the installed pinned TFHE 1.6.3 source, `/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/tfhe-1.6.3/src/boolean/server_key/mod.rs`:147–154 names MUX arguments `ct_condition`, `ct_then`, `ct_else` and forwards them in that order. Only this source interface was inspected; no cryptographic correctness claim or experiment was made.

## Width and signed arithmetic

[DERIVED] Every eight-bit signed input lies in `[-128,127]`. Thus `7s` lies in `[-896,889]`, and `7s+u` lies in `[-1024,1016]`. Eleven signed bits represent `[-1024,1023]`, so both intended signed values are representable, including the exact minimum. The source uses eleven-bit modular addition; the range proof justifies interpreting the final modular numerator as the intended integer. A ten-bit signed interpretation cannot do this at the minimum.

[DERIVED] The raw byte placed above three low zero bits correctly represents `8s` modulo 2048 even when `s` is negative. The theorem `eight_s_encoding` addresses precisely the apparent distinction between appending the original byte and shifting a sign-extended word. Negating the sign-extended `s` through complement-plus-one then yields the intended `7s` modulo 2048.

[DERIVED] `extract_signed_floor` quantifies over **all** `BitVec 11` values, independent of numerator reachability. If the word is nonnegative, high-bit extraction is ordinary integer division by eight. For a negative word, subtracting 2048 before division differs from the unsigned quotient by 256, exactly the signed interpretation of the extracted byte. Lean's integer division is floor division here; Rust does not invoke signed `/`, because the implementation takes a bit slice.

[EXECUTED / independent finite mathematics] `review.py` checked all 65,536 signed-byte `(s,u)` pairs against the source-shaped modular arithmetic and an independent integer-floor expression, all 2,048 possible eleven-bit extractions, all 16 address/bin combinations, and all 64 four-sign-pattern/query combinations. It also checked the eight full-adder truth-table rows and 482 invariant state/endpoint-label pairs. Every check passed; numerical ranges, cases, and witnesses are saved in `results.json` and `review.stdout.txt`. These are mathematical checks, not execution of the Rust library.

## Ripple relation and its open realization

[SOURCE / proof] `RippleTrace n a b out carry` contains exactly the local XOR/AND full-adder equations for `i < n`. It does not assume the desired word sum. `full_adder_identity` exhausts the Boolean cases in the Lean kernel. Induction in `ripple_correctness` proves weighted-bit conservation, including `2^n * carry(n)` on the output side and `carry(0)` on the input side. `ripple_modular` and `ripple_bitvec` derive modular addition from that conservation equation.

[DERIVED] The XOR used for the carry is correct because `x && y` and `(x XOR y) && carry` cannot both hold. The first call in `candidate` supplies an initial carry of true, implementing the `+1`; the second supplies false. Keeping `carry(0)` explicit in the relational theorem is therefore necessary. Discarding the final carry is correct for modular addition; `carry_falsifier` proves that it is not unbounded integer addition.

[OPEN / specific bridge] The frozen module contains no theorem showing that the arrays returned by the actual `lib.rs:add` loop, together with its intermediate carry values, satisfy `RippleTrace`. The relation has an all-zero inhabitation witness, but no general theorem constructs or extracts the trace for every runtime input and initial carry. This is an honest conditional lemma, not a finished Rust refinement proof.

[OPEN / composition] Applying `ripple_bitvec` to `candidate` still requires the following concrete joins: define the LSB-first array/word relation; show equal-length `zip` visits exactly the intended indices; establish initial carry true/false and per-step carry order; connect the sign-extension and prefix/slice operations to the standard `BitVec` operations; and connect flattened state slices and the learn/infer MUX results to `State`. `private_address_correctness`:167 uses the BitVec proofs and does not invoke `ripple_bitvec`. There is consequently no hidden completed bridge in the headline theorem's proof.

## Premises, witnesses, and falsifiers

[SOURCE / proved statement] `PrivateAddressCorrectness`:50 quantifies over arbitrary four-register states, both two-bit addresses, and every signed byte label. Word typing supplies the bounds; it has no external correctness premise. Its components force the selected update, preservation of all other registers, and inference on the updated state. `selected_unique`:233 rules out no-selection or multiple-selection behavior in this word specification.

[SOURCE / invariant] `Within120` is the **inclusive** interval `[-120,120]` for every register; `AllowedLabel` is exactly `-120` or `120`. `invariant_correctness`:172 preserves this invariant, and `history_invariant`:246 covers every finite history satisfying `AllowedHistory`. The closure proof is sufficient for the stated premises; it does not claim those premises are enforced on arbitrary host inputs.

[SOURCE / input-premise realization] The original honest issuer enforces the endpoint labels at `src/bin/issuer.rs`:23 and packs address bits before label bits at lines 24–25. The original host's `read_bits` calls enforce vector shape, and `lib.rs:100–103` checks lengths. No theorem in this frozen Lean module connects those reads to `AllowedLabel`. The main full-byte update theorem still covers other byte labels; the strict subrange invariant needs its stated premise.

[EXECUTED / premise sensitivity] A cleartext mathematical counterexample to dropping the label premise is `s=-120, u=-128`, whose next value is `-121`. This is outside `Within120`; it is recorded in `results.json`. It is not a host or cryptographic experiment.

[SOURCE / nonvacuity] `premises_inhabited`:258 uses zero state, address three, and label 120, producing a changed selected register with value 15. `satisfying_subject`:267 uses zero state and label -120 at address three, producing -15, preserving the other registers, and returning a true negative-sign result. Thus the positive proof is not supported only by a no-op subject. `ripple_premises_inhabited`:215 supplies a trace at every width, and `carry_falsifier`:221 supplies a nonzero-carry case.

[SOURCE / teeth] The actual pinned truncation witness is `(s,u)=(1,-8)`: floor gives -1 while truncation gives zero. The ten-bit witness is `(-128,-128)`: numerator -1024 narrows to zero, while the correct byte output is -128. The address tooth updates address three and observes register zero: the specified register remains zero while unconditional EMA would produce 15. These falsifiers refute concrete broken alternatives. The header's additional example `(15,-120)` is also a valid floor/truncation separation, but is not the chosen `truncation_falsifier` witness.

## Verification and execution boundary

[EXECUTED] A fresh isolated checkout `/tmp/minidregg-ema-review-20260908` applied the frozen patch without changing companion sources. Patch/source bytes match the assigned hash. `lake env lean Theory/PrivateAddressEma.lean` exited zero with empty stdout/stderr; see `lean_replay.json`. All 28 exact axiom dependency guards passed, modulo their declared whitespace normalization. The independent theorem/pin census matches all 28 names in declaration order. No `sorry`, `axiom`, `opaque`, or `native_decide` proof construct was found by the recorded source scan. The import-boundary script also exited zero; see `patch_application.json`.

[OPEN / serialization and execution TCB] `lib.rs:27–51` checks/enforces marker, kind, payload length, expected vector length, canonical reserialization, and a data-variant restriction. Those checks do not appear in the Lean theorem. Rust/LLVM behavior, array slicing/iteration, the Boolean gate interface's correctness, bincode/file conversion, stable read-time input bytes, and the host's invocation of the intended code remain outside this proof. Source inspection supports the intended mapping; kernel checking does not certify these runtime components.

[EXECUTED / review boundary] No Rust binary, TFHE operation, ciphertext, key, malformed-input case, crypto workload, or emitted successor was executed or inspected as data. The reviewer ran source/hash checks, finite cleartext mathematics, patch application, the import script, and a single-file Lean replay. Web/Kagi/Scry counts are zero. Frozen author files and the polynomial-kernel package remain unchanged. Whole-tree integration belongs to root.
