# Mixed window/journal history

[EXECUTED] Two new Assurance modules compile with23 exact axiom pins. Patch: `formal/durable_integration/window_frame/minidregg-window-frame.patch`, SHA256 `0bc70c1db6bc0d6c205cca88ce65c77dd9538af6364096211dd3dada32fda992`. Frozen window44 source/patch bytes remain unchanged. This is a semantic proof adapter, not an implementation or authentication theorem.

| New source under `formal/durable_integration/window_frame/` | SHA256 | Pins |
|---|---|---:|
| `Assurance/CiphertextWindowFrame.lean` | `ba0e26b70c5a52365e9f5bd260c9a30ac3568df507e487598185625fc25132d0` | 9 |
| `Assurance/CiphertextWindowFrameWitness.lean` | `629ef9054f66a365ee10fc54236f9b11cfba5b8fcc50127e14eceb3386f543bd` | 14 |

[DERIVED] `admissionProjection` filters the **actual recorded replay intents** under one fixed classifier, retaining journal order. `admissionCount` is the projection length, not independently mutable state. `projection_install`, `count_admission` and `count_frame` identify exactly how a real DataSnapshot installation changes this count. Global journal length may advance on every transaction while this per-window count advances only on classified admissions.

[DERIVED] `frameCheck` uses the existing `DataSnapshot.lookupPostBytes` on the proposed writes. It allows an absent write or a same-cell no-op whose exact canonical post bytes equal current bytes. `frameCheck_iff` equates acceptance with actual installed-byte preservation. `framesSelected` checks both selected window and genesis cells. No root-injectivity assumption is used. Full DataIntent preflight, transaction freshness and semantic framing are separate obligations.

[DERIVED] `MixedHistory` has three constructors: initial canonical empty window/empty journal and selected genesis; an actual checked window admission using the existing WindowPlan/preflight/current full prefix; or an actual preflight-ready non-admission that frames selected bytes. `mixed_invariant` proves for arbitrary finite interleavings in this relation that installed bytes encode the same logical window, genesis bytes remain selected, the logical next-admission id equals the actual admission projection length, and the original queue-sum/bound/provenance invariant holds. `mixed_queue_sum` exposes the HE-facing algebra conclusion without asserting that every authority revision is a learning step.

[DERIVED, routing scope] The supplied concrete `windowAdmission` inspects the actual replay envelope: versioned resident event, a write to the selected state cell, selected genesis and program2/version1 in the existing context encoding. It also requires decode/re-encode equality. This is a fixed routing discriminator, **not** cryptographic authentication or proof of valid admission. A learn edge still requires the real window checker and exact canonical materialization/openings. A frame edge still requires installed-byte preservation. A forged label alone supplies neither. Dispatch/classification must stay fixed across the history.

[EXECUTED] The witness reuses the frozen nonzero `ZMod17` two-component ciphertext group and real `planFor`. It executes:

1. Admit `(3,5)` through the original p0 DataIntent.
2. A same-window canonical no-op with an infer-style program3 event, its own consumed nonce and nonzero charge.
3. Admit `(7,1)` with the actual full journal prefix containing that no-op.
4. Commit an unrelated cell transaction with its own nonce/charge.
5. Admit `(2,6)`, expiring the exact original `(3,5)` entry.

[EXECUTED] `actual_five_executes` proves all five results through the existing full preflight/fresh execute path. `mixed_subject_history` inhabits the mixed relation. `mixed_subject` has total authority journal length5 but admission count3, surviving entry ids `[1,2]`, and accumulator `(7,1)+(2,6)`. The actual projected transaction ids are `[504,502,401]`, while the complete newest-first journal ids are `[504,503,502,501,401]`. `exact_retry_after_interleaved_expiry` returns the exact existing recorded intent without another expiry. The proof does not introduce another store executor or an independent model counter.

[REFUTED: frame by root or label alone] `dishonestFrame` is a real preflight-ready DataIntent with the same constant root and an infer-style non-admission tag, but different canonical window bytes. The frame check refuses it, and no mixed history can pair its installed bytes with the old logical state. `falseGenesisFrame` leaves window bytes intact but changes selected genesis bytes under the same constant root; it is also refused. Both demonstrate why the byte frame condition is load-bearing.

[REFUTED: permissive decoding assigns a canonical admission tag] The byte-level alias witness inserts a redundant high zero in the base255 list-length prefix. Existing natural decoding accepts the same context, but the new concrete classifier refuses its noncanonical encoding. Generic `noncanonical_tag_refused` states that boundary. This neither changes the existing codec law nor claims all raw decoder inputs were canonical.

[OPEN] Validity in this relation means the stated typed DataIntent, preflight/freshness, exact selected-byte framing or checked window transition. It does not grant authority over other cells, prove an inference output correct, enforce recipient/output policy, authenticate observation origin, establish hidden input range or add a noise theorem. Those deployment/controller obligations remain separate. The infer-style event in the witness is a genuine durable no-op, not a BFV inference implementation. The new E2E journal is responsible for actual authorized encrypted inference and its global-revision/admission distinction. Physical persistence and uncompacted full-post replay-storage costs are unchanged.

[EXECUTED] Reproduction from `/Users/ember/dev/zkml-research`:

```sh
python3 research/learn_infer_only/experiments/durable_integration/window_frame/check.py Assurance/CiphertextWindowFrame.lean Assurance/CiphertextWindowFrameWitness.lean
python3 research/learn_infer_only/experiments/durable_integration/window_frame/review.py
```

[EXECUTED] `review_01.json`/`review.json` pins both source/olean identities, all23 theorem pins, direct import dependencies, a red-tested forbidden-token scan over exactly these two files, successful staged Assurance umbrella check, read-only apply check, actual patch apply/content comparison and the real import-boundary script on copied full Theory/Selvage sources. All pins are subsets of `propext`, `Classical.choice`, `Quot.sound`; no custom axiom is introduced. Dependency oleans are reused; this is not a clean whole-tree rebuild. Prerequisites are the original resident-release, first durable-integration and window44 patches. Earlier elaboration failures remain in numbered logs. No companion writes, commits or queries; Scry0/web0.
