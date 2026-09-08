# Exact dynamics of the existing private-address EMA

[EXECUTED] This isolated Lean extension proves that six consistently labelled
updates to a selected bin suffice for the correct inference sign from every
state in the existing `Within120` invariant. Updates to other bins may be
interleaved. An arbitrary earlier history of allowed labels is also permitted;
the final segment must contain at least six updates to this particular bin,
all with the same label. The result reuses `PrivateAddressEma.candidate`,
`learn`, `history`, and `infer`; it introduces no replacement learner.

[EXECUTED] `Theory/PrivateEmaDynamics.lean:32` declares the keystone before its
proof. `six_consistent_sign` at line 160 proves it, and
`consistent_suffix_sign` at line 177 handles arbitrary allowed earlier
observations. `history_target_subsequence` at line 122 identifies the selected
cell with exactly the iteration of its own observations. Consequently, the
count is per selected bin, not per public route or elapsed time.

[EXECUTED] The checked consequences are:

| Property | Exact statement and source |
| --- | --- |
| Six updates suffice | Worst endpoints become +11 and -14 after six opposite-sign labels; `six_positive_endpoint`, line 84, and `six_negative_endpoint`, line 87. Monotonicity and sign preservation give all later consistent counts. |
| Five do not suffice | Starting at -120 with five +120 labels leaves -4; starting at +120 with five -120 labels leaves +2. Actual inference counterexamples are in `five_inference_falsifiers`, line 219. |
| Untargeted retention | Any cell never addressed by a history retains exactly its original byte, with no label restriction; `untargeted_retention`, line 144. |
| Floor residual | For the existing byte candidate, the integer residual `8*candidate.toInt - (7*s.toInt + u.toInt)` lies in [-7,0]; `floor_residual`, line 210. |
| Fixed-point asymmetry | Within [-120,120], +120 labels have fixed points 113 through 120, while -120 has only -120; `fixed_points`, line 185. From zero, 25 identical labels reach fixed points +113 and -120; `asymmetric_fixed_points`, line 227. |

[EXECUTED] Premise inhabitation is a theorem at line 234. The nonempty
`satisfying_subject` at line 248 learns a negative sign and retains another
cell. `interleaved_satisfying_subject` at line 254 gives a concrete 12-event
history with six observations each at two distinct bins and retention of a
third. The endpoint counterexamples, witnesses, and premise inhabitation use
kernel-checked decisions, not unproved assertions or external computation.

[EXECUTED] Verification is recorded in `results/verification.json` and the
final `results/lean_*.json` named there: 28 new declarations have exact
`#guard_msgs`-pinned `#print axioms`, with no admitted or custom axiom
declarations. Observed dependencies are subsets of Lean's standard
`propext`, `Classical.choice`, and `Quot.sound`. The frozen imported module's
28 pins are reused, not counted as new here. Failed development attempts remain
in `results/`; the final checked source is identified by its SHA-256.

[EXECUTED] Commands were `python3 research/learn_infer_only/formal/private_ema_dynamics/check.py`
and `python3 research/learn_infer_only/formal/private_ema_dynamics/package.py`.
Lean 4.30.0 and cached dependency oleans were used through the isolated `.build`
overlay. `results/environment.json` records paths and companion baseline;
`results/dependency.json` records compilation of the byte-exact dependency
copy. This is an isolated source check, not a clean dependency rebuild or a
whole-tree integration build. No companion source was edited, and its HEAD
and pre-existing dirty status were unchanged across packaging checks.

[EXECUTED] The proposed companion patch is
`minidregg-private-ema-dynamics.patch`. It requires the frozen
`private_address_ema` patch first. Fresh scratch application of both patches,
source-byte comparisons, and the companion import-boundary script passed.
`integration_entry.json` supplies the dependency and 28-pin count for root's
later integration; this lane did not modify shared integration registries.
`manifest.json` seals the local source, patch, scripts, and evidence.

[OPEN] These are consequences of the existing word-level BitVec semantic
specification. They do not supply a universal Rust/TFHE refinement theorem,
cryptographic privacy, a utility improvement, or removal of the full client
key. The separate encrypted successor stopped at a complete-byte replay
mismatch and was not privately drained. This proof does not resolve that
failure or establish that its decrypted semantics failed. Public routing of
the two four-bin states remains an explicit implementation limit.

[EXECUTED] This formal tranche used zero web, Scry, model, or cryptographic
calls. The separate pure finite dynamics calculation is retained in
`../../experiments/end_to_end/private_ema/encrypted_successor/analysis/`.
