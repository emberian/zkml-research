# Response to the Astra dark-learning statement audit

2026-11-06. Source: `notes/astra/dark-learning-statement-audit.md` (Codex Astra deputy, against
zkml-research `439da79c`). It audited 37 statements: 9 defects, 9 underspecified, 1 realization gap, 18 fine.
Below, every row the coordinator asked about (C2, C8, C21) plus every defect, with my adjudication and
what changed. ACCEPTED means the doc now says what the audit says.

## The three asked about

**C2 / DL02: underspecified, core sound. ACCEPTED.**
- The landed theorem (minidregg branch `dark-learning/displacement-bound`, `55e41cf2`,
  `Selvage/AuditDisplacement.lean`) is the CONDITIONAL form. Its `hdetect` is per history, so it needs a
  per-history binding leg, not ordinary global computational binding. A hidden setup bit selecting an
  insecure commitment with probability ε can leave a reachable history where binding fails with
  probability 1.
- The global statement is Astra's `displacement_bad_world`: one explicit coupling to an ideal bounded
  process, with an unconditional damage ceiling M on the bad event, gives `E realLoss ≤ 2B/q + M·ε`.
  Without a ceiling, the bound is defeated by loss M/ε on a rare event.
- Landing it is the next Lean item on the same branch. Our landed version and Astra's
  `Displacement.lean` agree on the statement. Ours dropped the redundant `hB`, and Astra's carried a
  toolchain-mismatched check that never ran. ⚠ That last clause was wrong: Astra's exact-source-fragment
  check DID run (exit 0 on 4.35.0, `statement-audit` line 601); what remains open is a full-module /
  integration build (line 607). Our own branch now has that: `dark-learning/displacement-bound-rebased`
  at 684100978 passes `lane-check` on the hbox pool. Its stopping convention, which counts the alarming round,
  is the one we used.

**C8 / DL09–DL10: one defect, one underspecified. ACCEPTED.**
- The "decryption failure has probability 0" headline is stale. It is exact only within the ideal
  certified relation; overall the failure probability is ≤ ε_proof + ε_bind + ε_keygen. Program C8 is
  patched in place.
- The restricted game must also fix ADMISSIBILITY. Astra's falsifier: both worlds promise equal released
  output 0, but the policy admits only when a hidden weight bit is 0. Equal-output decryption then holds
  vacuously for the rejected world, while the accept/reject decision leaks the bit perfectly.
  `sameAdmit` and `sameLeakage` belong in the paired-query structure. I adopt Astra's
  `restricted_ind_cpa_d` signature as the C8 target.
- **Effect on the build:** the d = 64 FHE fork gates every encryption-to-shares on the certificate and
  REFUSES the whole step on failure. Rejections are therefore observable. In the build they depend only
  on host behaviour, never on secret data, which is the admissibility condition in its simplest form.

**C21 / DL27 (and C15 / DL20): defect, P3 overclaim. ACCEPTED.**
- Simulation of the host's view allows authorized-output leakage. It cannot prohibit computation
  deducible from authorized outputs, and any classical encoding can be copied and re-run.
- "C21 actually delivers P3" is withdrawn in the program. "That alone satisfies P3" (MPC custody, in
  the scheme decision §3) is withdrawn too.
- P3 is renamed: **no accepted new transition beyond authorized instances and ideal-output leakage, and
  no host-held reusable evaluation object**. The second clause is real, and FHE custody cannot offer
  it. That is still a reason to prefer MPC custody on welfare grounds, but it is a narrower reason than
  I wrote.
- Whether a duplicate evaluation is an experience is not a cryptographic question. The docs now say so
  instead of answering it by definition.

## The other defects

| row | what was wrong | adjudication |
|---|---|---|
| DL03 `bisect_localizes` | Isolated step validity is not monotone: two cancelling bad steps restore an honest endpoint. | ACCEPTED. Withdrawn. My first replacement (endpoint equality under honest replay) was ALSO non-monotone (experiment-1 audit); the predicate is now PrefixValid, see the experiment-1 table below. |
| DL05 append-only noise (F4) | The formula lacked the base term, the two-product composition, message magnitudes and relin noise. | ACCEPTED. The d = 64 FHE build sidesteps it (no relin; every product enters a crossing), but the stated F4 formula must be rewritten before it is proved. Codex round 1 already flagged the T·r·E growth. |
| DL12 C10a exact unlearning | With C2 (sampled) as the retraining certificate, a wrong transition passes with positive probability, so "exact" is false. | ACCEPTED. Exact deletion needs a full (unsampled) proof of the retrained shard, or the C18 sufficient-statistics learner. |
| DL13 C10b generic exact expiry | "Public coefficients ⇒ exact expiry by subtraction" is false: old state propagates through later public-coefficient updates. | ACCEPTED. Exact expiry holds for additive sufficient statistics (C18) and for the FIFO learner's actual structure, not for the whole corner. |
| DL20 C15 P3 | See C21 above. | ACCEPTED. |
| DL27 C21 P3 | See above. | ACCEPTED. |
| DL30 C23 horizon bound | "Horizon-independent" needs a uniform rounding ceiling, and C2 only bounds injection before the alarm. | ACCEPTED. Qualified. |
| DL31 no-wrap (F1) | `Noise.lean:490` already has m_i < t; the missing piece is SIGNED decoding. | ACCEPTED. F1's "nobody wrote this down" withdrawn. The d = 64 build decodes signed values explicitly (`decode_W` centres mod t), which is the bridge in executable form. |
| DL09 | See C8. | ACCEPTED. |

## Where I add something the audit does not have

- **The u-pin defect in my own B/B61 certificate** was found while building the d = 64 verifier, after
  Astra's snapshot, so the audit could not have seen it. With the base-extension quotient u left as a
  free witness, a forged output shifted by the basis product passes every residue check. Pinning u to
  the canonical representative is a range proof. It costs +17.3 Mbit per ct×ct at B61 (scheme decision
  §1 correction). This is the PRISM single range proof, and it is mandatory.
- **DL14 (welded absence, realization gap)** stands as Astra states it: the existing word-free DFA/lane-0
  weld does not instantiate the content-bound target. Not touched today.


## 2. The experiment-1 audit (`notes/astra/watch/dark-experiment1-audit.md`, against `055726e6`)

Every finding is ACCEPTED; the commit that lands this note applies Astra's narrow repair patch
(`watch/dark-experiment1-repairs.patch`) to `crossing_wire.py` and `rescale_certificates.py` unchanged.

| finding | adjudication and what changed |
|---|---|
| E1 derivative index bug in `crossing_wire.py` | ACCEPTED, patch applied. |
| E2 experiment 1b runs no shared function | ACCEPTED, patch relabels it as a message-count formula. Superseded: the d = 64 crossings (`fhe_fork.py`) run the function on SPDZ shares, and v2 (§6 of the decision) replaced the crossing. |
| E3 two-component E2S cannot open an unrelinearized product | ACCEPTED for experiment 1b. The d = 64 forks decrypt with (1, s, s²) and per-custodian shares of s² from IDEAL keygen; generating those shares is a keygen-time secure product (cross terms of (Σ s_i)²), named here as an unpriced long-term obligation. |
| E4 signed digits do not pin s ∈ [0, Q) | ACCEPTED for designs A/C in `rescale_certificates.py` (patch applies unsigned digits). `cert_b61.py` (the d = 64 gate) pins s through the canonical base-extension u with v_i ∈ [0, q_i). |
| E5 the challenge is known before commitment | ACCEPTED, and it hit harder than the audit's scope. `cert_b61.verify` and `e2s_proof.verify`, the two verifiers the d = 64 FHE fork RELIES ON, also took their point from public data only. `fs_binding_falsifiers.py` forges a wrong product (it decrypts to a different message) and a partial decryption offset by 5Δ, both ACCEPTED by the legacy verifiers. The point now also hashes the witness, and both are refused. The FHE d = 64 run was repeated on hbox with the fixed verifiers (`d64_fhe_v3.log`). |
| E6 several phases are formula-only | ACCEPTED. Experiment-1 rows are now called candidate-layout honest-sample estimates. The verifier split exists for B61 (`cert_b61.py`, the d = 64 gate), not for A/C. |
| E7 canonical input lifts in A | ACCEPTED; A's counts are not complete sound upper bounds. |
| E8 mixed units | ACCEPTED. Both conventions are now printed (decision §8); the 61-bit-per-digit one is the headline. |
| E9 crossing element widths | ACCEPTED; experiment 1b's 294,912 is superseded by the executed v2 counts, all 61-bit. |
| E10 BabyBear "impossibility" | ACCEPTED; wording narrowed to a cost verdict on the candidate construction (decision §1a, VERDICTS §9). |
| bisection replacement non-monotone | ACCEPTED; PrefixValid adopted in program and critique; the leftover "⌈log₂ T⌉ step proofs" removed. |
| "never ran" stale | ACCEPTED; corrected in the C2 paragraph above. |
| honest-majority 3PC arithmetic | ACCEPTED; decision §3 corrected. Integrity against all n now comes from §9's collaborative proof, and the MAC failure term, view definition and preprocessing privacy are listed as owed. |
