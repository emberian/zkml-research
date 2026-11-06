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
  toolchain-mismatched check that never ran. Its stopping convention, which counts the alarming round,
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
| DL03 `bisect_localizes` | Isolated step validity is not monotone: two cancelling bad steps restore an honest endpoint. | ACCEPTED. Withdrawn. Bisection must test prefix validity (honest replay reaches the committed state), which costs a replay. |
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
