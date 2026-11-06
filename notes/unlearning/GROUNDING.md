# Initiative 16 grounding: unlearning / forgetting certificates (C18-C20)

Lane: initiative 16, opened 2026-11-06. Harness files `unlearn_*.py` go beside the dark-learning harness in
`/Users/ember/dev/zkml-research/research/dark_learning_2026_11_06/`; the note is
`/Users/ember/dev/zkml-research/docs/UNLEARNING-CERTIFICATES.md`; the Lean lands on the minidregg branch
`lane/unlearning-certs` under `Assurance/`, importing `Selvage/AuditDisplacement.lean` from minidregg main
(684100978). zkml-research has no `lean/` tree, and the displacement theorem the bar names is in minidregg, so the
Lean goes there.

## 1. What exists, and what it settles

| thing | where | what it gives this lane | kept / replaced |
|---|---|---|---|
| C10, C18, C19, C20 text and falsifiers | `docs/DARK-LEARNING-PROGRAM.md` §4 | the comparator ("the prescribed learner on D \ {d}"), Codex round 1's shard counterexample, the three C18 falsifiers (duplicate deleted once, φ changed after accumulation, singular or wrapped system), C19's capacity falsifier, C20's stale-parent falsifier | **kept** as the specification; status section appended there, nothing edited in place |
| Astra DL12, DL13 | `notes/dark-learning-astra-response.md` | exact deletion needs a FULL (unsampled) proof of the retrained part, or C18; "public coefficients imply exact expiry" is false in general | **taken as the bar**: no sampled audit is ever called exact here |
| harness discipline | `research/dark_learning_2026_11_06/` (`spdz.py` MACs and per-party stream commitments, `fs_binding_falsifiers.py`, `proofwire.py`'s Ledger) | every Fiat-Shamir point hashes the witness; the expected parent comes from the ledger, never from the blob; counts, not clocks | **reused**: the SPDZ engine is imported unmodified for the custodied variant; every random point in my checks hashes the witness; my ledger follows proofwire's rule |
| absence protocol | `whatember/sources/01-...md` §3, §5; breadstuffs `dregg-query/src/mmr.rs`, `MMR.lean` (`server_cannot_omit_position`, `rverifies_iff_exact`), `AttestedQuery.lean` | whole-log range opening with the length derived from the peak heights; Count = 0 over a whole-log coverage | **reused in structure** (same peaks, bagging and domain separation; SHA-256 in place of BLAKE3 to stay dependency-free like the harness; a Rust port uses `Blake3Mmr` directly) |
| displacement bound | minidregg `Selvage/AuditDisplacement.lean` (`Round.displacement_bound`, 2B/q) | the expected injected displacement before the first alarm under SAMPLED audits | **reused, for a different job than the bar says** (section 3) |
| C23 contraction | program §C23 | `dist(s', ŝ') ≤ ρ dist(s, ŝ) + injected + rounding` | **this is the SGD residual-influence bound**; built here in Lean for the deletion case |
| FIFO expiry learner | `research/vfhe_2026_09_08/` (C10b) | exact expiry for its own additive structure | read; not reused (its learner is FHE-side; C18 is the general form, per DL13) |

## 2. Prior art (Kagi, arXiv abstracts, ePrint, ~/paperbin grepped first: only Kaizen cites 2210.09126)

Exact deletion for a sufficient-statistics learner is old. **Cao and Yang (S&P 2015)** put learners in "summation
form" (statistical-query learning) and unlearn by subtracting a record's summands: that is C18's exactness, nine years
earlier. Ginart et al. (NeurIPS 2019) do k-means; Bourtoule et al. (SISA, S&P 2021) shard and retrain, which is C10a.
**Guo et al. (ICML 2020, 1911.03030)** define certified removal as (ε, δ)-indistinguishability from a never-trained
model, with a Newton step plus noise for L2-regularised linear models. That is a statistical guarantee about a
randomised mechanism; it is not checkable from a state either.

On verifiability: **Thudi, Jia, Shumailov, Papernot (USENIX Security 2022, 2110.11891)** show that approximate
unlearning ("close to a retrained model") is ill-defined, because the same model is reachable from different datasets,
so one can "unlearn" without changing the model; even for a given trajectory one cannot prove the absence of a point;
unlearning is auditable only at the algorithmic level. **Zhang et al. (ICML 2024, 2408.00929)** break both the
backdoor and the reproduction styles of verification. So output-only verification is out, and this lane makes no
output-only claim.

The constructions closest to ours: **Eisenhofer, Riepel, Chandrasekaran, Ghosh, Ohrimenko, Papernot (SaTML 2025,
2210.09126)**: a cryptographic definition of verifiable unlearning, SNARK proofs of training and of an "admissible"
unlearning function, and non-membership of d in the new dataset via hash chains, for linear and logistic regression
and small networks. Our design has the same three legs. **Weng et al. (TIFS 2024, 2210.11334)**, Proof of Unlearning
on SGX. **zkUnlearner (2509.07290)**, bit-masked proofs of SGD training with forgery resistance. **ZK-APEX
(2512.09953)**, ZK proofs of an approximate personalised unlearning transform. **FHorgEt (ePrint 2026/510)**: FHE plus
MPC training, inference and unlearning with confidentiality over the model's whole lifecycle; that is the prior art
for the custodied variant. Hardt, Recht, Singer (ICML 2016) is the non-expansiveness argument behind the SGD bound.
Naor and Teague (STOC 2001) name the property C18's state has: history independence.

**What is left for us is a narrowing and a composition, not a first:** (i) a Lean statement that the accepted
post-deletion state is the fold over the remaining multiset AND that the accepted release is the unique solution for
it, so "trained then deleted" and "never trained" are the same state (history independence, proved, rather than an
admissible-function abstraction); (ii) composed with the existing MMR absence protocol (whole-log Count = 0) so that
"delete d" means every copy; (iii) the SGD case stated as a contraction-discounted influence term plus the landed
displacement bound for what a sampled-audit host can re-inject, with teeth; (iv) a custodied variant whose deletion
is checkable by a stranger from linearly homomorphic commitments alone.

## 3. Corrections to the bar (I am a peer; these change what gets built)

1. **The displacement theorem does not bound a deleted datum's residual influence.** `displacement_bound` bounds the
   expected deviation a cheating host injects before a sampled audit alarms (2B/q). A datum's influence on later SGD
   iterates is a propagation question: it is bounded by non-expansiveness or contraction of the update map (C23,
   Hardt et al.), `‖w_T − w'_T‖ ≤ Σ_{t uses d} ρ^{T−1−t} γ_t`. The bar's `sgd_delete_bound` is therefore the SUM of
   two terms: the contraction-discounted influence of d (pathwise, deterministic) and the host's injection under
   sampled audits (in expectation, 2B/q, from the landed theorem). That is the statement built.
2. **Approximate deletion is not unlearning and the certificate says so.** "Doing nothing" satisfies the SGD bound
   whenever the bound is loose (Thudi et al.'s point, now as a theorem's consequence). The certificate's value is
   the number ε it carries; only exact replay of the suffix that used d (fully proved, DL12) is exact for SGD.
3. **Deletion is by content, every copy.** "Delete record i" leaves a duplicate's influence. The request names a
   content key; Count = 0 over the whole committed live set is what proves every copy went, and it is the leg that
   refuses the program's first C18 falsifier (a duplicate deleted once).
4. **The state must NOT distinguish "never trained on d" from "trained and deleted"; the log MUST.** The theorem is
   that the fold factors through the multiset, so the two states are equal. Accountability lives in the log (a
   tombstone leaf records that a deletion happened). Nothing here erases history: an old root with an old opening
   proves past membership forever, and old releases are not recalled (C13/C22 territory, stated, not solved).
5. **"Count of d's content pattern" is over the content key here.** An exact-content pattern needs no automaton: the
   verifier compares leaf keys. A regular pattern over record bytes needs the DFA leg of dossier 01 (step 2-3); that
   is out of this lane's scope and said so. A publicly checkable Count(c) = 0 is also a public membership oracle for
   c: the key is a hash of the record, so a guessable record is guessable from the log. Stated as a limit.
6. **"Checkable by a stranger from the commitments alone"** means: host-visible variant, the stranger replays the
   certified event chain from genesis (every insert and delete certificate, O(d² + log n) each); custodied variant,
   deletion is checked by commitment arithmetic (Pedersen over a 2048-bit MODP group: binding is discrete-log, so NOT
   post-quantum; a lattice commitment is the PQ replacement and is priced, not built). A release FROM custody needs the
   gen-3 lane's collaborative proof; that is a composition point, not claimed.
7. **C19 is exact only in its sufficient-statistics instance with a data-independent subspace.** The program's C19
   is an SGD adapter core; exact deletion holds for the projected least-squares learner (statistics Uᵀ A U, Uᵀ B)
   with U fixed independently of D. U computed from D (PCA) is the falsifier: deleting d should move U.
8. **The learner is real**: UCI Optical Recognition of Handwritten Digits (optdigits, 3,823 train / 1,797 test,
   64 integer features in 0..16, ten classes; files pinned by SHA-256). Features are integers already, so the C18
   statistics are exact integers and the release is an exact rational solve. Measured before building: ridge
   one-vs-rest on the 65 features (64 + bias) classifies 1,660 / 1,797 test digits at λ = 1 (λ is chosen on a
   train split in the harness, not on test).

## 4. What gets built

- Harness: `unlearn_c18.py` (data, learner, MMR log with tombstones, event certificates, absence leg, verifier,
  ledger with proof-gated activation = C20), `unlearn_c19.py` (projected learner), `unlearn_sgd.py` (multinomial
  logistic SGD: exact suffix replay vs bound-only, measured distance vs the bound), `unlearn_custody.py` (SPDZ-shared
  statistics, Pedersen-committed, local deletion, MAC check, stranger check), `run_unlearn.py` (attacks, counts, JSON).
- Lean (minidregg `Assurance/Unlearning*.lean`): `delete_exact`, `delete_absence`, `release_unique`,
  `history_independent`, `sgd_delete_bound` composed with `Round.displacement_bound`; teeth for each; axioms pinned.
- Two Codex (gpt-6-astra) rounds against `delete_exact` and the approximate case; adjudication in the note.
