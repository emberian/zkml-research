# Unlearning certificates: what a stranger can check about a deletion, and what nobody can

2026-11-06. Initiative 16 (C18-C20 of `docs/DARK-LEARNING-PROGRAM.md`). Grounding, prior art and the corrections to
the bar: `notes/unlearning/GROUNDING.md`. Harness: `research/dark_learning_2026_11_06/unlearn_*.py`,
`run_unlearn.py`, results `unlearn_results.json` (bb2 run of c18, c19, sgd) + `unlearn_results_custody.json` (hbox), logs `unlearn_run.log`, `unlearn_custody.log`. Lean: minidregg branch `lane/unlearning-certs`,
`Assurance/UnlearningExact.lean`, `Assurance/UnlearningSgd.lean`. Every number below is a count from the run.

## 1. The table: which unlearning claims are verifiable

| claim | verifiable? | by whom, from what | where |
|---|---|---|---|
| the post-deletion STATE of a sufficient-statistics learner equals the learner's state on the remaining records | **yes, exactly** | a stranger holding only the ledger head (+ the public statistics, or their commitment when custodied); the certificate carries the record, positions, paths and the whole post-deletion leaf list | `delete_exact`, `deleted_equals_never_trained`; harness C18, C19, custody |
| "trained then deleted" and "never trained" are indistinguishable from the state | **yes, as a theorem** (history independence: the state is a function of the live multiset) | nobody needs to check it per deletion; it is the learner's structure | `history_independent`; harness: stats and model commitments byte-identical to a from-scratch run |
| the released model after deletion is the retrained model | **yes, exactly**, given `λ > 0` pinned at genesis | the stranger checks `(λI + A) N = δ B` over Z on the D x 10 matrix (shape checked) | `release_unique`, `deleted_release_is_retrained` |
| every copy of the record is gone from the committed set | **yes**: whole-log Count = 0 over the MMR | stranger, O(n) leaf hashes (32 bytes per record, never the records) | the absence leg; `DeleteLegs.absent`; refuses the duplicate-deleted-once falsifier |
| nothing of the record's content survives in the state | **yes, as a theorem**: the state is unchanged by any redefinition of the record's contribution | | `influence_gone` |
| the log no longer shows the record happened | **NO, and it must not**: tombstones record that a deletion happened (accountability) | | §4 |
| old roots, old openings, old releases, old copies are gone | **NO**: a certificate cannot erase history; an old root plus an old opening proves past membership forever | needs custody-side erasure (C22) and refusal of stale roots (C20, C13) | §4 |
| an SGD learner "forgot" d | **only as a bound, only structurally**: `‖w − w_never‖ ≤ ε` given the run is the prescribed one (proved per step) and the Lipschitz constants are certified; ε is the whole claim, and doing nothing satisfies it | stranger checks the schedule (which steps used d), the constants and ε | `traj_gap`, `sgd_delete_bound`; harness SGD |
| an SGD learner forgot d, with SAMPLED audits | **only in expectation**: `E‖deployed − never-d‖ ≤ G + 2B/q` at the first alarm | the displacement theorem's legs | `sgd_delete_bound_audited` |
| an SGD learner forgot d, exactly | **yes**, by replaying the suffix from d's first step, with a FULL proof of every replayed step (Astra DL12) | bit-identical to the comparator in the harness | harness SGD, exact replay |
| a model "forgot" d, judged from its weights or outputs alone | **NO** (Thudi et al. 2022: the same model is reachable without d; Zhang et al. 2024 break both verification styles) | | prior art, not re-proved |

## 2. What was built

**The learner (C18).** Ridge regression, one-vs-rest on ten one-hot targets, on UCI optdigits (3,823 train records,
1,797 test; 64 integer features in 0..16, plus a bias: D = 65). State: the exact integer statistics
`A = Σ φφᵀ`, `B = Σ φ e_yᵀ` of the live records. Release: the exact rational solution of `(λI + A)W = B` in canonical
form `N/δ` (δ has 830 bits). Test accuracy 1,660 / 1,797 before and after deleting ten keys (eleven records). Replaying the whole history from genesis costs the verifier 3,824 insert certificates: 71,536 hashes and 8,202,480 products.
`λ = 1` is pinned a priori: Codex round 1 showed that a λ chosen by validation on deletable records depends on them
(a synthetic case kept λ = 16 where re-selection on D \ d gives 1), so the comparator is "retrain with the
hyperparameters fixed at genesis". Any data-dependent choice (λ, φ, normalisation, schedule) must be pinned from
non-deletable data or re-run inside the deletion; the C19 falsifier below is the same point for φ.

**The commitments.** The dataset log is an MMR in dregg-query's shape (peaks oldest-first, bagged by `bag(peak, rest)`,
domain-separated leaf / node / bag / empty; SHA-256 for BLAKE3). A leaf is the record's content key while live and
a tombstone `H("tomb", position)` after. Positions never move. A head binds (genesis = φ, λ, data source pins;
parent; seq; log root; log length; statistics commitment; active model commitment or none).

**The certificates and the verifier** (`Ledger.accept`; it holds the head and the public statistics, never the data):

| certificate | the verifier checks | counts per certificate (verifier only) |
|---|---|---|
| insert(r) | record shape; frontier bags to the root; appends `K(r)`; recomputes `S + contrib(r)` itself; the claimed head equals the one it determines, field for field, no extra fields | 27 hashes, 2,145 products (`D(D+1)/2`; B is additions) |
| delete(key) | record shape and hash; one path per position; each position opens to the key and becomes a tombstone (sequential updates); the whole post-deletion leaf list rebuilds the new root and has Count(key) = 0; recomputes `S − m·contrib(r)`; no active model after | m = 1: 7,693 hashes, 3,824 leaf compares, 2,145 products; m = 2: 7,734 hashes |
| release(N, δ) | δ > 0; N is D x 10 integers; canonical; `(λI + A)N = δB` exactly | 42,250 big-integer products |
| serve(model) | only the head's active model (C20: none after a deletion until a release verifies) | |

The absence leg dominates a deletion: it is the whole-log scan (3,824 leaf comparisons and the rebuild hashes;
122,368 bytes of leaf keys). That is the absence protocol's cost, linear in the log; a recursive aggregate of the
scan (dossier 01 step 5) is the succinct form, priced there, not built here.

**Exactness, measured.** After eleven deletions (a duplicated record's two copies plus nine others), the ledger's
statistics commitment and model commitment are byte-identical to those of a from-scratch run on the remaining
records; the logs differ by exactly 11 tombstones.

**Attacks** (each a mutation of an honest certificate; 22 of 22 REFUSED by the named check, C18 and C19 alike): see
`attacks` in the results. They are the bar's three (a fake deletion that keeps the record, A1a-c; a deletion of a
different record, A2a-c; a state trained on d that claims not, A3a-c including serving the pre-deletion model
after the deletion), the program's three C18 falsifiers (A4 duplicate deleted once; A5 φ changed; A6 λ = 0,
where two distinct canonical models pass the release check, so λ > 0 is pinned), stale parent, absence-leg
omission and substitution, fork, deleting a never-inserted record, and Codex round 1's two (A11 a release with an
extra row carrying the deleted record, which the first version ACCEPTED; A12 a record with a trailing payload)
and Codex round 2's (A13 a head with an extra field carrying the record, which the second version ACCEPTED).

**C19, the fixed public subspace.** ψ = Uᵀ(x, 1) with U the 15 lowest 2-D DCT frequencies (u + v ≤ 4) of the
8 x 8 image, integer-scaled, plus the bias: r = 16, a 16 x 16 + 16 x 10 state. Same theorem, same driver, same 22
attacks refused (22 of 22, as for C18); exact. The capacity price: 1,553 / 1,797 test digits against 1,660 for the full features. The
falsifier bites: with U = PCA of D (data-dependent), deleting one record moves 846 of 1,040 basis entries and the
subtracted state is NOT the learner on D \ d.

**The custodied variant.** See §3.

**SGD.** Multinomial logistic regression, B₀ = 32, weight decay 0.05, η = 1/(λ + L) with the PUBLIC
L = 65/2 (‖x‖² ≤ 65 for pixels / 16 plus the bias; Codex round 2: not the data's maximum), so the update map is
ρ-Lipschitz with ρ = 1 − ηλ = 0.998464; 5 epochs (600 steps), 1,622 / 1,797 test digits. For four deleted records:
exact replay from d's first step (517-581 of 600 steps replayed) is bit-identical to the never-d run; the measured
distance of the do-nothing state is 2.8e-3 to 3.6e-3 against a certified ε of 1.56e-2 to 1.69e-2 (4.6-5.9x
slack); three more epochs on D \ d shrink the certified ε to 9.0e-3 to 9.7e-3 (measured 1.3e-3 to 1.7e-3). The
price of forgetting by contraction is visible: at ρ = 0.9985 a halving of ε costs ~450 steps. The host term:
re-injecting d's gradient on every round under a 5% sampled audit gives a mean deviation at the stop of 3.1e-2
over 40 trials, under the a priori D/q = 1.03e-1 (`displacement_bound_of_gap`, D = η√2‖x_d‖/B₀).

## 3. Custody

Three custodians hold the 4,875 statistics as SPDZ shares with MACs over a 256-bit prime field (the harness's
`spdz.py`, imported unmodified at blob ad90dddf, the gen-3 lane's working copy with committed sigma openings). The
record is the host's, so a deletion is a PUBLIC-coefficient update: party 0 subtracts `m·c` from its share, every
party subtracts `α_i·m·c` from its MAC share. No communication, no triples. Per deletion: 650 to 930 local updates
per party (the record's nonzero contribution entries).

| check | for whom | what it establishes | counts per deletion |
|---|---|---|---|
| homomorphic Pedersen check `Π C_i' = Π C_i · Com(m·c)⁻¹` (2048-bit Schnorr group, 256-bit order) | a stranger, from the published commitments and the public record | the COMMITTED state moved by exactly the record's contribution | 650-930 small-exponent exponentiations |
| MAC check in the exponent: `Π D_i = Π_i (Π_j C_j)^{α_i}`, each factor with a Chaum-Pedersen proof against `g0^{α_i}` | a stranger | the commitments commit to the MAC-AUTHENTICATED shared state (Codex round 2's missing link) | 12 exponentiations |
| zero test: open `Σ r_k (S'_k − S_k + m c_k)`, coins hashing every custodian's commitment to its updated (share, MAC) vector, then the SPDZ MAC check | the custodians | the authenticated update is the public one | 18 wire elements |
| log legs (positions, tombstones, whole-log Count = 0) | a stranger | as host-visible (shared code) | as §2 |

Custody entry costs 29,250 exponentiations (share and MAC-share commitments for three custodians). After four
deletions (a duplicate's two copies and three others) every check passes on every deletion, and the reconstructed
dark state equals the host-visible fold over the remaining records.

Attacks and outcomes: K1 (commitments unchanged) and K2 (commitment subtracts a different record) refused by the
stranger; K5 (a custodian's commitment off by `contrib(d)` from its share) and K6 (the same, with its MAC commitment
offset by `α_1·e`, which is all it can do without `α`) refused by the MAC check in the exponent; K3 (a custodian
moves its share by a different record) refused by the zero test; K7: an error orthogonal to PREDICTABLE coins keeps
part of d's contribution in a share and is ACCEPTED by the legacy zero test (Codex round 2's attack, the falsifier
bites), and refused once the coins hash the committed updated shares.

K4 is not a refusal, and the note says why rather than counting it: a custodian whose raw share deviates and who
lies at the opening back to the honest value passes, because its MAC shares followed the public rule. What custody
can ever open is the MAC-AUTHENTICATED value, which is the honest one; a deviating raw share is a future lie that
every later MAC check catches unless it restores that value. The guarantee is therefore about the authenticated
state (which the commitments now bind), not about bytes a custodian stores. (My first harness expected K4 refused;
the run said otherwise and the run is right.)

Not built: a release FROM custody (an MPC solve of the 65 x 65 system, plus a proof the stranger can check: the
gen-3 lane's collaborative proof is the composition point); a post-quantum commitment (Pedersen binding is discrete
log; an SIS commitment admits the same homomorphic and MAC-in-the-exponent checks). FHorgEt (ePrint 2026/510) is the
prior art for FHE+MPC unlearning with lifecycle confidentiality; what this adds is a deletion a stranger checks
from commitments.


## 4. What a deletion certificate cannot do

- **History stays.** Old heads and old openings prove that d was in the set. The event chain names the deleted
  key. Tombstone positions say where. This is accountability, not leakage, by design (GROUNDING §3.4): the state
  must not distinguish never-trained from deleted, the log must. A host that kept a copy of the pre-deletion
  statistics or model still has it; refusing to SERVE it is C20 (the ledger has no active model after a deletion
  until a release verifies, and serves only the head's), erasing it is C22.
- **The key is a membership oracle.** Count(c) = 0 is publicly checkable, so Count(c) = 1 is too: anyone who can
  guess a record can test it against the log. A hiding commitment would stop that and also stop the public
  absence check; the trade is the requester's to make.
- **Patterns beyond exact content** (a regex over record bytes) need the DFA leg of dossier 01; not built here.
- **Hyperparameters and feature maps** must be pinned independently of deletable data (§2), or the comparator is
  weaker than "retrain the pipeline".

## 5. Cross-model rounds

Two rounds, `codex exec -c model="gpt-6-astra" --sandbox read-only`. Round 1's final summary was withheld by the
service ("this session was not authenticated with one of your authorized hardware keys"); its findings were
recovered from its working notes and its executed probes. Round 2 completed.

| # | finding | verdict | what changed |
|---|---|---|---|
| r1.1 | the release check read only the first D x 10 entries: an extra row of N carried the deleted record into the accepted model commitment, and was served | ACCEPTED (executed: the first version accepted it) | shape check; attack A11 |
| r1.2 | λ chosen by validation on deletable records depends on them (a synthetic case: λ 16 kept, re-selection on D \ d gives 1) | ACCEPTED | λ pinned a priori at genesis; the comparator is named "retrain with genesis hyperparameters" |
| r1.3 | the harness's host term used the largest gap OBSERVED in the trials; the theorem needs an a priori one | ACCEPTED | D = η√2‖x_d‖/B₀, asserted ≥ every observed gap |
| r1.4 | the ledger stored the prover's own head object (aliasing) | ACCEPTED | the ledger stores the head IT computes |
| r2.1 | extra head fields survived acceptance (a field could carry d); genesis source aliased its caller; the diagnostic λ sweep was itself a data-dependent output; SGD's η came from the data's max norm | ACCEPTED | exact head schema (A13); genesis frozen to a canonical string; sweep removed; L = 65/2 public |
| r2.2 | custody: the zero test's coins hashed only public commitments and the request, so a custodian could pick an error e with ⟨r, e⟩ = 0 and keep part of d's contribution in its share with consistent MACs; and nothing tied published commitments to held shares | ACCEPTED, both | coins now hash every custodian's commitment to its UPDATED (share, MAC) vector (K7: the legacy test accepts the orthogonal error, the fixed one refuses it); the MAC check lifted to the exponent ties commitments to the authenticated state (K5, K6) |
| r2.3 | `sgd_delete_bound_audited`: right coupling, uniform G is what random stopping needs, ρ ≤ 1 is what stops amplification; `audited_fires` has zero influence | ACCEPTED (statement), ACCEPTED (witness gap) | `audited_fires_influence`, `audited_influence_real` (distance exactly 1 after one round, inside 1 + 4) |
| r2.4 | `release_unique` concluded only cross-multiplication; (N, δ) = (0, 0) passes the bare check; `influence_gone` is contribution-map invariance, not "nothing inferable" | ACCEPTED | nonzero denominators, quotient conclusion (`release_cross` kept as the trivial-at-0 form); docstrings narrowed |
| r2.5 | the null-record SGD comparator (fixed B₀, empty slot) is fair for a publicly fixed slot schedule; repacking is a different comparator | ACCEPTED as stated | |
| r2.6 | keys, parent chains and tombstone positions break transcript indistinguishability | ACCEPTED as a scope statement | §4: the guarantee is about the state and the release, never the transcript |

On the question the bar asked: the certificate does NOT distinguish "never trained on d" from "trained and deleted"
at the level of the state and the release (that is the theorem), and it should not; the transcript (log, keys,
certificates) does, and it should, as accountability. Both rounds agreed.


## 6. Rerun

    cd research/dark_learning_2026_11_06
    python3 run_unlearn.py            # c18 c19 sgd custody; fetches optdigits into data/ (SHA-256 pinned)
    python3 run_unlearn.py c18        # minutes on a quiet machine; custody wants a build box (2048-bit group)

Lean, on a minidregg tree with the pool's packages: `lake build Assurance.UnlearningExact Assurance.UnlearningSgd`.
