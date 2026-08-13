# CLAIM LEDGER — Rock 1 paper

2026-08-13. Every claim the draft makes, its status, its evidence pointer, and what would
falsify it. **This file is the contract: nothing goes into a submitted PDF at a strength
its row does not support.** Statuses:

- **PROVED-IN-LEAN** — a named theorem, buildable, axiom footprint pinned
- **MEASURED** — a named harness/command produced the number on real execution
- **COMPUTED** — a named, committed script reproduces the number deterministically
- **SOURCED** — cited to a document (external paper, or an internal note when flagged)
- **PENDING** — an in-flight lane owns it; the draft may state it only as prediction/plan

⚠ Rows marked `(lane, uncommitted)` have evidence that exists only in a lane's notes —
real work, but not yet re-runnable by a reader. Each such row has a submission gate.
Absolute paths below; the repo-relative forms are `paper/scripts/…` and `notes/…`.

## C1 — the two-communities claim (the related-work section IS this claim)

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C1.1 | FHE and proof-system communities select moduli independently; every surveyed vFHE system picks from {Goldilocks, BabyBear, 2¹⁶+1, generic RNS} | SOURCED (lane survey) | /Users/ember/dev/zkml-research/notes/two-rocks.md, notes/joint-representation.md | one paper found that runs a joint modulus search — then our delta shrinks to family+certificates and §9 rewrites |
| C1.2 | ≥ six papers adopt an existing proof prime as an FHE modulus | SOURCED — **incomplete: only 2026/027 and GBFV are named in notes** | notes/two-rocks.md; gate G5 enumerates all six with citations | fewer than six withstand reading; then say the true count |
| C1.3 | HELIOPOLIS 2023/1949 §6.2 derives a two-sided feasibility region; 2025/286 states our exact tension and takes the weaken-the-PCS branch | SOURCED | the two eprints (lane-read; re-verify quotes at G5) | misreading of either section — re-read before camera-ready, these two get full-credit framing |
| C1.4 | 2-adicity appears in no FHE paper: 39 hits in a 25,765-paper corpus, none FHE | COMPUTED (lane, uncommitted) | notes/two-rocks.md; gate G6 commits corpus manifest + grep command | a single FHE paper using proof-side 2-adicity — weakens "never crossed the boundary" to "rarely"; survivable but must be restated |

## C2 — the constraint is live (Zama 2026/027)

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C2.1 | 2026/027's instance bound D·t·n ≤ 2³¹ is imposed by Goldilocks' 2-adicity 32; `Domain::new(2^32)` panics | **PENDING — red-team lane re-reproducing** (first execution 2026-08-13, recorded in notes/two-rocks.md) | gate G1: pinned repo commit + command + panic transcript | panic not reproducible at a pinned commit, or the bound traced to a different cause — sentence two of the abstract falls and the intro reshapes |
| C2.2 | that ceiling = one doubling of headroom above their current parameters | PENDING (rides C2.1) | same lane: their deployed D·t·n vs 2³¹ | their current parameters are further from the ceiling than one doubling |
| C2.3 | Goldilocks 2-adicity = 32 (the arithmetic fact under C2.1) | COMPUTED | /Users/ember/dev/zkml-research/paper/scripts/verify_candidate.py (29/29 pass; output committed at paper/scripts/verify_candidate.out) | — (deterministic) |

## C3 — the constraint space is comfortable (the census)

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C3.1 | Solinas 2ᵃ−2ᵇ+1, a ∈ [96,130]: **117 primes**, **93 with 2-adicity ≥ 20** (adicity = b exactly) | COMPUTED | paper/scripts/verify_candidate.py (93 confirms notes/joint-representation.md; >64-bit primality is 40-round MR, error < 4⁻⁴⁰) | an accepted-parameterization recount disagreeing; certifiable primality proofs (e.g. Pratt/ECPP via the Lean lane) close even the MR caveat |
| C3.2 | ⚠ brief's census figure "104 Solinas + 106 Proth" | **PENDING — DISCREPANCY**: our script finds 117 Solinas under the stated band; the 104+106 parameterization was never committed | gate G4 reconciles; until then the draft quotes ONLY C3.1's numbers | — (this row exists to prevent the brief's number reaching the draft unverified) |
| C3.3 | Proth-form census for the band | PENDING | gate G4 (extend verify_candidate.py or commit the lane's script) | — |
| C3.4 | one-word band analysis + step-function cost model ⇒ optimum just under 64 bits | PENDING — **no committed artifact found in repo**; ASSUMED-BY-BRIEF | gate G10 | a cost model showing 2-word arithmetic within ~1.2× of 1-word on the actual prover — would move the optimum into the 96–130 band and demote p61 to "the one-word pick" |
| C3.5 | 31-bit structurally excluded as ciphertext modulus (security/noise floor ≈ 37 bits) | SOURCED (lane, uncommitted) | notes/two-rocks.md; re-derive at G7 with the pinned estimator | estimator run finding a secure+useful 31-bit instance |

## C4 — the candidate p = 2⁶¹ − 2⁵⁴ + 1

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C4.1 | p = 2287828610704211969 = 127·2⁵⁴+1, prime (deterministic MR < 2⁶⁴), KoalaBear's exact Solinas shape and cofactor one word up | COMPUTED → **PENDING Lean** (`p61_prime`, family form) | paper/scripts/verify_candidate.py; gate G2 | — (deterministic; Lean adds the certificate) |
| C4.2 | 2-adicity exactly 54; negacyclic NTT legal to N = 2⁵³ (ω of order 2⁵⁴ exhibited, ω^(2⁵³) = −1) | COMPUTED → PENDING Lean | verify_candidate.py; gate G2 (NTT-legality cert + domain-availability lemma) | — |
| C4.3 | FRI instance ceiling 2⁵³ = 2²² × Goldilocks' 2³¹ | arithmetic on C4.2 + C2 | rides C2.1 for the Goldilocks half | C2 falling restates this as "2²² × the Goldilocks *domain* gap" without the deployed-ceiling hook |
| C4.4 | Goldilocks-class reduction: fold identity 2⁶¹ ≡ 2⁵⁴−1 (mod p), plus 3 lazy-reduction bits (p < 2⁶¹) | COMPUTED → PENDING Lean | verify_candidate.py; gate G2 | — (note: "Goldilocks-class" = same fold *shape*; no cycle-count is claimed anywhere until someone measures one) |
| C4.5 | maximal 3-adic inertia: ord₉(p) = 6, hence Φ_{3^k} irreducible ∀k; Goldilocks and BabyBear fail (ord₉ = 3), KoalaBear passes | COMPUTED (ord₉ + direct check k ≤ 8) → PENDING Lean (∀k) | verify_candidate.py; route exists: /Users/ember/dev/minidregg/Theory/CyclotomicInertia.lean — `orderOf_koalaBear_three_pow`, `irreducible_cyclotomic_of_orderOf_eq_totient`; gate G2 instantiates at p61 | — (deterministic; the ∀k lift is the standard cyclic-group argument the Lean file already executes for KoalaBear) |

## C5 — the family law 127·2ⁿ + 1

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C5.1 | for prime p = 127·2ⁿ+1: maximal inertia at every 3^k ⟺ n ≡ 0, 2 (mod 6); n odd or ≡ 3 (mod 6) ⇒ 3 \| p (no primes) | COMPUTED (scan n ≤ 80 + proof sketch: 127 ≡ 1 mod 9, 2ⁿ mod 9 period 6) → **PENDING Lean** | verify_candidate.py; gate G2 | a family prime violating the law — none exists if the mod-9 argument is right, which is what the Lean theorem settles |
| C5.2 | both branches exhibited: n ∈ {2,12,18,24,54,72} prime and inert; **n = 214 prime and NOT inert (ord₉ = 2)** — first failing witness, search to 600 | COMPUTED (n=214 is 40-round MR) | verify_candidate.py | — |
| C5.3 | KoalaBear (n=24) and p61 (n=54) are instances of one theorem | COMPUTED; KoalaBear half PROVED-IN-LEAN today (`orderOf_koalaBear_three_pow`) | verify_candidate.py + minidregg CyclotomicInertia.lean; gate G2 makes both corollaries of the family statement | — |

## C6 — the experiment (empirical centerpiece)

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C6.1 | one-line swap (`#[modulus]` → 2287828610704211969 + F2 constants) removes the ν=32 panic and moves the ceiling 2³¹ → 2⁵³ | **PENDING — experiment lane** | prediction registered in notes/two-rocks.md before the run | hidden Goldilocks dependence making it not-one-line (→ reported in §5's "what was not one line", still a result); ceiling not moving (→ paper reshapes around census+family+certificates) |
| C6.2 | cost ≈ 3 bits of noise margin (log q 64 → 61) | PENDING (lane measures against the row-sum bound) | bound *shape* PROVED-IN-LEAN: /Users/ember/dev/breadstuffs/metatheory/Bfv/Noise.lean:264–287 — `matVecCt`, `RowBound`, `step_noise_le`; this instance's numbers are the lane's | measured loss ≫ 3 bits |
| C6.3 | lattice security improves under the swap | PENDING (G7 estimator, both models, stated secret distribution) | — | estimate not improving — would contradict smaller-q-same-n monotonicity, so first suspect the run |

## C7 — negative results (reported as results)

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C7.1 | Goldilocks is the UNIQUE barrel-shift prime in 65–160 bits (Φ₆(2³²) = Φ₁₂(2¹⁶) = Φ₂₄(2⁸), unique three times over) | identities COMPUTED (verify_candidate.py); **uniqueness scan (lane, uncommitted)** | notes/two-rocks.md; gate G8 commits the scan or the Lean proof | a second barrel-shift prime in band — flips "take-it-or-leave-it" framing |
| C7.2 | Crandall primes 2ᵏ−c structurally excluded: 2-adicity = v₂(c+1) ≤ 12 for c < 4096 | COMPUTED (one-line argument + script check) | verify_candidate.py | — (deterministic) |
| C7.3 | shift-twiddles unavailable at 96–130 bits (ord_p(2) astronomically large for every candidate); Solinas still buys shift+fold reduction | SOURCED (lane, uncommitted) | notes/joint-representation.md; fold-cost framing G10 | a census candidate with small ord_p(2) |
| C7.4 | NTT-inside-FRI-domain: novel (absent from 25,765-paper corpus) but worthless — NTT is 0.27% of reference proving (73% gadget decomposition); coset-separation ZK forfeited | novelty COMPUTED (lane, G6); cost **MEASURED (lane, uncommitted — harness unnamed in notes)** | notes/two-rocks.md; gate G9 names the profiling harness + command | NTT share ≫ 0.27% on a relevant workload would soften "worthless" to "narrow" |

## C8 — the security-model reconciliation

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C8.1 | same deployed parameters: 127.9 bits (HE-standard) vs 95.5 (core-SVP); estimator validated against Kyber-768/1024 | COMPUTED (lane, uncommitted) | notes/two-rocks.md; gate G7 commits estimator scripts + commit pin + validation rows | re-run disagreeing by >1 bit |
| C8.2 | Zama's "~100 bits" reads 104.6 / 74.2 under the same two models | COMPUTED (lane, uncommitted) | notes/two-rocks.md; G7 | same |
| C8.3 | 2026/027's code samples **binary** secrets; the paper does not state the distribution — reported neutrally as a reproducibility observation, NOT an attack | SOURCED (lane, uncommitted) | notes/two-rocks.md; gate G11 pins file+line at a repo commit | the distribution stated somewhere we missed (check paper versions + docs before publishing; G11 includes author contact) |
| C8.4 | our own stack: deployed secret CBD(10), threshold shares ternary (~4.3 bits apart in B_key-carrying bounds); MATZOV reading ≈ 122 | SOURCED (source-verified lane) | notes/fhe-core-theory.md (verified against vendor/fhe-dregg + metatheory/Bfv); G7 re-runs both distributions | — |

## C9 — the Lean certificate artifact

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C9.1 | primality, family form, 2-adicity, NTT legality, fold identity, family-law inertia — all as named Lean theorems, pinned axiom footprints | **PENDING — Lean lane (gate G2)** | template PROVED-IN-LEAN today: minidregg Theory/CyclotomicInertia.lean (488 lines, KoalaBear instance complete) | lane returning `native_decide`-only or unnamed-`#guard` artifacts — repo discipline (metatheory/docs/GUARD-DISCIPLINE.md) forbids; the gate audits statements, not green |
| C9.2 | the domain-availability lemma, parameterized over (p, ν): positive at (p61, 53), **negative instance at (Goldilocks, 32) IS the §1 panic**, machine-checked | PENDING (G2) — the paper's best single artifact if it lands | — | — |
| C9.3 | artifact scope: certificates of parameter properties ONLY — not a verified FHE scheme, not verified FRI soundness | framing commitment | draft §8 carries the sentence | any draft text letting "machine-checked" leak wider — strike it |

## Cross-cutting honesty constraints (bind the whole draft)

- The abstract's experiment sentence stays conditional until C6 lands; C6 failing reshapes
  the paper, and the ledger row says to.
- No cycle-count or throughput claim exists anywhere for p61 reduction (C4.4) — "Goldilocks-
  class" is a *shape* claim. If a reviewer reads speed into it, the text failed; fix the text.
- Numbers with status "(lane, uncommitted)" appear in the draft only with their gate named.
  At submission every such row is either upgraded (script/harness committed) or the number
  leaves the paper.
- Rock 2 appears exactly once, in future work, as one sentence, with "no cryptanalysis yet"
  attached (per notes/two-rocks.md).
