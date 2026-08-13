# CLAIM LEDGER — Rock 1 paper

2026-08-13. Every claim the draft makes, its status, its evidence pointer, and what would
falsify it. **This file is the contract: nothing goes into a submitted PDF at a strength
its row does not support.** Statuses:

- **PROVED-IN-LEAN** — a named theorem, buildable, axiom footprint pinned
- **MEASURED** — a named harness/command produced the number on real execution
- **COMPUTED** — a named, committed script reproduces the number deterministically
- **SOURCED** — cited to a document (external paper, or an internal note when flagged)
- **PENDING** — an in-flight lane owns it; the draft may state it only as prediction/plan

**Updated 2026-08-13 (late): gates G1 (red team), G2 (Lean — minidregg commit 641ceeb),
and G3 (experiment) all closed the same day this file was scaffolded.** Rows are flipped
accordingly, and the red team's four mandatory corrections are applied (prior-art C4.7,
noise floor C6.2, security numbers C6.3/C8.1/C8.4, barrel-shift C7.1). Detail:
notes/two-rocks.md "GATE RESULTS (2026-08-13)" and SUBMISSION-GATES.md.

⚠ Rows marked `(lane, uncommitted)` have evidence that exists only in a lane's notes —
real work, but not yet re-runnable by a reader. Each such row has a submission gate.
Absolute paths below; the repo-relative forms are `paper/scripts/…` and `notes/…`.

## C1 — the two-communities claim (the related-work section IS this claim)

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C1.1 | FHE and proof-system communities select moduli independently; every surveyed vFHE system picks from {Goldilocks, BabyBear, 2¹⁶+1, generic RNS} | SOURCED (lane survey) | /Users/ember/dev/zkml-research/notes/two-rocks.md, notes/joint-representation.md | one paper found that runs a joint modulus search — then our delta shrinks to family+certificates and §9 rewrites |
| C1.2 | ≥ six papers adopt an existing proof prime as an FHE modulus | SOURCED — **incomplete: only 2026/027 and GBFV are named in notes** | notes/two-rocks.md; gate G5 enumerates all six with citations | fewer than six withstand reading; then say the true count |
| C1.3 | HELIOPOLIS 2023/1949 §6.2 derives a two-sided feasibility region; 2025/286 states our exact tension and takes the weaken-the-PCS branch | SOURCED | the two eprints (lane-read; re-verify quotes at G5) | misreading of either section — re-read before camera-ready, these two get full-credit framing |
| C1.4 | 2-adicity appears in no FHE paper: 39 hits in a 25,765-paper corpus, none FHE | COMPUTED (lane; **re-grepped with pinned counts by the red team 2026-08-13, counts unchanged** — the grep itself is still uncommitted) | notes/two-rocks.md; gate G6 commits corpus manifest + grep command | a single FHE paper using proof-side 2-adicity — weakens "never crossed the boundary" to "rarely"; survivable but must be restated |

## C2 — the constraint is live (Zama 2026/027)

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C2.1 | 2026/027's instance bound D·t·n ≤ 2³¹ is imposed by Goldilocks' 2-adicity 32 — mechanism precise: `Domain::new` returns `None`, the `.expect` in `WhirConfig::new` panics, and at rate log_rho_inv = 1 the 2³² domain cap yields the 2³¹ instance bound | **MEASURED — G1 closed 2026-08-13** (reproduced at a pinned commit) | red-team transcript + derivation (artifact bundle: gate G15). Precision note folded: the early notes' literal `Domain::new(2^32, 2)` repro overshot the boundary 4× and named the wrong call — the conclusion stood | the bound traced to a different cause at another rev — sentence two of the abstract falls and the intro reshapes |
| C2.2 | that ceiling = one doubling of headroom above their current parameters | MEASURED (closed with C2.1) | red-team measurement of deployed D·t·n vs 2³¹ (bundle G15) | their current parameters move |
| C2.3 | Goldilocks 2-adicity = 32 (the arithmetic fact under C2.1) | COMPUTED | /Users/ember/dev/zkml-research/paper/scripts/verify_candidate.py (29/29 pass; output committed at paper/scripts/verify_candidate.out) | — (deterministic) |

## C3 — the constraint space is comfortable (the census)

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C3.1 | Solinas 2ᵃ−2ᵇ+1, a ∈ [96,130]: **117 primes**, **93 with 2-adicity ≥ 20** (adicity = b exactly) | COMPUTED | paper/scripts/verify_candidate.py (93 confirms notes/joint-representation.md; >64-bit primality is 40-round MR, error < 4⁻⁴⁰) | an accepted-parameterization recount disagreeing; certifiable primality proofs (e.g. Pratt/ECPP via the Lean lane) close even the MR caveat |
| C3.2 | ⚠ brief's census figure "104 Solinas + 106 Proth" | **PENDING — DISCREPANCY, unchanged by today's gates**: our script finds 117 Solinas under the stated band; the 104+106 parameterization was never committed | gate G4 reconciles; until then the draft quotes ONLY C3.1's numbers | — (this row exists to prevent the brief's number reaching the draft unverified) |
| C3.3 | Proth-form census for the band | PENDING | gate G4 (extend verify_candidate.py or commit the lane's script) | — |
| C3.4 | one-word band analysis + step-function cost model ⇒ optimum just under 64 bits | PENDING — **no committed artifact found in repo**; ASSUMED-BY-BRIEF | gate G10 | a cost model showing 2-word arithmetic within ~1.2× of 1-word on the actual prover — would move the optimum into the 96–130 band and demote p61 to "the one-word pick" |
| C3.5 | 31-bit structurally excluded as ciphertext modulus (security/noise floor ≈ 37 bits) | SOURCED (lane, uncommitted) | notes/two-rocks.md; re-derive at G7 with the pinned estimator | estimator run finding a secure+useful 31-bit instance |

## C4 — the candidate p = 2⁶¹ − 2⁵⁴ + 1

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C4.1 | p = 2287828610704211969 = 127·2⁵⁴+1, prime, KoalaBear's exact Solinas shape and cofactor one word up | **PROVED-IN-LEAN** — `p61_prime` (Lucas certificate **checked in the kernel**: `decide` through fueled `powMod` + correctness theorem `powMod_eq`; no `native_decide`), form `p61_eq_familyP` | minidregg Theory/CyclotomicInertia.lean @ 641ceeb; verify_candidate.py cross-check | — |
| C4.2 | 2-adicity exactly 54; negacyclic NTT legal to N = 2⁵³ | **PROVED-IN-LEAN** — `p61_sub_one` + `not_two_pow_55_dvd_p61_sub_one` (exactly 54), `p61_mod_8192`, `p61_domain_exists` (to 2⁵⁴) / `p61_no_domain_two_pow_55` | minidregg @ 641ceeb; verify_candidate.py exhibits ω of order 2⁵⁴ with ω^(2⁵³) = −1 | — |
| C4.3 | FRI instance ceiling 2⁵³ = 2²² × Goldilocks' 2³¹ | arithmetic on C4.2 (PROVED-IN-LEAN) + C2.1 (MEASURED) — both halves landed | rows above | — |
| C4.4 | Goldilocks-class reduction: fold identity 2⁶¹ ≡ 2⁵⁴−1 (mod p), plus 3 lazy-reduction bits (p < 2⁶¹) | COMPUTED; the *form* identity is PROVED-IN-LEAN (`p61_eq_familyP`) — ⚠ the fold **congruence** itself is NOT a named theorem in 641ceeb; two-line residue tracked at G12 | verify_candidate.py | — ("Goldilocks-class" = fold *shape* only — see C4.6, p61 has NO barrel-shift twiddles; no cycle-count is claimed anywhere until someone measures one) |
| C4.5 | maximal 3-adic inertia: ord₉(p) = 6, hence Φ_{3^k} irreducible ∀k; Goldilocks and BabyBear fail (ord₉ = 3), KoalaBear passes | **PROVED-IN-LEAN** — `maximalInertia_p61` / `orderOf_p61_three_pow` (via the family law at 54 ≡ 0 mod 6), `irreducible_cyclotomic_three_pow_p61`, conductor-81 field `P61Cyc81_isField` / `P61Cyc81_finrank` = 54 | minidregg @ 641ceeb; verify_candidate.py cross-check | — |
| C4.6 | **p61 has NO barrel-shift capability**: ord_p61(2) ≈ 2⁵⁷ — no draft prose may imply it inherits Goldilocks' shift twiddles | COMPUTED (red team 2026-08-13; script uncommitted) | ord computation → G8 bundle (blocked on G13/G14) | a small ord_p61(2) — would be a computation error, re-run |
| C4.7 | prior appearance: p61 sits in a **2014 candidate-moduli table** (stylewarning/lisp-random, comment-only output of a modulus-search tool; later carried into hypergeometrica's comments); **never an active modulus anywhere we can find** | SOURCED (red team 2026-08-13) | reference pins (URL + file + commit) owed at G5 | an actual deployment found — "never deployed" retracts and the delta restates; the 2014 listing itself is already in the paper as a footnote, so the frame survives |

## C5 — the family law 127·2ⁿ + 1

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C5.1 | for prime p = 127·2ⁿ+1: maximal inertia at every 3^k ⟺ n ≡ 0, 2 (mod 6); n odd or ≡ 3 (mod 6) ⇒ 3 \| p (no primes) | **PROVED-IN-LEAN** — `familyP_maximalInertia_iff` verbatim, with `maximalThreeAdicInertia_iff_irreducible` (order ⟺ Φ_{3^{k+1}} irreducible) and `not_prime_familyP_of_mod_six` (the no-prime branches) | minidregg @ 641ceeb; verify_candidate.py scan agrees | — (the theorem settles it) |
| C5.2 | both branches exhibited: n ∈ {2,12,18,24,54,72} prime and inert; **n = 214 prime and NOT inert (ord₉ = 2)** — first failing witness, search to 600 | **PROVED-IN-LEAN** (the teeth): `familyP_214_prime` (a **67-digit prime**, kernel-checked Lucas), `orderOf_familyP_214_mod_nine` = 2, `card_factors_9_familyP_214` (Φ₉ splits into **exactly 3 quadratic factors** — the factor count is the refutation witness); the ⟺ now has exhibited teeth in both directions. Scan to 600: COMPUTED | minidregg @ 641ceeb + verify_candidate.py | — |
| C5.3 | KoalaBear (n=24) and p61 (n=54) are instances of one theorem | **PROVED-IN-LEAN** — both are corollaries of `familyP_maximalInertia_iff`: `maximalInertia_koalaBear` / `orderOf_koalaBear_three_pow_of_family` (same statement as the direct §3 proof; both derivations kept) and `maximalInertia_p61` / `orderOf_p61_three_pow` | minidregg @ 641ceeb | — |

## C6 — the experiment (empirical centerpiece)

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C6.1 | the modulus swap removes the panic and moves the ceiling — **CONFIRMED on mechanism, REFUTED on "one line"**: domain ceiling 2³² → 2⁵⁴ by execution at the pinned WHIR rev (instance 2³¹ → 2⁵³ at rate log_rho_inv = 1), e2e prove/verify to ν = 29; p61 measured **10–40% FASTER** than Goldilocks at **equal proof sizes** (one machine, M2 Max, interleaved runs — do not inflate). Not one line — four hidden Goldilocks structures: (i) generator 2 is a QR mod p61; (ii) Fp2 constants; (iii) two Goldilocks-reduced test literals; (iv) RLWE encode/decode Goldilocks-structural two ways (bit-shift decode assuming 2⁶⁴ mod q tiny; `wrapping_add` through u64) — **12/12 unit tests green while decryption was garbage**; repaired in ~20 field-generic lines (13/13 on both fields) | **MEASURED — G3 closed 2026-08-13** | experiment transcripts + diff (bundle G15); the prediction was registered pre-run in notes/two-rocks.md | — (the "hidden dependence" falsifier fired exactly as this row said it would: reported in §5's "what was not one line", as a result — it is the thesis instantiated inside the artifact under study) |
| C6.2 | noise floor **55–59 bits** (≈55 at ~4-bit weights, **59 at 8-bit** with fhe.rs's actual sampled distributions); the 61-bit candidate clears the 8-bit floor by **2.4 bits** — tight, presented as such; 4-bit is the comfortable case. ⚠ the floor assumes **fhe.rs's exact-division encoding**: p61 mod t ≈ 0.95t is near-WORST for textbook-Δ BFV, so the encoding is part of the claim and the paper states it | COMPUTED (red team — supersedes the earlier **51**, which used weight bit-width as magnitude, a 16× ℓ1 understatement; 51 is really the ~4-bit-weight figure) | derivation script commits at G7; bound *shape* PROVED-IN-LEAN: /Users/ember/dev/breadstuffs/metatheory/Bfv/Noise.lean:264–287 — `matVecCt`, `RowBound`, `step_noise_le` | a workload whose true ℓ1 exceeds the row-sum assumption — restate the floor for it |
| C6.3 | lattice security improves under the swap: candidate core-SVP **213.7 (β = 732)** | COMPUTED (red team — the earlier draft number **205 was stale and matches no script**) | estimator scripts + commit pin at G7 | re-run disagreeing by >1 bit |

## C7 — negative results (reported as results)

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C7.1 | barrel-shift uniqueness, **restated 2026-08-13**: among primes Φ_m(2ᵇ) in **64–160 bits with 2-adicity ≥ 9**, Goldilocks is unique — and it is of the form **SIX ways**: Φ₆(2³²) = Φ₁₂(2¹⁶) = Φ₂₄(2⁸) = Φ₄₈(2⁴) = Φ₉₆(2²) = Φ₁₉₂(2). The original claim ("unique barrel-shift prime in 65–160 bits") was **FALSE twice over**: Goldilocks is 64 bits — outside its own window — and **37** Φ_m(2ᵇ) primes exist in 65–160 bits. Scope: the form is **sufficient, not necessary** for shift twiddles (prime *factors* of Φ_d(2) qualify — the 73-bit factor of F₇ is a live example), so the capability-level statement is a **bounded scan, not a theorem** | COMPUTED (red-team re-scan) — ⚠ the scan scripts carry the factorint-limit and primesearch-`ms` bugs; artifact blocked on **G13/G14**, then G8 | form identities: verify_candidate.py; scan → G8 | a shift-twiddle-capable prime in band with adicity ≥ 9 via the Φ_d(2)-factor route — flips "take-it-or-leave-it" framing |
| C7.2 | Crandall primes 2ᵏ−c structurally excluded: 2-adicity = v₂(c+1) ≤ 12 for c < 4096 | COMPUTED (one-line argument + script check) | verify_candidate.py | — (deterministic) |
| C7.3 | shift-twiddles unavailable at 96–130 bits (ord_p(2) astronomically large for every candidate) — **and at p61 itself (C4.6: ord ≈ 2⁵⁷)**; Solinas still buys shift+fold reduction | SOURCED (lane, uncommitted) + COMPUTED (red team, the p61 ord) | notes/joint-representation.md; fold-cost framing G10 | a census candidate with small ord_p(2) |
| C7.4 | NTT-inside-FRI-domain: novel (absent from 25,765-paper corpus) but worthless — NTT is 0.27% of reference proving (73% gadget decomposition); coset-separation ZK forfeited | novelty COMPUTED (lane, G6); cost **MEASURED (lane, uncommitted — harness unnamed in notes)** | notes/two-rocks.md; gate G9 names the profiling harness + command | NTT share ≫ 0.27% on a relevant workload would soften "worthless" to "narrow" |

## C8 — the security-model reconciliation

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C8.1 | same deployed parameters under the **actual sampled secret (CBD, η = 20)**: **130.5 bits (HE-standard) vs 98.1 (core-SVP)** — the ~32-bit spread is the MODEL, not the parameters; estimator validated against Kyber-768/1024; **reconciliation CLOSED by the red team to the 2019 HE standard's own formula and table row** | COMPUTED (red team — the earlier 127.9/95.5 pair was computed under a mislabeled secret distribution and is superseded; the model-spread claim survives the correction unchanged) | scripts + commit pin owed at G7 | re-run disagreeing by >1 bit |
| C8.2 | Zama's "~100 bits" reads 104.6 / 74.2 under the same two models | COMPUTED (lane; reconciliation closed with C8.1) | notes/two-rocks.md; G7 | same |
| C8.3 | 2026/027's code samples **binary** secrets; the paper does not state the distribution — reported neutrally as a reproducibility observation, NOT an attack | SOURCED (lane, uncommitted) | notes/two-rocks.md; gate G11 pins file+line at a repo commit | the distribution stated somewhere we missed (check paper versions + docs before publishing; G11 includes author contact) |
| C8.4 | our own stack: deployed secret is **centered binomial with parameter η = 20 — support ±20, variance 10 (σ = √10)**. Earlier notes recorded it as "ternary" AND as "CBD(10)"; **both were misreadings** (the 10 is the *variance*, not the parameter or the support). Threshold shares are ternary — two distributions in one tree. Actual-distribution readings: **98.1 core-SVP / 130.5 HE-model** (= C8.1) | SOURCED + COMPUTED (red team) — prior derived figures (the ~4.3-bit B_key gap, MATZOV ≈ 122) were computed under the misread labels and are **superseded pending the G7 re-run** | notes/fhe-core-theory.md carries the stale labels (correct it when next touched); G7 re-runs both shipped distributions | — |

## C9 — the Lean certificate artifact

| id | claim | status | evidence | falsifier |
|---|---|---|---|---|
| C9.1 | primality, family form, 2-adicity, NTT legality, family-law inertia, domain availability — all as named Lean theorems, pinned axiom footprints | **PROVED-IN-LEAN — G2 closed 2026-08-13**: minidregg Theory/CyclotomicInertia.lean @ **641ceeb** (+697 lines on the KoalaBear base); zero `sorry`, zero obligations, **no `native_decide`** (Lucas certificates `decide` through kernel-checked `powMod`), axiom pins at most [propext, Classical.choice, Quot.sound] | theorem names in the C4/C5 rows above; `#guard_msgs`-pinned `#print axioms` blocks in-file | ⚠ one residue: the fold *congruence* (C4.4) is script-only — a two-line theorem, tracked at G12 |
| C9.2 | the domain-availability lemma, parameterized over (p, d): positive at (p61, 2⁵⁴), **negative instance at (Goldilocks, 2³³) IS the §1 panic**, machine-checked | **PROVED-IN-LEAN (G2)** — `exists_subgroup_card_eq` / `not_exists_subgroup_card_eq` (parameterized); `p61_domain_exists` (to 2⁵⁴) + `p61_no_domain_two_pow_55`; **`goldilocks_no_domain_two_pow_33`** — the deployed `Domain::new(2^32)` panic stated as mathematics; `goldilocks_prime` proved en route (Lucas witness 7) | minidregg @ 641ceeb | — |
| C9.3 | artifact scope: certificates of parameter properties ONLY — not a verified FHE scheme, not verified FRI soundness | framing commitment | draft §8 carries the sentence | any draft text letting "machine-checked" leak wider — strike it |

## Cross-cutting honesty constraints (bind the whole draft)

- The abstract's experiment sentence is now a RESULT with a **split verdict** — mechanism
  confirmed, "one line" refuted — and never appears without the refuted half. The
  refutation is the thesis's second witness, not an embarrassment; write it that way.
- The speedup never travels without its caveat: **10–40%, one machine (M2 Max),
  interleaved runs, equal proof sizes.** Do not inflate.
- Every noise-floor number names the encoding it assumes (fhe.rs exact division; p61 mod
  t ≈ 0.95t is near-worst for textbook-Δ). At 8-bit weights the margin is **2.4 bits** —
  the draft presents the tightness, and presents 4-bit as the comfortable case.
- No cycle-count or throughput claim exists anywhere for p61 *reduction* (C4.4) —
  "Goldilocks-class" is a *shape* claim — and **no prose implies p61 inherits barrel-shift
  twiddles** (C4.6: ord_p61(2) ≈ 2⁵⁷).
- Numbers with status "(lane, uncommitted)" appear in the draft only with their gate named.
  At submission every such row is either upgraded (script/harness committed) or the number
  leaves the paper.
- Rock 2 appears exactly once, in future work, as one sentence, with "no cryptanalysis yet"
  attached (per notes/two-rocks.md).
