# DRAFT — Rock 1: the joint representation paper

Status: scaffold, 2026-08-13; **updated the same day after gates G1–G3 closed** (red team,
Lean, experiment — see SUBMISSION-GATES.md and notes/two-rocks.md "GATE RESULTS").
Abstract and introduction are full prose; sections 2–10 are structured bullet drafts.
Every number carries an inline provenance tag `[Cn · STATUS]` resolving to a row of
`CLAIM-LEDGER.md`; tags are stripped at submission. Rock 2 (the ring-native hash) is out
of scope except for one sentence in future work.

**Do not cite anything tagged PENDING as established. The ledger is the contract.**

---

## Title

Candidates, with a recommendation:

1. *Choosing the Modulus Together: Joint Parameter Selection for Verifiable Homomorphic
   Computation* — accurate frame, but generic; nothing in it survives as a handle.
2. *KoalaBear, One Word Up: NTT-and-FRI-Friendly Primes for Single-Modulus Verifiable FHE*
   — memorable and literally true (127·2⁵⁴+1 vs 127·2²⁴+1), but assumes the reader knows
   KoalaBear, and "single-modulus" oversells even now that the experiment has landed: the
   deployed BFV tower is untouched by it.
3. **Recommended: *Choosing the Modulus Together: an NTT- and FRI-Friendly Prime Family for
   Verifiable Homomorphic Encryption*** — the frame from (1), the concrete deliverable from
   (2), no dependence on the reader's field-name vocabulary. "KoalaBear, one word up"
   survives as the first sentence of §4, where it earns its keep.
4. Rejected: anything with "nobody" in it. The related-work section says it generously;
   the title should not say it at all.

## Venue

**eprint first, then CiC (IACR Communications in Cryptology).** Reasoning: the paper's
contributions are a constraint system, a search, a prime family, negative results, and
machine-checked certificates — CiC explicitly accepts parameter-selection, implementation,
SoK-adjacent, and negative-result papers that the big-four venues treat as out of band,
and its audience (IACR) spans both communities this paper addresses, which is the point.
TCHES is the alternate if §5 grows into a real performance story — the measured 10–40% is
a single-machine feasibility observation, not that story — and TCHES expects
implementation depth we do not intend to build. RWC is worth a talk submission for reach;
it is not archival and does not replace CiC.

---

## Abstract (~200 words)

FHE implementations choose their moduli for noise budget and RNS efficiency; proof systems
choose their fields for NTT domains and FRI soundness — and the two choices are made by
different communities, independently. The cost is now measurable in a deployed system: the
verifiable-FHE scheme of Zama (eprint 2026/027) proves over the Goldilocks field, whose
2-adic subgroup caps instances at D·t·n ≤ 2³¹ — one doubling of headroom above its current
parameters, a ceiling imposed by a modulus chosen without consulting the proof-side domain
`[C2 · MEASURED — G1 closed]`. We pose modulus selection as a joint problem and run the
search neither community has run. The space is comfortable, not tight: Solinas primes at
96–130 bits alone give 117 candidates, 93 with 2-adicity ≥ 20 `[C3 · COMPUTED]`, and a
word-granular cost model places the optimum just below 64 bits `[C3 · PENDING]`. We
propose p = 2⁶¹ − 2⁵⁴ + 1 = 127·2⁵⁴ + 1 — never deployed anywhere, though once listed in
a 2014 search-candidate table `[C4.7 · SOURCED]` — with 2-adicity 54, negacyclic NTT to
length 2⁵³, Goldilocks-class fold reduction with three spare bits, and maximal inertia at
every power-of-three conductor, which Goldilocks and BabyBear both fail
`[C4 · PROVED-IN-LEAN]`. The inertia property is one instance of a family law for
127·2ⁿ + 1, machine-checked with its failing branch exhibited `[C5 · PROVED-IN-LEAN]`.
Executing the swap in a deployed encrypted matrix-vector kernel moved the domain ceiling
2³² → 2⁵⁴ and ran 10–40% faster than Goldilocks at equal proof sizes on one machine — and
was **not** the predicted one line: the kernel's RLWE encode/decode was
Goldilocks-structural in two hidden ways, its unit tests green while decryption was
garbage — our thesis, instantiated inside the artifact under study `[C6 · MEASURED]`. At
8-bit weights the candidate clears the measured 59-bit noise floor by 2.4 bits; we state
the encoding this assumes `[C6 · COMPUTED]`. Every parameter claim ships as a Lean theorem
with a pinned axiom footprint `[C9 · PROVED-IN-LEAN]`. We also report what fails: among
cyclotomic-form primes Φ_m(2ᵇ) at 64–160 bits with 2-adicity ≥ 9, Goldilocks is the only
one — and p61 has no barrel-shift capability of its own; Crandall primes cap at 2-adicity
12; NTT-inside-FRI-domain is novel but worthless `[C7]`.

*(Drafting note: sentence two carries the one-doubling fact, per plan. The experiment
sentence is now a RESULT — G3 closed — and always carries the split verdict: mechanism
confirmed, "one line" refuted. Never quote the speedup without "one machine"; the runs
were interleaved on an M2 Max and prove feasibility, not throughput. Well over 200 words;
G12 trims.)*

---

## 1. Introduction

Verifiable homomorphic computation sits on one algebraic object — a modulus and the ring
around it — that two research communities parameterize under different objective functions,
in different venues, without a shared search. The FHE literature selects ciphertext moduli
for noise budget, RNS decomposition, and negacyclic NTT efficiency at ring dimensions of a
few thousand. The proof-system literature selects fields for large 2-adic evaluation
domains, small-characteristic arithmetic cost, and FRI soundness. When the two stacks are
composed — proving that ciphertext operations were performed faithfully — one of the two
communities' choices is imported wholesale into the other's constraint system, and the
literature's uniform answer is to pick a field from the proof menu and ask the FHE scheme
to live with it. Every verifiable-FHE system we surveyed chooses from the same short list:
Goldilocks, BabyBear, 2¹⁶+1, or a generic RNS tower `[C1 · SOURCED — enumeration gate G5]`.

This is not merely an aesthetic complaint; the constraint binds in production. Zama's
deployed verifiable-FHE scheme (eprint 2026/027) proves over Goldilocks, whose
multiplicative group contains a 2-adic subgroup of order exactly 2³². Their instance-size
bound D·t·n ≤ 2³¹ is a direct consequence: at the implementation's rate (log_rho_inv = 1)
the next doubling requests an evaluation domain of size 2³², `Domain::new` returns `None`,
and the `.expect` in `WhirConfig::new` panics — reproduced by execution at a pinned commit
`[C2 · MEASURED — G1 closed 2026-08-13]`. The flagship deployment of this research area
has **one doubling of headroom**, imposed by a modulus chosen before anyone checked the
proof-side domain it would eventually need.

The joint problem has been *posed* before, and we want to be precise and generous about
that. HELIOPOLIS (eprint 2023/1949, §6.2) derives a genuine two-sided feasibility region
relating FHE and PCS parameters. Eprint 2025/286 states exactly the tension above and
resolves it by weakening the proof commitment scheme rather than moving the modulus —
a legitimate branch of the same fork; we take the other one. And at least six systems
papers adopt an existing proof-side prime as an FHE modulus, which is a one-sided answer
to the right question `[C1 · SOURCED — G5]`. What does not appear anywhere, to our
knowledge, is the *search*: no paper enumerates the moduli satisfying both communities'
constraints and picks a winner, and the proof-side notion of 2-adicity does not appear in
any FHE paper in a 25,765-paper corpus sweep (39 hits total, none FHE) `[C1 · COMPUTED —
corpus pin gate G6]`.

This paper runs that search and reports everything it found, including the negative
results, which we consider results. Concretely:

- **The joint constraint system** (§2): the decision variables — prime, conductor,
  encoding, plaintext modulus, limb structure — and the quantified constraints each side
  imposes, in one table.
- **The census** (§3): the constraint space is comfortable. Solinas primes 2ᵃ−2ᵇ+1 with
  a ∈ [96,130]: 117 primes, 93 with 2-adicity ≥ 20 `[C3 · COMPUTED:
  paper/scripts/verify_candidate.py]`. A word-granular cost model locates the optimum just
  under 64 bits `[C3 · PENDING — artifact gate G10]`.
- **The candidate and its family** (§4): p = 2⁶¹ − 2⁵⁴ + 1 = 127·2⁵⁴ + 1 — KoalaBear one
  machine word up — with 2-adicity 54, NTT to 2⁵³, Goldilocks-class fold reduction plus
  three lazy-reduction bits (the fold *shape* only; no barrel-shift twiddles), and maximal
  3-adic inertia, which Goldilocks and BabyBear fail `[C4 · PROVED-IN-LEAN]`. The inertia
  is an instance of a family law: for prime 127·2ⁿ+1, maximal inertia ⟺ n ≡ 0, 2 (mod 6)
  `[C5 · PROVED-IN-LEAN — failing branch exhibited at n = 214]`.
- **The experiment** (§5): the modulus swap in the deployed kernel — mechanism confirmed
  by execution (domain ceiling 2³² → 2⁵⁴), 10–40% faster on one machine at equal proof
  sizes, and **not** one line; the distance between those two facts is the section's core
  `[C6 · MEASURED — G3 closed]`.
- **The negatives** (§6): barrel-shift twiddles — Goldilocks stands alone among Φ_m(2ᵇ)
  primes at 64–160 bits with 2-adicity ≥ 9, a bounded scan, not a theorem; Crandall
  primes are structurally excluded; NTT-inside-FRI-domain is novel and worthless `[C7]`.
- **The security-model reconciliation** (§7): the same deployed parameters read 130.5 bits
  under the HE-standard model and 98.1 under core-SVP; every "128-bit" claim in this area
  is a model choice, usually unstated. Ours is stated `[C8]`.
- **The artifact** (§8): every parameter property as a machine-checked Lean theorem with a
  pinned axiom footprint, including the domain-availability lemma whose *negative*
  instance is the production panic of §1 `[C9 · PROVED-IN-LEAN — minidregg @ 641ceeb]`.

One scoping note. A second gap adjacent to this work — hashing inside the ciphertext ring
— is real but has no cryptanalysis yet and is not part of this paper (§10, one sentence).

## 2. The joint constraint system

*Bullet draft. Deliverable: one quantified table the reader can re-derive.*

Decision variables (from notes/joint-representation.md, restated for the paper):
- **the prime p** — size (noise budget), 2-adicity (NTT and FRI domains), algebraic form
  (reduction cost), ord_p(2) (twiddle cost)
- **the ring conductor** — power-of-two vs Φ_{3^k}; decides inertia/splitting behavior and
  lattice-commitment compatibility
- **the encoding** — coefficient vs slot vs hybrid; decides whether rotations exist at all
  (the deployed workload's matvec closes rotation-free under a *proven* bound — see
  metatheory/Bfv/Noise.lean matVecCt/RowBound `[C6-adjacent · PROVED-IN-LEAN]`) — and,
  per C6.2, decides the noise floor: the clean 55–59-bit floor of row 2 assumes fhe.rs's
  exact-division encoding, and p61 mod t ≈ 0.95t is near-worst for textbook-Δ BFV
- **the plaintext modulus t** — nonlinearity degree, batching, transcipher compatibility
- **the limb structure** — RNS tower vs single prime

Constraint table (each row gets a number and a tag):

| # | constraint | side | quantity | tag |
|---|---|---|---|---|
| 1 | ciphertext modulus security floor | FHE | 31-bit structurally excluded; floor ≈ 37 bits | [C3 · SOURCED notes/two-rocks.md — G7 re-derivation] |
| 2 | noise budget at depth 1, int8 matvec | FHE | floor 55–59 bits (4-bit → 8-bit weights; fhe.rs sampled distributions, exact-division encoding); the 61-bit candidate clears 8-bit by 2.4 bits | [C6 · COMPUTED — G7 commits the derivation; bound shape PROVED-IN-LEAN: Bfv/Noise.lean step_noise_le] |
| 3 | negacyclic NTT, N = 4096 | FHE | 2-adicity ≥ 13 | [arithmetic, verify_candidate.py pattern] |
| 4 | negacyclic NTT, N = 8192 (depth 2) | FHE | 2-adicity ≥ 14; deployed limb q0 has 13 — cannot support | [C3 · SOURCED notes/two-rocks.md] |
| 5 | FRI/trace evaluation domain | proof | 2-adicity 25–32 wanted today; Zama bound D·t·n ≤ 2³¹ at adicity 32, rate log_rho_inv = 1 | [C2 · MEASURED — G1 closed] |
| 6 | arithmetic cost | both | step function in machine words; one word ⇒ p < 2⁶⁴ | [C3 · PENDING G10] |
| 7 | reduction cost | both | Solinas form ⇒ shift+fold; barrel-shift twiddles ⇒ Goldilocks only among Φ_m(2ᵇ) primes, 64–160 bits, adicity ≥ 9 (§6 — bounded scan) | [C7 · COMPUTED — artifact G8, blocked on G13/G14] |
| 8 | 3-adic inertia (lattice-commitment ring) | joint | ord₉(p) = 6 required; GL, BB fail (ord₉ = 3) | [C4 · PROVED-IN-LEAN — orderOf_p61_three_pow] |

- Frame honestly: rows 1–4 are the FHE side's veto set, rows 5–7 the proof side's, row 8
  the genuinely *joint* row that neither community checks.
- State plainly which constraints are hard (NTT legality, security floor) vs economic
  (reduction form, word count).

## 3. The search

*Bullet draft.*

- **Census, Solinas form 2ᵃ − 2ᵇ + 1, a ∈ [96,130]**: 117 primes; 2-adicity is exactly b,
  so filtering b ≥ 20 gives 93 `[C3 · COMPUTED: paper/scripts/verify_candidate.py, 29/29
  checks]`. Examples in the BFV-noise band: 2¹⁰⁸−2⁵⁰+1 (adicity 50), 2¹⁰⁹−2⁵⁸+1 (58),
  2¹⁰⁹−2⁶⁵+1 (65), 2¹¹³−2³²+1 (32) — all verified prime `[C3 · COMPUTED]`.
- ⚠ **Open reconciliation**: the census brief circulating internally says "104 Solinas +
  106 Proth" for the same band; our committed script finds 117 Solinas under the stated
  parameterization. Until the original census script is committed and the parameterizations
  reconciled, the paper quotes ONLY the script's numbers `[gate G4]`.
- **Proth-form census** (k·2ⁿ+1, small odd k): not yet committed; the family of §4 is the
  k = 127 slice `[PENDING G4]`.
- **The point of the census**: FHE negacyclic NTT at N = 4096 needs 2-adicity ≥ 13; FRI
  wants 25–32. Ninety-three primes clear BOTH by a wide margin in one Solinas band alone.
  The joint constraint is comfortable. Nobody had a single-prime candidate because nobody
  ran the query, not because number theory resists.
- **The one-word band and the cost step function**: arithmetic cost is a step function in
  machine words; crossing 64 bits doubles (and more) every multiply in both the NTT and
  the prover. So the optimum sits just under 64 bits, maximizing noise budget within one
  word — which is where the candidate lives `[C3 · PENDING G10 — commit the model]`.
- Negative found during the search, reported in §6: the Goldilocks barrel-shift twiddle
  trick does not transfer to the 96–130 band (ord_p(2) astronomically large for every
  candidate) — nor to p61 itself (ord_p61(2) ≈ 2⁵⁷ `[C4.6 · COMPUTED]`); Solinas form
  still buys shift-plus-fold reduction `[C7 · SOURCED notes/joint-representation.md]`.

## 4. The candidate and the family

*Bullet draft. Open with: "p = 2⁶¹ − 2⁵⁴ + 1 = 127·2⁵⁴ + 1 is the KoalaBear prime
(127·2²⁴ + 1) one machine word up: same Solinas shape, same cofactor."*

- **Prior art on the prime itself, stated in full**: p61 appears exactly once in the
  public record that we can find — a 2014 candidate-moduli table in a public Lisp NTT
  repository (stylewarning/lisp-random; comment-only output of a modulus-search tool,
  later carried into hypergeometrica's comments). It has never been an active modulus
  anywhere. The honest frame — **never deployed; once listed as a search candidate in
  2014** — costs nothing and is arguably more charming: the prime sits exactly where a
  modulus search looks, and has sat there unused for twelve years
  `[C4.7 · SOURCED — reference pins G5]`.

Property list (every row was a Lean-certificate obligation for §8; the lane landed —
minidregg `Theory/CyclotomicInertia.lean` @ 641ceeb):

| property | value | evidence | Lean theorem (landed) |
|---|---|---|---|
| primality | p = 2287828610704211969 | [C4 · PROVED-IN-LEAN] + verify_candidate.py cross-check | `p61_prime` — Lucas certificate checked in the kernel (`decide` through `powMod`/`powMod_eq`; no `native_decide`) |
| 2-adicity | 54 exactly | [C4 · PROVED-IN-LEAN] | `p61_sub_one` + `not_two_pow_55_dvd_p61_sub_one` |
| negacyclic NTT | N up to 2⁵³ (ω of order 2⁵⁴ with ω^(2⁵³) = −1 exhibited by script) | [C4 · PROVED-IN-LEAN] | `p61_mod_8192` + `p61_domain_exists` |
| FRI instance ceiling | 2⁵³ — 2²² × Goldilocks' 2³¹ | [C4 · PROVED-IN-LEAN (p61 half) + C2 · MEASURED (Goldilocks half)] | `p61_domain_exists` / `p61_no_domain_two_pow_55` |
| reduction | Goldilocks-class fold 2⁶¹ ≡ 2⁵⁴ − 1, plus 3 lazy-reduction bits (p < 2⁶¹); the fold *shape* only — **no barrel-shift twiddles: ord_p61(2) ≈ 2⁵⁷** | [C4 · COMPUTED; C4.6 · COMPUTED] | form identity `p61_eq_familyP` PROVED; the fold congruence itself is script-only — the one G2 residue (G12) |
| 3-adic inertia | ord₉(p) = 6 ⇒ Φ_{3^k} irreducible ∀k; GL and BB fail (ord₉ = 3) | [C4 · PROVED-IN-LEAN] | `maximalInertia_p61` / `orderOf_p61_three_pow` (via the family law); `P61Cyc81_isField` / `P61Cyc81_finrank` = 54 |

- **The family law** `[C5 · PROVED-IN-LEAN — familyP_maximalInertia_iff, minidregg @
  641ceeb]`: for p = 127·2ⁿ + 1 prime, maximal inertia at every 3^k ⟺ n ≡ 0, 2 (mod 6).
  Proof shape (now the machine-checked one): 127 ≡ 1 (mod 9) and 2ⁿ mod 9 has period 6,
  so p mod 9 walks a 6-cycle; n ≡ 1, 3, 5 give 3 | p (no primes at all,
  `not_prime_familyP_of_mod_six`), n ≡ 4 gives ord₉(p) = 2, n ≡ 0, 2 give p a primitive
  root mod 9, which lifts to every 3^k since (ℤ/3^k)* is cyclic.
- **Instances**: family primes at n ∈ {2, 12, 18, 24, 54, 72} for n ≤ 80, all inert —
  KoalaBear is n = 24, the candidate is n = 54 `[C5 · COMPUTED verify_candidate.py]`. The
  failing branch is *proved*, not just exhibited: the first family prime with n ≡ 4
  (mod 6) is n = 214 — a **67-digit prime** (`familyP_214_prime`, kernel-checked Lucas) —
  and inertia fails: ord₉ = 2 (`orderOf_familyP_214_mod_nine`) and Φ₉ splits into exactly
  three quadratic factors (`card_factors_9_familyP_214` — the factor count is the
  refutation witness). The ⟺ has exhibited teeth in both directions
  `[C5 · PROVED-IN-LEAN]`.
- One theorem, two deployed-relevant instances — **landed as such**: KoalaBear's inertia
  is re-derived as a corollary of the family law with the same statement as its direct
  proof (`orderOf_koalaBear_three_pow_of_family`; both derivations kept), and the
  candidate's is `maximalInertia_p61`. That is the shape §8 ships, and now does.
- Note n = 72 (a 79-bit, two-word family member, prime and inert, 2-adicity 72)
  `[C5 · COMPUTED]` — relevant to §10's unresolved ≥2-word band.

## 5. The experiment — the paper's empirical centerpiece

*Bullet draft, updated 2026-08-13: the lane landed. Verdict: **CONFIRMED on mechanism,
REFUTED on "one line"** — and the refutation is the thesis instantiated a second time,
inside the very artifact under study. All numbers `[C6 · MEASURED — G3 closed; artifact
bundle gate G15]`.*

- **Design, as registered before the run**: in the deployed encrypted matvec kernel at a
  pinned WHIR revision, swap `#[modulus]` to 2287828610704211969 and recompute the F2
  (quadratic-extension) constants. Predicted: the ν = 32 panic disappears; the ceiling
  moves; ~3 bits of noise-margin cost; lattice security improves. One line plus constants.
- **Confirmed by execution**: the panic is gone; the evaluation-domain ceiling moved
  **2³² → 2⁵⁴** (instance bound 2³¹ → 2⁵³ at rate log_rho_inv = 1); end-to-end
  prove/verify green to ν = 29.
- **Faster, with the caveat welded on**: p61 measured **10–40% faster** than Goldilocks
  at **equal proof sizes** — 61 bits leaves spare-bit headroom (lazy reduction,
  accumulator slack) that exactly-64 cannot have. Measured on one machine (M2 Max),
  interleaved runs; this is a feasibility observation, not a throughput claim, and the
  paper says so wherever the number appears.
- **Refuted: it was not one line.** Four hidden Goldilocks structures surfaced:
  1. the artifact's chosen generator — 2 is a quadratic residue mod p61;
  2. the F2 (quadratic-extension) constants;
  3. two test literals pre-reduced mod Goldilocks;
  4. the RLWE encode/decode was **Goldilocks-structural in two hidden ways** — a
     bit-shift decode that silently relies on 2⁶⁴ mod q being tiny, and `wrapping_add`
     through u64 — and **12/12 unit tests stayed green while decryption was garbage**.
  Repair: ~20 lines of textbook exact-division encode/decode, field-generic by
  measurement (13/13 on both fields).
- **Noise, corrected and tight** `[C6.2 · COMPUTED — derivation commits at G7]`: the
  measured floor is **55–59 bits** (4-bit → 8-bit weights, fhe.rs's actual sampled
  distributions). At 8-bit weights the 61-bit candidate clears the 59-bit floor by
  **2.4 bits** — tight, and we present it as tight; 4-bit weights are the comfortable
  case. The clean floor depends on fhe.rs's **exact-division encoding**: p61 mod t ≈
  0.95t is near-worst for textbook-Δ BFV, so the encoding is part of the claim and the
  paper states it. (An earlier internal figure of 51 bits used the weight bit-width as
  its magnitude — a 16× ℓ1 understatement; 51 is really the ~4-bit-weight figure.)
- **Security improves, as predicted**: candidate core-SVP **213.7 (β = 732)**
  `[C6.3 · COMPUTED — estimator pin G7]`. (An earlier draft number, 205, was stale and
  matches no script.)
- **"What was not one line" is the section's core, not an appendix.** An artifact built
  around the claim that representation choices propagate into deployed systems unexamined
  was itself carrying four unexamined Goldilocks commitments — one of which passed its
  entire test suite while decrypting garbage. That is the paper's thesis with a second,
  self-referential witness, and we report it at full resolution.

## 6. Negative results, reported as results

*Bullet draft.*

- **Barrel-shift twiddles: Goldilocks stands alone — restated with its true scope**
  `[C7.1 · COMPUTED — red-team re-scan; artifact G8, blocked on G13/G14]`. Our first
  formulation — "the unique barrel-shift prime in 65–160 bits" — was **false twice
  over**: Goldilocks is a 64-bit prime, outside the claimed window, and 37 primes of the
  form Φ_m(2ᵇ) exist in 65–160 bits. The true statement: **among primes Φ_m(2ᵇ) in
  64–160 bits with 2-adicity ≥ 9, Goldilocks is unique** — and it is of the form six
  ways over: Φ₆(2³²) = Φ₁₂(2¹⁶) = Φ₂₄(2⁸) = Φ₄₈(2⁴) = Φ₉₆(2²) = Φ₁₉₂(2). Scoped
  honestly: the form is **sufficient, not necessary**, for shift twiddles — prime
  *factors* of Φ_d(2) qualify too (the 73-bit factor of F₇ is a live example) — so the
  capability-level statement is a **bounded scan, not a theorem**. The consequence
  survives in spirit: a modulus move away from Goldilocks forfeits shift-only twiddles
  knowingly — and **p61 has no barrel-shift capability of its own** (ord_p61(2) ≈ 2⁵⁷);
  nothing in the family inherits it `[C4.6 · COMPUTED]`.
- **Crandall primes 2ᵏ − c are structurally excluded**: 2-adicity of p − 1 equals
  v₂(c + 1) ≤ 12 for c < 4096 — a one-line argument, script-checked
  `[C7 · COMPUTED verify_candidate.py]`.
- **The shift-twiddle trick does not transfer to 96–130 bits**: every census candidate has
  astronomically large ord_p(2) — as does p61 itself (§3, C4.6); Solinas form still buys
  shift-plus-fold reduction `[C7 · SOURCED notes/joint-representation.md — G10]`.
- **NTT-domain-inside-FRI-domain: novel and worthless.** Absent from a 25,765-paper corpus
  `[COMPUTED — G6]`, and not worth building: NTT is 0.27% of the reference prover's time
  (73% is gadget decomposition) `[C7 · MEASURED by lane — harness pin G9]`, the matvec
  reduction is provable as a one-line committed-quotient identity anyway, and
  coset-separation zero-knowledge is forfeited. We report it so nobody else builds it.

## 7. Security models: what "128-bit" means here

*Bullet draft. Tone: neutral, reproducibility-first. Nothing in this section is an attack.*

- The same deployed parameters, under the **actual sampled secret distribution**, read
  **130.5 bits under the HE-standard model and 98.1 under core-SVP** — a ~32-bit spread
  that is entirely the model, not the parameters; estimator validated against
  Kyber-768/1024, and the reconciliation is **closed to the 2019 HE standard's own
  formula and table row** `[C8 · COMPUTED — red team; estimator pin G7]`. (Earlier
  internal figures of 127.9/95.5 were computed under a mislabeled secret distribution —
  see the third bullet; the model-spread claim is unchanged by the correction.)
- Zama 2026/027's "~100 bits" reads 104.6 / 74.2 under the same two models `[C8 ·
  COMPUTED — G7]`.
- Adjacent honesty about our own stack, one paragraph: the deployed secret is **centered
  binomial with parameter η = 20 — support ±20, variance 10 (σ = √10)**. Earlier internal
  notes recorded it as "ternary" and as "CBD(10)"; **both were misreadings** (the 10 is
  the variance, not the parameter or the support), which is itself a small argument for
  this section's thesis: distributions must be stated unambiguously because estimator
  outputs depend on them. Threshold shares are ternary — two distributions in one tree.
  Under the actual distribution the readings are the 98.1 / 130.5 above; figures derived
  under the misread labels (a ~4.3-bit B_key gap, MATZOV ≈ 122) are superseded pending
  the G7 re-run `[C8.4 · SOURCED + COMPUTED — G7 re-runs both shipped distributions]`.
- Reproducibility observation, reported neutrally: the code accompanying 2026/027 samples
  **binary** secrets; the paper does not state the secret distribution. We note it because
  estimator outputs depend on it, and leave interpretation to the reader `[C8 · SOURCED —
  file/line pin G11; NOT an attack claim]`.
- The section's thesis: every security number in this paper carries its model tag **and
  its secret distribution**, and we recommend the area adopt the practice. This costs
  nothing and dissolves a recurring ~30-bit ambiguity.

## 8. The artifact: machine-checked parameter certificates

*Updated 2026-08-13: the Lean lane landed in full — minidregg
`Theory/CyclotomicInertia.lean` @ commit **641ceeb** (+697 lines on the KoalaBear base).
Zero `sorry`, zero named obligations, **no `native_decide`**; axiom footprints pinned
in-file at most [propext, Classical.choice, Quot.sound]. `[C9 · PROVED-IN-LEAN]`*

- Shipped as named theorems a consumer can import (no `#guard`-style unnamed checks):
  - **the family law, verbatim**: `familyP_maximalInertia_iff` — for prime 127·2ⁿ+1,
    maximal 3-adic inertia ⟺ n ≡ 0, 2 (mod 6); `maximalThreeAdicInertia_iff_irreducible`
    ties the order statement to Φ_{3^{k+1}} irreducibility;
    `not_prime_familyP_of_mod_six` closes the no-prime branches
  - **p61, fully certified**: `p61_prime` — a Lucas certificate **checked in the kernel**
    (`decide` through a fueled `powMod` with correctness theorem `powMod_eq`);
    `p61_sub_one` + `not_two_pow_55_dvd_p61_sub_one` (2-adicity exactly 54);
    `p61_mod_8192`; `maximalInertia_p61` / `orderOf_p61_three_pow`; the conductor-81
    field `P61Cyc81_isField` / `P61Cyc81_finrank` = 54
  - **the counterexample, with teeth**: `familyP_214_prime` (67 digits, Lucas again —
    p − 1 = 127·2²¹⁴ factors by construction), `orderOf_familyP_214_mod_nine` = 2,
    `card_factors_9_familyP_214` — Φ₉ splits into exactly three quadratic factors; the
    family ⟺ is exhibited in both directions
  - KoalaBear re-derived as a family corollary with the same statement as its direct
    proof: `orderOf_koalaBear_three_pow_of_family` (both derivations kept)
  - **the domain-availability lemma** — `exists_subgroup_card_eq` /
    `not_exists_subgroup_card_eq`, parameterized over (p, d); positive at p61
    (`p61_domain_exists` to 2⁵⁴, `p61_no_domain_two_pow_55`) and **negative at
    Goldilocks: `goldilocks_no_domain_two_pow_33` IS the production panic of §1, stated
    as mathematics** (`goldilocks_prime` proved en route, Lucas witness 7)
- **One residue, stated plainly**: the Solinas fold congruence 2⁶¹ ≡ 2⁵⁴ − 1 (mod p) is
  still script-checked only (verify_candidate.py), not a named theorem — a two-line
  addition tracked at G12's final audit.
- The artifact's claim is calibrated precisely: these are *certificates of the parameters'
  algebraic properties*, not a verified FHE scheme and not verified FRI soundness. Say so
  in one sentence and do not let the phrase "machine-checked" leak wider than this.
- Release: repo + pinned toolchain + the verify_candidate.py cross-check — the script and
  the theorems check the same facts through independent evaluators, and now both exist.

## 9. Related work (generous by design)

*Bullet draft — this section IS claim C1; state it so a HELIOPOLIS author would call it fair.*

- **Posed the joint problem**: HELIOPOLIS (2023/1949 §6.2) — a real two-sided feasibility
  region between FHE and PCS parameters; full credit as the first joint statement.
  Eprint 2025/286 — states precisely the tension this paper addresses and takes the other
  branch (weaken the PCS to fit the modulus); our work is the complementary branch (move
  the modulus to fit the PCS), and both should exist `[C1 · SOURCED]`.
- **One-sided adoptions**: ≥ six papers adopt an existing proof prime as an FHE modulus
  (Zama 2026/027 ciphertext-side; GBFV plaintext-side; four more to enumerate — gate G5)
  `[C1 · SOURCED, enumeration incomplete]`.
- **The prime itself has prior art, and we cite it**: a 2014 candidate-moduli table in
  stylewarning/lisp-random (comment-only output of a modulus-search tool; later carried
  into hypergeometrica's comments) lists p61 among NTT modulus candidates — never
  deployed, never active. A search tool found it twelve years before we did; nobody
  picked it up, which is the two-communities claim in miniature
  `[C4.7 · SOURCED — pins G5]`.
- **The boundary fact**: 2-adicity — load-bearing on the proof side — appears in no FHE
  paper of a 25,765-paper corpus (39 hits, none FHE) `[C1 · COMPUTED — corpus pin G6]`.
- **Our delta, stated exactly**: the search (§3), the family and its law (§4), the
  measured binding constraint in a deployed system (§1/§5), and the machine-checked
  certificates (§8). Not the posing of the problem, which is prior work's.
- Also situate: proof-prime lineage (Goldilocks, BabyBear, KoalaBear — Plonky3 PR #329
  for the KoalaBear rationale; SP1's public rationale does not exist, per
  notes/field-choice-verdict.md `[SOURCED]`), and the FHE parameter-selection lineage
  (standard-model estimator practice).

## 10. Future work

- **The ≥2-word band is unresolved, and we say so**: depth-2 workloads want N = 8192,
  which the deployed RNS tower cannot support at all (limb q0 has 2-adicity 13
  `[SOURCED notes/two-rocks.md]`); any depth-2 move is a full limb re-choice at ≥ 2 words,
  where our cost model goes flat and the census (117 candidates, and family member n = 72
  `[COMPUTED]`) offers options but this paper offers no verdict.
- One sentence, exactly: a second representation-level gap — a hash that is native to the
  ciphertext ring rather than decompose-and-hash — appears open and is the subject of
  ongoing work with no cryptanalysis yet.

---

*Drafting conventions: tags `[Cn · STATUS]` resolve to CLAIM-LEDGER.md rows; STATUS ∈
{PROVED-IN-LEAN, MEASURED, COMPUTED, SOURCED, PENDING}. Gates Gn resolve to
SUBMISSION-GATES.md. Strip both at submission.*
