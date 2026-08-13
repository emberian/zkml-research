# DRAFT — Rock 1: the joint representation paper

Status: scaffold, 2026-08-13. Abstract and introduction are full prose; sections 2–10 are
structured bullet drafts. Every number carries an inline provenance tag `[Cn · STATUS]`
resolving to a row of `CLAIM-LEDGER.md`; tags are stripped at submission. Rock 2 (the
ring-native hash) is out of scope except for one sentence in future work.

**Do not cite anything tagged PENDING as established. The ledger is the contract.**

---

## Title

Candidates, with a recommendation:

1. *Choosing the Modulus Together: Joint Parameter Selection for Verifiable Homomorphic
   Computation* — accurate frame, but generic; nothing in it survives as a handle.
2. *KoalaBear, One Word Up: NTT-and-FRI-Friendly Primes for Single-Modulus Verifiable FHE*
   — memorable and literally true (127·2⁵⁴+1 vs 127·2²⁴+1), but assumes the reader knows
   KoalaBear, and "single-modulus" oversells until the experiment lands (the deployed BFV
   tower is untouched by this paper's experiment).
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
TCHES is the alternate if the experiment (§5) grows into a real performance story, but our
centerpiece is a feasibility ceiling, not throughput, and TCHES expects implementation
depth we do not intend to build. RWC is worth a talk submission for reach; it is not
archival and does not replace CiC.

---

## Abstract (~200 words)

FHE implementations choose their moduli for noise budget and RNS efficiency; proof systems
choose their fields for NTT domains and FRI soundness — and the two choices are made by
different communities, independently. The cost is now measurable in a deployed system: the
verifiable-FHE scheme of Zama (eprint 2026/027) proves over the Goldilocks field, whose
2-adic subgroup caps instances at D·t·n ≤ 2³¹ — one doubling of headroom above its current
parameters, a ceiling imposed by a modulus chosen without consulting the proof-side domain
`[C2 · PENDING]`. We pose modulus selection as a joint problem and run the search neither
community has run. The space is comfortable, not tight: Solinas primes at 96–130 bits alone
give 117 candidates, 93 with 2-adicity ≥ 20 `[C3 · COMPUTED]`, and a word-granular cost
model places the optimum just below 64 bits `[C3 · PENDING]`. We propose p = 2⁶¹ − 2⁵⁴ + 1
= 127·2⁵⁴ + 1: 2-adicity 54, negacyclic NTT to length 2⁵³, Goldilocks-class reduction with
three spare bits, and maximal inertia at every power-of-three conductor, which Goldilocks
and BabyBear both fail `[C4 · COMPUTED/PENDING-Lean]`. The inertia property is one instance
of a family law for 127·2ⁿ + 1 `[C5 · COMPUTED/PENDING-Lean]`. A one-line modulus swap
moves a deployed encrypted matrix-vector kernel's ceiling from 2³¹ to 2⁵³ for ~3 bits of
noise margin, with lattice security improving `[C6 · PENDING — prediction, not result]`.
Every parameter claim ships as a Lean theorem with a pinned axiom footprint `[C9 ·
PENDING]`. We also report what fails: Goldilocks is the unique barrel-shift prime in
65–160 bits; Crandall primes cap at 2-adicity 12; NTT-inside-FRI-domain is novel but
worthless `[C7]`.

*(Drafting note: sentence two carries the one-doubling fact, per plan. The §5 sentence is
written as a result but MUST remain conditional until the experiment lane lands; if C6
fails, the abstract reshapes around the census + family + certificates.)*

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
bound D·t·n ≤ 2³¹ is a direct consequence: the next doubling requests an evaluation domain
of size 2³², and the domain constructor panics — a behavior we reproduced by execution
`[C2 · PENDING — red-team lane re-reproducing; first execution 2026-08-13]`. The flagship
deployment of this research area has **one doubling of headroom**, imposed by a modulus
chosen before anyone checked the proof-side domain it would eventually need.

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
  machine word up — with 2-adicity 54, NTT to 2⁵³, Goldilocks-class reduction plus three
  lazy-reduction bits, and maximal 3-adic inertia, which Goldilocks and BabyBear fail
  `[C4]`. The inertia is an instance of a family law: for prime 127·2ⁿ+1, maximal inertia
  ⟺ n ≡ 0, 2 (mod 6) `[C5]`.
- **The experiment** (§5): a one-line modulus swap in the deployed kernel, with a stated
  prediction and falsification condition `[C6 · PENDING — the empirical centerpiece]`.
- **The negatives** (§6): barrel-shift twiddles are take-Goldilocks-or-nothing; Crandall
  primes are structurally excluded; NTT-inside-FRI-domain is novel and worthless `[C7]`.
- **The security-model reconciliation** (§7): the same deployed parameters read 127.9 bits
  under the HE-standard model and 95.5 under core-SVP; every "128-bit" claim in this area
  is a model choice, usually unstated. Ours is stated `[C8]`.
- **The artifact** (§8): every parameter property as a machine-checked Lean theorem with a
  pinned axiom footprint, including the domain-availability lemma whose *negative*
  instance is the production panic of §1 `[C9 · PENDING]`.

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
  metatheory/Bfv/Noise.lean matVecCt/RowBound `[C6-adjacent · PROVED-IN-LEAN]`)
- **the plaintext modulus t** — nonlinearity degree, batching, transcipher compatibility
- **the limb structure** — RNS tower vs single prime

Constraint table (each row gets a number and a tag):

| # | constraint | side | quantity | tag |
|---|---|---|---|---|
| 1 | ciphertext modulus security floor | FHE | 31-bit structurally excluded; floor ≈ 37 bits | [C3 · SOURCED notes/two-rocks.md — G7 re-derivation] |
| 2 | noise budget at depth 1, int8 matvec | FHE | log q ≈ 54–61 sufficient (row-sum bound) | [PROVED-IN-LEAN shape: Bfv/Noise.lean step_noise_le; instance numbers G3] |
| 3 | negacyclic NTT, N = 4096 | FHE | 2-adicity ≥ 13 | [arithmetic, verify_candidate.py pattern] |
| 4 | negacyclic NTT, N = 8192 (depth 2) | FHE | 2-adicity ≥ 14; deployed limb q0 has 13 — cannot support | [C3 · SOURCED notes/two-rocks.md] |
| 5 | FRI/trace evaluation domain | proof | 2-adicity 25–32 wanted today; Zama bound D·t·n ≤ 2³¹ at adicity 32 | [C2 · PENDING G1] |
| 6 | arithmetic cost | both | step function in machine words; one word ⇒ p < 2⁶⁴ | [C3 · PENDING G10] |
| 7 | reduction cost | both | Solinas form ⇒ shift+fold; barrel-shift twiddles ⇒ Goldilocks only (§6) | [C7 · COMPUTED identities / PENDING scan G8] |
| 8 | 3-adic inertia (lattice-commitment ring) | joint | ord₉(p) = 6 required; GL, BB fail (ord₉ = 3) | [C4 · COMPUTED verify_candidate.py] |

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
  candidate); Solinas form still buys shift-plus-fold reduction `[C7 · SOURCED
  notes/joint-representation.md]`.

## 4. The candidate and the family

*Bullet draft. Open with: "p = 2⁶¹ − 2⁵⁴ + 1 = 127·2⁵⁴ + 1 is the KoalaBear prime
(127·2²⁴ + 1) one machine word up: same Solinas shape, same cofactor."*

Property list (every row is a Lean-certificate obligation for §8):

| property | value | today's evidence | Lean target |
|---|---|---|---|
| primality | p = 2287828610704211969 | [C4 · COMPUTED verify_candidate.py] | `p61_prime` (G2) |
| 2-adicity | 54 exactly | [C4 · COMPUTED] | `p61_sub_one` (G2) |
| negacyclic NTT | N up to 2⁵³ (ω of order 2⁵⁴ exhibited, ω^(2⁵³) = −1) | [C4 · COMPUTED] | NTT-legality cert (G2) |
| FRI instance ceiling | 2⁵³ — 2²² × Goldilocks' 2³¹ | arithmetic from row 2 + [C2] | domain-availability lemma (G2) |
| reduction | Goldilocks-class fold 2⁶¹ ≡ 2⁵⁴ − 1, plus 3 lazy-reduction bits (p < 2⁶¹) | [C4 · COMPUTED] | fold identity (G2) |
| 3-adic inertia | ord₉(p) = 6 ⇒ Φ_{3^k} irreducible ∀k; GL and BB fail (ord₉ = 3) | [C4 · COMPUTED; route exists: minidregg Theory/CyclotomicInertia.lean, `orderOf_koalaBear_three_pow` + `irreducible_cyclotomic_of_orderOf_eq_totient`] | `orderOf_p61_three_pow` (G2) |

- **The family law** `[C5 · COMPUTED both branches; PENDING Lean G2]`: for p = 127·2ⁿ + 1
  prime, maximal inertia at every 3^k ⟺ n ≡ 0, 2 (mod 6). Proof shape: 127 ≡ 1 (mod 9)
  and 2ⁿ mod 9 has period 6, so p mod 9 walks a 6-cycle; n ≡ 1, 3, 5 give 3 | p (no primes
  at all), n ≡ 4 gives ord₉(p) = 2, n ≡ 0, 2 give p a primitive root mod 9, which lifts to
  every 3^k since (ℤ/3^k)* is cyclic.
- **Instances, computed**: family primes at n ∈ {2, 12, 18, 24, 54, 72} for n ≤ 80, all
  inert — KoalaBear is n = 24, the candidate is n = 54. The failing branch is *exhibited*:
  the first family prime with n ≡ 4 (mod 6) is n = 214, and it fails (ord₉ = 2)
  `[C5 · COMPUTED verify_candidate.py]`.
- One theorem, two deployed-relevant instances: KoalaBear's inertia proof
  (`orderOf_koalaBear_three_pow`, already machine-checked) and the candidate's become
  corollaries of the family statement. That is the shape §8 ships.
- Note n = 72 (a 79-bit, two-word family member, prime and inert, 2-adicity 72)
  `[C5 · COMPUTED]` — relevant to §10's unresolved ≥2-word band.

## 5. The experiment — the paper's empirical centerpiece

*Bullet draft. ALL of this section is `[C6 · PENDING — experiment lane in flight]`. If the
prediction fails, the paper reshapes: the census, family, and certificates stand; the
"live constraint removed by one line" story does not.*

- **Design**: in the deployed encrypted matvec kernel, swap `#[modulus]` to
  2287828610704211969 and recompute the F2 (quadratic-extension) constants. One line plus
  constants; no new key material claimed until the lane confirms.
- **Predictions, falsifiable, stated before the run**:
  1. the panic at ν = 32 disappears;
  2. the instance ceiling moves 2³¹ → 2⁵³;
  3. cost: ~3 bits of noise margin (log q 64 → 61), against the row-sum noise bound whose
     Lean shape already exists (metatheory/Bfv/Noise.lean:264–287, matVecCt/RowBound/
     step_noise_le `[PROVED-IN-LEAN — the bound's shape, not this instance]`);
  4. lattice security *improves* (smaller q at unchanged dimension).
- **Falsifiers**: any hidden Goldilocks dependence in the kernel (constants, gadget
  decomposition widths, extension-tower choices) that makes the swap not-one-line; noise
  margin loss above prediction; security estimate not improving.
- **Reserved subsection: "What was not one line."** Whatever the lane finds beyond the
  modulus constant gets reported here at full resolution — this subsection is a selling
  point, not an appendix.

## 6. Negative results, reported as results

*Bullet draft.*

- **Goldilocks is the unique barrel-shift prime in 65–160 bits** `[C7 · lane result,
  notes/two-rocks.md; identities Φ₆(2³²) = Φ₁₂(2¹⁶) = Φ₂₄(2⁸) = GL COMPUTED
  verify_candidate.py; uniqueness scan PENDING G8]`. Consequence: shift-only twiddles are
  take-Goldilocks-or-leave-it — a theorem, not a scan — and any modulus move away from
  Goldilocks forfeits them knowingly.
- **Crandall primes 2ᵏ − c are structurally excluded**: 2-adicity of p − 1 equals
  v₂(c + 1) ≤ 12 for c < 4096 — a one-line argument, script-checked
  `[C7 · COMPUTED verify_candidate.py]`.
- **The shift-twiddle trick does not transfer to 96–130 bits**: every census candidate has
  astronomically large ord_p(2); Solinas form still buys shift-plus-fold reduction
  `[C7 · SOURCED notes/joint-representation.md — G10]`.
- **NTT-domain-inside-FRI-domain: novel and worthless.** Absent from a 25,765-paper corpus
  `[COMPUTED — G6]`, and not worth building: NTT is 0.27% of the reference prover's time
  (73% is gadget decomposition) `[C7 · MEASURED by lane — harness pin G9]`, the matvec
  reduction is provable as a one-line committed-quotient identity anyway, and
  coset-separation zero-knowledge is forfeited. We report it so nobody else builds it.

## 7. Security models: what "128-bit" means here

*Bullet draft. Tone: neutral, reproducibility-first. Nothing in this section is an attack.*

- The same deployed parameters read **127.9 bits under the HE-standard model and 95.5
  under core-SVP** — a ~32-bit spread that is entirely the model, not the parameters;
  estimator validated against Kyber-768/1024 `[C8 · COMPUTED by lane — estimator pin G7]`.
- Zama 2026/027's "~100 bits" reads 104.6 / 74.2 under the same two models `[C8 ·
  COMPUTED by lane — G7]`.
- Reproducibility observation, reported neutrally: the code accompanying 2026/027 samples
  **binary** secrets; the paper does not state the secret distribution. We note it because
  estimator outputs depend on it, and leave interpretation to the reader `[C8 · SOURCED —
  file/line pin G11; NOT an attack claim]`.
- Adjacent honesty about our own stack, one paragraph: the deployed secret is CBD(10)
  while threshold shares are ternary — two distributions in one tree, ~4.3 bits apart in
  any bound carrying B_key; MATZOV-model reading ≈ 122 `[SOURCED
  notes/fhe-core-theory.md — G7 re-run against both shipped distributions]`.
- The section's thesis: every security number in this paper carries its model tag, and we
  recommend the area adopt the practice. This costs nothing and dissolves a recurring
  ~30-bit ambiguity.

## 8. The artifact: machine-checked parameter certificates

*Bullet draft. All `[C9 · PENDING — Lean lane, gate G2]` except the named template.*

- Shipped as Lean theorems with pinned axiom footprints (`#assert_axioms` discipline; no
  `#guard`-style unnamed checks — each fact is a named theorem a consumer can import):
  primality, the family form, 2-adicity, NTT legality (the order-2⁵⁴ root exhibited),
  the Solinas fold identity, maximal inertia via the family law, and the
  **domain-availability lemma** — parameterized over (p, ν), whose positive instance at
  (p61, 53) is the candidate's ceiling and whose *negative* instance at (Goldilocks, 32)
  IS the production panic of §1, machine-checked.
- The template exists and is cited as such: minidregg `Theory/CyclotomicInertia.lean`
  (488 lines) already proves `orderOf_koalaBear_three_pow` and the general
  `irreducible_cyclotomic_of_orderOf_eq_totient` / `not_irreducible_cyclotomic_of_orderOf_ne_totient`
  pair — the exact route the p61 and family-law certificates instantiate
  `[PROVED-IN-LEAN — for KoalaBear, today]`.
- The artifact's claim is calibrated precisely: these are *certificates of the parameters'
  algebraic properties*, not a verified FHE scheme and not verified FRI soundness. Say so
  in one sentence and do not let the phrase "machine-checked" leak wider than this.
- Release: repo + pinned toolchain + the verify_candidate.py cross-check (the script and
  the theorems check the same facts through independent evaluators).

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
