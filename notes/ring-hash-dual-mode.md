# Ring-hash dual-mode: is the absorb phase also our multilinear PCS?

2026-08-16. MATHEMATICS + DESIGN lane. The wildcard composition: two of our own threads that
nobody had put on one axis.

- **Thread 1** (`sumcheck-batched-opening.md` §0a, `[READ]`): the ×2.13 sumcheck endpoint is
  unreachable over two-adic FRI because *"a Merkle leaf supports no evaluation opening"* — the
  sumcheck's terminal claim is an MLE evaluation of the opened values, and the only commitment
  those values have cannot answer it. `galois-levers.md` §2b closed the same door from the
  composition side and named what would open it: *"an evaluation-binding commitment to V that
  travels — a multilinear PCS … or a homomorphic accumulator (Halo/IPA — a curve, foreign to
  this stack). Both are PCS replacements."*
- **Thread 2** (`ring-hash-design.md`, `ring-hash-cryptanalysis.md` PA3, `[READ]`): the ring-hash
  candidate's compressive core is R-SIS-linear — SWIFFT's `f(x) = Σ aᵢxᵢ`, *"exactly our
  problem, posed in 2008"* — with a ring-native de-linearizer (σ-layer / gadget-Feistel) bought
  precisely so the RO mode never leaves R_q.

**The question: is one primitive both?** A homomorphic, evaluation-friendly Ajtai commitment
(linear mode) and the Fiat–Shamir hash (full mode), sharing one parameter set and one cost table.
Every number below is `[READ]` at a named source, `[MEASURED]` (a computation run this session,
reproduce block at §8), or `[DERIVED]` (arithmetic on stated counts, labeled). Counts, not clocks.
Substrate said out loud: **nothing here authors a constraint anywhere** — this is mathematics,
counts, and Lean-statable forms; §6 names what would move first and in which language.

---

## 0. THE ONE-BREATH ANSWER

**Yes, the modes are compatible — one parameter set serves both, and it was found this session
(τ=2, q = 2^64 − 257, B = 2^16, K = 4; §5). The linear mode is the third entry behind
`galois-levers.md` §2b's door: an evaluation-binding commitment that is not a curve and not
hash-based — it is the hash's own absorb matrix.** The de-linearizer sits strictly after the
commitment read-out, so linear-mode openings never cross it (§2c), which is simultaneously what
keeps the KRS25 hash-delegation attack configuration out of reach (§5d).

**But the two readings of "does it pay" split, and the split is the verdict:**

| reading | verdict | arithmetic |
|---|---|---|
| **transplant into the BabyBear wrap** (replace two-adic FRI's reduced opening with sumcheck + lattice opening) | ⚑ **NO — dead twice over** | normalized to base-mults, the opening verify is ×0.7–×13 of the Horner chains it would replace (best case parity, §4c) — and `galois-levers.md` already reached ×2.011 of the ×2.13 target by table geometry alone, so the prize the PCS was priced against has largely been banked without it |
| **R_q-native artifact** (the lattice-folding world of 2026/1127, where the ring-hash lives anyway) | **YES — coherent and cheap at the margin** | the opening verify is 1.5–3.0×10⁴ R_q rows ≈ 16–33% of the gadget-Feistel FS bill it shares an artifact with (§4b), and it enables absorb-volume compression (commit κ=24 ring elements instead of the vector; §4d) — the volume attack that `ring-hash-build-verdict.md` proved delegation could not make |

**And the honest asymmetry of the security story (§3): the modes share arithmetic, parameters and
a cost table — they do not share one assumption.** Linear-mode binding is provable (MSIS); full-mode
RO-likeness stays the ideal-permutation heuristic it always was. What is genuinely shared is the
one-way implication (a collision in the linear core breaks both modes at once), the parameter set,
and the pleasing self-reference of §4b: the full mode prices the transcript of the linear mode's
own opening protocol, so every row shaved off the hash cheapens the commitment's openings too.

A correction carried from the brief: the σ-Poseidon bar figure **302,141 is the τ=4 point**
(`ring-hash-design.md` §5.0). The standing τ verdict is **τ=2** (`ring-hash-tau-verdict.md`), where
the same table gives **363,513** (= 3,372.1 ring elements/step × 107.8). Both quoted below.

---

## 1. The two threads at source, and what moved since the brief

### 1a. The Merkle-leaf obstruction `[READ]`

`sumcheck-batched-opening.md` §0a: a sumcheck batching `Σ_k α^k v_k` over the ~390,716 opened
values terminates in a claim `Ṽ(r) = c` about the MLE of those values. The verifier has two
discharge routes — recompute Θ(N), or open from a commitment — and the only commitment is the
child's MMCS Merkle leaf, which supports univariate/positional openings only. Verbatim: *"lever
3(b), as stated, is not a prover-side rearrangement — it is a PCS replacement."* This is Neo's
whole world seen from the other side: `neo-verdict.md` records that Neo's fix for the identical
wrap identity is *"stop being hash-based"* — **Ajtai commitments open no Merkle paths**, and we
are literally the row Neo labels Arc.

### 1b. ⚠ The goalposts moved after the brief was written `[READ]`

`galois-levers.md` (this repo, commit `e5700e2`) showed the ×2.13 **cell** endpoint is reachable
*without* a PCS: the deployed packing is ×1.400 from its own family's minimum (a4/K16: 40,554,496
→ 28,971,008 wrap cells, ×2.011 cumulative, `[MEASURED]` there), and a dedicated chain table
prices to ≈×2.23 `[DERIVED]` there. So the brief's comparison target — "the Horner chains it
would replace (216,330 HornerAcc post-split …, packing to ~29.0M wrap cells measured)" — is a
target the geometry lever already substantially reached. **Any wrap-side case for a lattice PCS
must now beat the residual, not the original**, and §4c shows it does not beat even the original.

### 1c. The R-SIS-linear core `[READ]`

`ring-hash-cryptanalysis.md` PA3: SWIFFT `f(x) = Σ aᵢ·xᵢ` over Z_257[α]/(α^64+1) is collision-
resistant under R-SIS and *"not pseudorandom (at least as currently defined), due to linearity"*
— and SWIFFTX de-linearized it by **leaving the ring** (base-257→256 conversion + byte S-box),
which is why it cannot be arithmetized. Our design constraint, verbatim from that note:
*"de-linearize WITHOUT leaving R_q."*

⚠ **Premise check, stated rather than inherited**: "the absorb phase is R-SIS-linear" is true of
the **gadget-Feistel** candidate specifically — its round is gadget-decompose ∘ public-dense-affine,
with *all* nonlinearity in the P plane-products (`ring-hash-design.md` §3: at P=0 the round is
"linear-up-to-carries") — and true of σ-Poseidon only in the trivial sense that every sponge
absorb is additive. **The dual-mode construction below rides the Feistel branch.** If the
Feistel's three caveats kill it, the linear mode survives standalone as a plain gadget-Ajtai
commitment (§7, last bullet) — the brief's "linear mode alone may stand" clause.

---

## 2. Task 1 — both modes, stated precisely

Ring: R_q = Z_q[X]/(X^d+1), d = 16, q the joint modulus of §5 (τ=2: q = 2^64 − 257). Gadget:
base B = 2^16, K = 4 planes, B^K = 2^64, γ := B^K − q = 257. G : (R^K) → R the recomposition
map Y ↦ Σ_k B^k·Y_k; G⁻¹ the (norm-constrained, not everywhere unique — §2d) decomposition.

### 2a. Linear mode — the commitment

For a payload v ∈ R_q^{n_r} (equivalently N_Z = 16·n_r Z_q values; the *values are arbitrary
field elements* — shortness is manufactured by the gadget, never assumed of the data):

```
  Y  = G⁻¹(v + a₀)          ∈ R^{K·n_r},  ‖Y‖∞ < B          (planes; a₀ a public offset)
  C  = A·Y                  ∈ R_q^κ                            (the commitment)
```

with **A ∈ R_q^{κ × K·n_r} sampled uniformly** and published as part of the primitive's parameter
set. Positional opening: reveal (v_i, the plane column slice, nothing else is hidden — this is a
binding commitment, not a hiding one; hiding would be a separate mask, out of scope here).

- **Which A?** A *fresh uniform matrix in the same currency as the Feistel's round matrices* —
  same shape as the round-0 dense form F₀, domain-separated from it (§5d). Not the literal F₀:
  full mode's round matrices may be tuned; the commitment key must stay uniform for MSIS. A
  pleasant freebie `[DERIVED]`: a uniform A satisfies the C6-class subfield-avoidance condition
  (σ-fixed coefficients) except with probability ~ℓ·q^{−τ(ℓ−1)·…} ≈ negligible — the condition
  the σ-Poseidon layer must *check*, the commitment key gets by sampling.
- **Binding = MSIS, on the planes.** Two verifying openings Y ≠ Y′ with A·Y = A·Y′ and both
  ‖·‖∞ < B give A·(Y−Y′) = 0 with ‖Y−Y′‖∞ < 2B — an MSIS_{κ, 2B} solution. Binding *to v*
  follows because v = G·Y − a₀ is a function of the planes. **The norm story, honestly**
  (the brief's ⚠): binding holds **only on the short-plane subtype**. The range check
  ‖Y‖∞ < B is not free — it is **paid by the host** folding scheme's norm machinery
  (2026/1127's own ∞-norm checks; ProtoGaLattice's *"we need to add the cost of a range proof …
  for each of the witnesses"*). §5c prices what happens if it is forgotten: binding silently
  evaporates — so in the Lean form it is a structure field, not prose (§6).
- **κ estimate `[DERIVED — root-Hermite sketch, NOT a lattice-estimator run]`**: at q ≈ 2^64,
  ∞-bound 2B = 2^17, module dimension 16κ, a 128-bit core-SVP target needs κ ≈ 24 (κ = 16
  fails the same sketch). Carry `sis-lattice-verdict.md`'s warning before quoting any bits:
  the field's "128-bit" labels have re-derived to ~98-bit core-SVP before. The estimate's job
  here is the *cost table's κ*, not a security claim; the estimator run is obligation O6.
- **Payload-dependent K**: BabyBear-sized payloads (2^31 < B²) decompose into **K = 2** planes —
  half the commit width and half the absorb; full Z_q payloads need K = 4. Both rows appear in §4.

### 2b. Full mode — the hash

The existing candidate, unchanged: the sponge over the full permutation — gadget-Feistel at
NR = 16, P = 2, rate 7, capacity 1 (or σ-Poseidon as the fallback candidate), Fiat–Shamir per
`ring-hash-design.md`. The mode-level formal object already exists:
`~/src/ring-ro-hash/RingSponge.lean` (Tier 0, elaborates against minidregg HEAD) instantiates
Selvage's sponge mode at the R_q carrier with zero new hypotheses — the ring structure lives
entirely inside the permutation parameter, and `ringCap_card` computes the capacity bound's
denominator to q^{d·c}.

### 2c. ⚑ Where the de-linearizer sits — the design invariant that makes it one primitive

```
              v ──► G⁻¹ ──► planes Y ──► A·Y ──► C           ══ LINEAR MODE READS OUT HERE
                                          │
                                          ▼  (P plane-products, Feistel swap, NR rounds)
                                     de-linearizer π ──► digest   ══ FULL MODE ONLY
```

**Linear mode is the P = 0, round-0 projection of the gadget-Feistel round: one decomposition and
one public dense linear map. The de-linearizer — the plane-products and every subsequent round —
sits strictly after the commitment read-out.** Consequences, each load-bearing:

1. **Linear-mode openings never cross π.** Verifying an opening (or an evaluation claim, §4) is
   linear algebra over R_q plus norm checks; π appears in no verification relation.
2. **P is the mode switch.** The design note proved P = 0 is trivially distinguishable *as a
   hash* (fixed differentials propagate) — and that is fine, because the commitment mode never
   claimed pseudorandomness; it claims binding, which P = 0 retains in full.
3. **The KRS25 configuration is avoided by construction** (§5d): the proven statements contain
   the linear core only, never the FS hash function itself.

### 2d. The γ-ambiguity is asymmetric between the modes — and the asymmetry is good news

`ring-hash-design.md` §3: base-B decomposition constrained by "recomposes mod q + coefficients
< B" is non-unique for coefficients < γ. At the §5 modulus, γ/q = 2^−56.0 `[MEASURED]`, ~2^−52
ambiguous coefficients per ring element.

- **Full mode**: the ambiguity is a Fiat–Shamir grinding channel — a malicious prover picks the
  representative, each choice reroutes the hash. Priced into the ROM bound as ~Q·2^−52, exactly
  the design note's accounting. This is the mode the hazard was discovered in.
- **Linear mode**: the two representatives of a coefficient recompose to the **same** v — so the
  ambiguity produces two commitments *by the honest committer's choice*, and zero violations of
  binding-to-v (a collision needs two *different* v under one C, which is MSIS). Cost: `commit`
  is a relation, not a function — the Lean interface takes the plane vector as the witness and
  never pretends `G⁻¹` is canonical (§6).

---

## 3. The shared security argument — what is actually shared, said without inflation

| property | linear mode | full mode | shared? |
|---|---|---|---|
| collision resistance of the core `A·G⁻¹(·)` | **= MSIS_{κ,2B}, provable** | inherited as a floor: a core collision collides the sponge input injection | ⭐ **yes — one reduction serves both directions of the implication that matters** |
| position binding (openings) | from MSIS, on the short subtype | n/a | linear only |
| RO-likeness / indifferentiability | n/a (P=0 is *provably not* PR — by design) | ideal-permutation heuristic + NR=16 (borrowed, `ring-hash-design.md` §3 caveat 2) | **no — and saying otherwise would be the honest-label sin** |
| parameters (q, d, B, K, τ, challenge sets) | §5 | §5 | ⭐ yes, one set |
| cost table (R_q rows) | §4 | `ring-hash-design.md` §5.0 | ⭐ yes, one currency |

The precedent stack, for placement: **SWIFFT is the linear mode** (R-SIS binding, no RO),
**SWIFFTX is the full mode** (linear core + de-linearizer), and our contribution over both is
(a) the de-linearizer stays in R_q, and (b) **the linear core is not discarded as an internal
detail — it is exported as the commitment scheme**, so the folding stack needs one primitive
where it currently budgets two (an FS hash *and* an Ajtai commitment: 2026/1127 already carries
both separately — its App C.4 MSIS-hash *is* an un-exported linear mode, at a modulus where
γ/q = 0.159 makes the full-mode reading broken, per the design note's flag).

**Absence check, instrument named**: `grep -ril "dual.mode\|one primitive.*both\|absorb.*commitment"`
over `notes/` finds no prior statement of this composition; the eprint mirror is cryptology-only
and its full-text cache stops at 2026/777, so **no literature-wide absence is claimed** — the
claim is "not in our corpus," per the corpus-blindness preflight rule.

---

## 4. Task 2 — the evaluation opening, priced in R_q rows

The claim to discharge: for committed V (N_Z = 2^ν Z_q values), prove `Ṽ(r) = c` at a challenge
point r drawn from the strong sampling set (the diagonal F_{q^τ} copy, size q^τ = 2^128 at τ=2 —
the same τ that §5 fixes for the hash; `ring-hash-design.md` §5.1 already recorded that sumcheck
over R_q wants exactly this set). Two protocol shapes exist on the shelf; both are priced
`[DERIVED — structural round-shape counts on the stated protocols; no implementation exists]`,
with the ring-hash cost table as the currency (Feistel 27.4 rows/absorbed ring element,
σ-Poseidon τ=2 107.8; arithmetic: 1 ring mult = 1 row).

### 4a. Shape G — Greyhound (eprint 2024/1293), verified at the mirror copy `[READ]`

Greyhound at source: Ajtai commitment over a power-of-two cyclotomic (d = 64, q ≈ 2^32 in the
paper; ours transposes to d = 16, q ≈ 2^64), a three-round evaluation protocol with verifier
time O(√N), composed with LaBRADOR for succinctness — *"the verifier time for LaBRADOR is linear
in the size of the statement"*, statement size O(√N) ring elements, and its own drawback
statement: *"our verification time seems comparable with Brakedown and two times slower than
Ligero."* Proof size 53KB at N = 2^30.

In-circuit at N_Z = 2^19 (√-split into 181-ring-element chunks): absorb the ~50KB opening proof
= ~400 ring elements → **11.0k rows** (Feistel) / 43.1k (σ-P τ=2); tensor-vector builds + inner
products ≈ 0.9k rows; LaBRADOR verification arithmetic c_L·O(√N) with c_L unmeasured — call it
4k–18k. **Total ≈ 1.6–3.0×10⁴ rows, proof-absorption-led, with the LaBRADOR constant the soft
spot.** Batching (Greyhound §4.4 is a batched-evaluation section) amortizes the 50KB floor across
every claim in a step.

### 4b. Shape F — folding-style opening (the LatticeFold/2026/1127-native shape)

Sumcheck the ν variables of `Σ_x eq(r,x)·V(x)`; fold the commitment alongside, one κ-element
fresh commitment + 3 sumcheck coefficients absorbed per round; terminal check A·Y* = C* on a
short K-plane preimage. At ν = 19, κ = 24:

| component | rows |
|---|---:|
| sumcheck checks + commitment folds + value folds + terminal | ~650 |
| transcript absorb, 513 ring elements × 27.4 (Feistel) | 14,056 |
| norm-control overhead (per-round decomposition commitments, ×1–2 on absorb) | 0–14,056 |
| **total (Feistel hash)** | **1.5–2.9×10⁴** |
| total (σ-Poseidon τ=2 hash) | 5.6–11.1×10⁴ |

> ⚑ **The finding inside the table: the opening verify is ~95% transcript hashing.** The
> arithmetic of an Ajtai evaluation opening is nearly free in this cost model; what costs is
> absorbing the opening protocol's own messages — which the full mode prices. **The dual-mode
> artifact is self-referential in the right direction: every row shaved off the hash cheapens
> the openings of its own commitment mode.** (Feistel vs σ-Poseidon changes the opening bill by
> ×3.8 — the same ratio as the FS bills themselves.)

Both shapes land at the same order: **1.5–3.0×10⁴ R_q rows ≈ 16–33% of the gadget-Feistel FS
bill (92,396 rows), ≈ 4–8% of the σ-Poseidon τ=2 bill (363,513).** The marginal cost of giving
the transcript's committed vectors an evaluation opening is a fraction of the hash bill the
artifact already pays.

### 4c. ⚑ Against the Horner chains — the comparison the brief asked for, and it is a refusal-with-arithmetic

The Horner chains are **216,330 HornerAcc ops in a BabyBear-ext circuit**; the opening is
**R_q rows**. These are different substrates and there is no honest single conversion — so here
is the range, with both ends' assumptions named `[DERIVED]`:

```
  Horner chains:  216,330 ext4 MACs × ~10 base mults each        ≈ 2.16×10⁶ BabyBear-mult-equiv
  Shape F:        1.5–2.8×10⁴ R_q rows × (100 … 1024) equiv/row  ≈ 1.5×10⁶ … 2.9×10⁷
                  (100: CRT-slot representation, Karatsuba per F_{q²} slot, 64-bit≈4×31-bit;
                   1024: schoolbook d² negacyclic, same mult conversion)
```

**Ratio ×0.7 – ×13 — parity at the most favorable representation, an order worse at the
deployed-style one.** And the comparison is *already unfair in the lattice side's favor*: it
prices no witness generation, no substrate migration (the whole R_q proof system the wrap does
not have — `PROVEN-IN-LEAN ≠ ROUTABLE`'s grep test fails maximally here), and it competes
against a target `galois-levers.md` already cut ×1.400 further by geometry (§1b). **The
wrap-transplant reading is dead: not by taste, by arithmetic.** What would flip it: an R_q-native
recursion substrate (Neo's world) — at which point there are no Horner chains and no two-adic
FRI at all, and the question dissolves rather than resolves (§7).

### 4d. What the linear mode buys in its own world — the absorb-volume lever

In the R_q IVC, the FS bill is **volume** (3,372 ring elements/step absorbed; the build-verdict's
whole thesis). A transcript vector of n_r ring elements that is *committed* (linear mode) instead
of absorbed costs κ = 24 absorbed elements plus its share of one opening. Break-evens `[DERIVED]`:

- **one-shot** (vector opened alone): pays at n_r > ~535–1,046 ring elements (8.6k–16.7k Z_q
  values) — only the largest transcript objects qualify;
- **amortized** (all claims folded first, one Shape-F opening per step — the natural folding
  usage): pays at **n_r > κ = 24 ring elements = 384 Z_q values**, which is most vector-shaped
  transcript traffic.

This is the systems argument delegation could not make (`ring-hash-build-verdict.md`: delegation
attacks unit cost, the bill is volume): **commitment attacks volume directly**, and it needs no
second primitive to do it — the committing map is the hash's own absorb core. ⚠ The FS-soundness
fine print is hazard §5b: absorbing C binds the vector only computationally, so the ROM analysis
of the whole transcript acquires an MSIS term. Named, not hand-waved.

---

## 5. Task 3 — parameter compatibility, and the hazards named before they bite

### 5a. ⭐ The joint modulus exists at τ=2, and it is strictly better than the τ=4 one — `[MEASURED this session]`

The design note's joint modulus 2^64−279 was searched under **τ=4** constraints; the standing τ
verdict moved to **τ=2** (`ring-hash-tau-verdict.md`), so the search was re-run under τ=2
constraints (ord₃₂(q) = 2; gcd(7, q²−1) = 1; γ minimal; primality). First hit:

```
  gamma= 257  q = 18446744073709551359 = 2^64−257   q mod 32 = 31   q mod 7 = 4   gamma/q = 2^-56.0
  (next candidates: gamma = 945, 1505, 1665, 1839 — all strictly worse; control re-verified:
   2^64−279 has ord_32 = 4, i.e. it is the tau=4 point, as recorded)
```

**q = 2^64 − 257 serves every requirement of both modes at τ=2**: ℓ = 8 slots F_{q²}; challenge
space q² = 2^128 (exactly the 128-bit target, no repetition); α = 7 legal (q ≡ 4 mod 7); Feistel
decomposition unambiguous except ~2^−52/element (γ = 257 < 279 — **two γ-candidates better than
the τ=4 modulus**, so the grinding channel is no worse); MSIS binding indifferent to τ. Script:
`notes/ring-hash-scripts/dual_mode_modsearch.py`. If the named SPN.ipynb experiment flips τ back
to 4, 2^64−279 resumes and everything else in this note survives with ℓ = 4.

The trilemma table, extended with the binding column the dual-mode question adds:

| | τ=1 | **τ=2** | τ=4 |
|---|---|---|---|
| challenge space q^τ (both modes' sumchecks) | 2^64 — insufficient | **2^128** | 2^256 |
| integral-property survival (full mode, 2025/932) | round 1 | **13** | 20 — worst |
| σ-Poseidon slot-MDS cost | 143.8/elt | **107.8** | 89.8 — best |
| MSIS binding (linear mode) | indifferent | **indifferent** | indifferent |
| strong-sampling soundness of the opening (§4) | marginal | **ample** | ample |
| joint modulus with tiny γ + legal α=7 | — | **2^64−257 ✓** | 2^64−279 ✓ |

**Verdict: no parameter divorce. τ=2 with q = 2^64−257 serves both modes**, and the linear mode
adds zero constraints to the τ fork — it is indifferent on the axis that is genuinely open.

### 5b. Hazard (b): the commitment must be BOUND into the transcript — the basis-binding class

`basis-binding.md`'s lesson transposes exactly: there, the ordered basis β was carried in the
clause and entered the sponge nowhere, guarded by a docstring its only inhabitant violated. Here
the analogous unbound objects would be **the key identity A and the geometry (κ, K, B, n_r)** —
an adversary who can substitute keys or reshape planes equivocates commitments without touching
MSIS. The rule, structural not prose: the FS input carries an enveloped, positional
`keyBinding = envelope(len κ ‖ len K ‖ len B ‖ keyDigest(A))` alongside every absorbed C, in
both challenge and query inputs — the same five decisions as `basisPrefix` (index-inside-frame,
one codec, one envelope). And the ROM accounting gains one term: FS-over-committed-transcript is
sound only against binding, so the transcript's extraction argument carries Q·ε_MSIS. **No new
class opens; the fix shape is on the shelf and it is the one that closed the last instance.**

### 5c. Hazard (c): the free-norm-check assumption — inherited, doubled, and made refutable

The Feistel's named risk — plane norms checked "for free" by the host's ∞-norm machinery — is
inherited by the linear mode **at the binding layer**, which is worse than inheriting it at the
cost layer: if no host norm check covers the opening's planes, binding does not degrade, it
**vanishes** (unbounded Y makes A·Y surjective per column block — every C opens to every v).
That is a fail-open gate, the house's named class. Two consequences:

1. the Lean interface (§6) carries the norm bound as a **structure field of the opening type**
   (a subtype), so an unchecked opening is unrepresentable rather than un-remembered;
2. the cost tables in §4 must be read as *conditional on the host already paying its norm
   checks* — in 2026/1127's world it does (its folding IS norm-checked); in any transplant the
   check must be priced in, and "free" re-labels to **HOST-PAID**.

Also inherited unchanged: **challenge operator norms.** Strong-sampling challenges (diagonal
F_{q²}) have unbounded coefficient norm, so commitment folding grows witness norms — the reason
LatticeFold-family schemes interleave decomposition steps. §4b's ×1–2 norm-control factor is that
machinery's price at our counts; the exact schedule is 2026/1127's own and is obligation O5.

### 5d. Hazard (KRS25): the delegation loop the design must never close

Symphony's flag (`ring-hash-design.md` §5.1): GKR-based SNARKs are attackable *"if we allow the
proven statement to compute the Fiat–Shamir hash function itself."* The dual-mode design avoids
the configuration **by the §2c invariant**: every proven relation (opening verification,
evaluation reduction, norm checks) is a statement about the *linear core only* — A, G, planes —
and π never appears inside a proven statement. The full mode hashes transcripts *about* the
linear mode; nothing proves the full mode. This must be kept as a design refusal, not a habit:
the moment someone delegates the sponge itself to the proof system, the KRS25 question reopens
and `ring-hash-design.md`'s warning against quoting delegation costs applies verbatim.

### 5e. Mode separation

A linear-mode commitment must never verify as a full-mode digest or vice versa: standard sponge
domain separation (a mode tag in the capacity's IV / distinct cSHAKE-style namespace, the same
mechanism the additive-FRI controllers use for `challengeDomainId`), plus distinct derivation of
A from the round-constant stream. One line of spec, zero rows of cost, and without it the two
modes' security arguments contaminate each other through shared oracles.

---

## 6. Task 4 — the Lean-statable form, against what the tree already holds

Two prior findings shape this section, and both are refusals of the obvious design:

- `ingredient-inventory.md` §1.4: `Selvage/Commitment.lean`'s `OpeningScheme (Root F ι Op)` is
  **fully carrier-generic** — four bare `Type*` parameters, no `Field`, no characteristic. It
  instantiates at R_q payloads as-is.
- `multilinear-pcs-verdict.md`: changing `openAt`'s index type to an evaluation point is **the
  KZG-shape mirror trap** — the evaluation opening is an *interactive reduction*, i.e. one
  `Rbr.Reduction` + `RbrKnowledgeSoundness` instance, not a new commitment abstraction. That
  verdict was written for hash-based PCSs; it holds here for the sibling reason: the lattice
  opening (§4) is a protocol, and `Rbr`/`Depth`/FS already compile protocols.

The sketch (names indicative; home `minidregg/Selvage/`, ~three files):

```lean
-- carrier, from ~/src/ring-ro-hash/RingSponge.lean (Tier 0, already elaborates):
--   abbrev Rq (q d : ℕ) [NeZero q] := Fin d → ZMod q

/-- Short plane vectors: the opening TYPE carries the norm bound, so an
    unchecked opening is unrepresentable (§5c), not un-remembered. -/
def Planes (q d m K B : ℕ) [NeZero q] : Type :=
  {Y : Fin (K * m) → Rq q d // ∀ i j, ((Y i j).val < B) }

structure DualModeSpec (q d κ m K B : ℕ) [NeZero q] where
  A       : Fin κ → Fin (K * m) → Rq q d      -- the shared absorb/commitment matrix
  a₀      : Fin m → Rq q d                     -- public offset (round constants, round 0)
  perm    : SpongeState q d → SpongeState q d  -- the de-linearizer π (P=2, NR rounds)
  keyBind : List UInt8                          -- structural key binding, §5b (not prose)

/-- LINEAR MODE: an `OpeningScheme` instance, the existing structure UNCHANGED.
    Root := Fin κ → Rq q d, F := ZMod q (Z_q payload view), Op := the plane slice. -/
noncomputable def linearMode (S : DualModeSpec q d κ m K B) :
    OpeningScheme (Fin κ → Rq q d) (ZMod q) (Fin (m * d)) (PlaneSlice q d K B) where
  commit f    := matVec S.A (decompPlanes f S.a₀)   -- any valid representative (§2d)
  openAt f i  := planeSliceAt f i
  verifyOpen rt i v o := recomposeAt o = v ∧ matVecColumn S.A o rt
  verifyOpen_commit := …                             -- completeness, constructive

/-- The MSIS hypothesis, query-counted per `reference-grounding-efficient-adversaries`
    (no `_from_polyTime` vacuity): -/
def MsisHard (q d κ cols B bound : ℕ) : Prop := …    -- named, external, honest

/-- Obligation O1 — the reduction. The conclusion is the EXISTING `PositionBinding`;
    nothing downstream re-types. -/
theorem linearMode_positionBinding (h : MsisHard q d κ (K*m) (2*B) t) :
    (linearMode S).PositionBinding := …

/-- FULL MODE: RingSponge.lean's `ringSponge S.perm iv`, with `SpongeIndiffGame` as the
    stated-not-proved residual its own docstring already declares. Nothing new to state. -/

/-- THE WELD — the theorem that makes it ONE primitive: the sponge's input injection
    factors through the commitment core. `π ∘ inject = π ∘ (pad ∘ commitCore)`, with
    `commitCore = linearMode.commit` DEFINITIONALLY (same `S.A`, same planes). -/
theorem absorb_factors_through_commit (S : DualModeSpec …) :
    spongeAbsorbRound S.perm S.A = fun st v => S.perm (injectRoot st ((linearMode S).commit v)) := …

/-- EVALUATION OPENING: one Rbr instance (Shape F, §4b) — claim (root, r, c) reduces
    round-by-round to claim (short preimage of the folded root). NOT a new openAt. -/
noncomputable def mleOpening (S : DualModeSpec …) : Rbr.Reduction := …
-- knowledge soundness enters as the hypothesis field of the instance:
--   RbrKnowledgeSoundness (mleOpening S) εopen     -- Obligation O4
```

**The honest obligation list** — each either a theorem of the model (terminal) or undone work in
its clothes (transmutable), labeled:

| # | obligation | status | class |
|---|---|---|---|
| O1 | MSIS ⇒ `PositionBinding` on the short subtype | undone; route exists — `sis-lattice-verdict.md` item 4's two-way ArkLib trade (their `LyubashevskySeiler` is 0-sorry and proves our named gap) | transmutable, days-to-weeks |
| O2 | sponge indifferentiability of π | **stated, not proved** — `RingHashPlan.lean`'s own honest label; the open pieces are ring-independent | terminal for now (the field's open problem), carried as the named hypothesis it already is |
| O3 | NR = 16 round count + the τ experiment (`SPN.ipynb` at our parameters) | named in `ring-hash-design.md` §4.5; **gates the full mode only** — linear mode is round-free | transmutable, hours (needs sage) |
| O4 | `RbrKnowledgeSoundness` of `mleOpening` (extraction through folds + norm growth) | undone; the hard half is the norm-aware extractor | transmutable, the substantial piece |
| O5 | the norm-control schedule (challenge operator norms, §5c) priced at our counts against 2026/1127's own decomposition machinery | undone; bounds the ×1–2 factor in §4b | transmutable |
| O6 | a real lattice-estimator run for κ at (q, d, 2B) | undone — §2a's κ=24 is a sketch | transmutable, hours |
| O7 | key/geometry transcript binding (§5b) as a `basisPrefix`-shaped splice + injectivity | undone; the closed basis-binding instance is the template | transmutable, days |
| O8 | mode domain separation (§5e) | spec line; zero cost | transmutable, trivial |

Nothing above is a conjecture-shaped wall except O2 — and O2 is precisely the residual the hash
already carried before the dual-mode question existed. **The dual-mode reading adds O1, O4–O8 and
removes nothing; its marginal formal surface is the commitment side, whose hardest item (O4) is
also the one with the richest prior art to lean on.**

---

## 7. Task 5 — the verdict, and what flips each half

**POSITIVE, in its home world.** The composition is real: the gadget-Feistel's round-0 core *is*
an Ajtai gadget commitment (§2c), the parameters want no divorce (§5a — τ=2, q = 2^64−257,
found this session, strictly better γ than the τ=4 point), the evaluation opening costs 16–33%
of the FS bill it rides beside (§4b), and the commit-instead-of-absorb lever attacks the volume
half of the bill that every delegation escape provably could not (§4d). **In the R_q lattice-
folding world, the FS-hash problem and the MLE-endpoint problem do collapse into one artifact.**
One artifact, one modulus, one cost currency, one Lean spec with eight named obligations.

**NEGATIVE, as a wrap-side rescue.** The brief's motivating arithmetic — beat 216,330 HornerAcc —
fails by ×0.7–×13 with the unit conversion stated (§4c), against a target the packing lever
already cut to 28.97M cells without new cryptography (§1b), and on top of an unpriced substrate
migration. The ×2.13-as-sumcheck figure stays behind the PCS door *in the BabyBear stack*; the
geometry route reached the same number and is landed-or-nearly.

**What flips the negative half**: a decision to move the recursion substrate to R_q folding
(Neo's world, Escape 0 of `ring-hash-design.md` §5.1 — explicitly a substrate choice above any
note's pay grade). The day that decision is taken, this note's artifact is the reason the new
world needs one primitive where every existing design budgets two — and the Merkle-leaf
obstruction dissolves rather than being solved, because nothing in that world is a Merkle leaf.

**What flips the positive half**: (i) the Feistel dying — its three caveats are live
(NR=16 borrowed; order-2 differential; free-norm-check). Then the linear mode **still stands
alone** as the multilinear-PCS-over-lattices answer (a plain gadget-Ajtai commitment + Shape-F
opening needs no de-linearizer at all — §2c consequence 2), and only the *shared-artifact* story
is lost, reverting to the two-primitive budget with the same parameters. (ii) A τ re-verdict to
τ=4 — survivable, §5a. (iii) The O5 norm-control price coming back ≫×2 — that would push the
opening toward the σ-Poseidon-hash column of §4b and squeeze the one-shot break-even; the
amortized lever (§4d) survives even that, since its threshold is κ, not the opening bill.

**The one-line through-line for the horizon file**: the hash's absorb matrix was a commitment key
all along; Merkle couldn't answer an evaluation claim, and the primitive we were already building
to *replace Merkle's hash* answers it natively — the two problems were one artifact wearing two
costumes, in the R_q world only, and the arithmetic says so in both directions.

---

## 8. Reproduce

```bash
# the tau=2 joint-modulus search (seconds; sympy):
python3 ~/dev/zkml-research/notes/ring-hash-scripts/dual_mode_modsearch.py
#   expected first hit: gamma=257  q=18446744073709551359  q%32=31  q%7=4
#   control line: 2^64-279 has ord_32=4 (the tau=4 point, as the design note records)

# cost-table arithmetic of §4 (pure arithmetic on stated counts, embedded in the script):
python3 ~/dev/zkml-research/notes/ring-hash-scripts/dual_mode_costs.py
```

Greyhound verified at the mirror: `~/dev/gh/forks/IACR-eprint-mirror/2024/1293.pdf` (Nguyen–
Seiler; abstract, §"verifier runtime" analysis pp. around the LaBRADOR composition, and the
"comparable with Brakedown" drawback sentence — all quoted verbatim in §4a). All other sources
are this repo's own notes, cited by section at point of use.
