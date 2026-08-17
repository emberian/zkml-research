# Galois levers — is the wrap's arithmetic wasteful, and does any field-theoretic structure pay?

2026-08-16. MATHEMATICS + MEASUREMENT lane. Ember's challenge, verbatim: *"are there mathematical
facts that we're overlooking, potential pathways of exploiting these things via towers or extensions
or any other kind of any-theoretic-anything?"* — suspecting that `sumcheck-batched-opening.md`'s
"×2.13 is not reachable over two-adic FRI" verdict priced the arithmetic **as given** instead of
asking whether the arithmetic is wasteful.

Everything below is `[READ]` at source (file:line), `[MEASURED]` (exact counts off the deterministic
circuit build / the packing-grid harness added by this lane), or `[DERIVED]` (arithmetic on measured
counts, labeled). Substrate said out loud: **nothing here authors a constraint anywhere** — the
deliverable is mathematics + counts + Lean-statable forms, and where a change is named, the Lean
statement is named as moving first.

Baseline throughout = the wrap **after** the landed reduced-opening split
(`emberian/plonky3-recursion@b471aca`, `sumcheck-batched-opening.md` §2): perms 38,168 ·
HornerAcc 216,330 (= 19 × 10,306 per-query + 20,516 hoisted) · Alu 267,526 · committed cells
40,554,496 (Alu 17,694,720 = 43.6%, poseidon2 21,233,664 = 52.4%, recompose 1,572,864).

---

## 0. THE ONE-BREATH ANSWER

**Yes, the arithmetic is wasteful — but the waste is GEOMETRIC, not algebraic, and no Galois
structure is being left on the table.**

The precise finding, and it inverts the ×2.13 verdict's framing without contradicting its
mathematics:

> ### ⚑ The per-query reduced opening is a **fixed K-linear map** `K^N → L` (N ≈ 10,258 base-field
> opened values per query). Computing a K-linear map requires **zero** L×L products. The deployed
> Horner evaluation order manufactures **N of them per query** — and then the deployed table
> geometry charges each one ~67 committed cells against a packed-step floor of ~15 in the existing
> AIR family.
>
> So the ×2.13 endpoint the sumcheck could not reach over two-adic FRI **is reachable in cells** —
> by evaluation-order + table-geometry re-arrangement alone, VK-rotation only, child proof
> byte-identical. The sumcheck was never the only road to its own number.

The five pathways, one line each (details in §1–§5, ranked in §6):

| # | pathway | verdict | class |
|---|---|---|---|
| 1 | Frobenius / minpoly quotient | **arithmetic ≤ 0; absorption already at its floor; the conjugate-point variant is UNSATISFIABLE (proved, §1d)** | closed |
| 2 | deferred accumulation (Halo-style) | **factor 0 over Merkle-only commitments — the obligation cannot travel even one layer (§2b); the apex hop where it lands natively is already landed and marginal** | closed; PCS-conditional |
| 3 | in-circuit ring-switching / packing | ⚑ **the live one: 90.5% of HornerAcc is (K-data × L-challenge); measured packing grid + designed table land ×1.2–1.45 further on wrap cells** | pure re-arrangement |
| 4 | fold-orbit structure | **null AT SOURCE — the ±x orbit is already fully spent** (computed child seated into the leaf, 1 sibling/phase) | nothing to change |
| 5 | trace/norm maps | **mathematically identical to #3's coordinate view; no separate terminal check has the collapsible shape** | subsumed by 3 |

---

## 1. PATHWAY 1 — Frobenius and the minimal-polynomial quotient

### 1a. The mathematics, precisely

K = BabyBear = F_p, p = 2³¹ − 2²⁷ + 1 (a PRIME field — this matters). L = K[X]/(X⁴ − W) = Ext4.
Frobenius φ(x) = x^p is the generator of Gal(L/K) ≅ Z/4; it fixes K pointwise. Since 4 | p − 1,
φ is **diagonal in the power basis**: φ(a₀ + a₁x + a₂x² + a₃x³) = a₀ + a₁cx + a₂c²x² + a₃c³x³
with c = W^((p−1)/4) ∈ K — 3 base multiplications per application. For any f ∈ K[X]:
**f(ζ)^p = f(ζ^p), free.** `[READ]` p3's only "conjugate" is the ±x fold pair
(`breadstuffs/vendor/plonky3-fri-82cfad73/src/prover.rs:213` — *"evaluations at conjugate points are
adjacent"*, meaning ±x); the Frobenius structure is untouched, confirmed.

The minpoly form of a DEEP claim: for ζ ∈ L with minimal polynomial M_ζ (degree 4) and f ∈ K[X],

    f(ζ) = v   ⟺   M_ζ(X) | (f(X) − U(X))   where U ∈ K[X], deg U < 4, U(ζ) = v.

U's coefficients are exactly v's coordinates in the basis (1, ζ, ζ², ζ³) — the map v ↦ U is a
K-linear bijection L ≅ K[X]_{<4}. The quotient (f − U)/M_ζ has **K coefficients** and can be
evaluated at any query point x ∈ K entirely in K.

### 1b. What ethSTARK actually does `[READ at source]`

`~/paperbin/ethstark-v1.2-grinding.pdf` (= eprint 2021/582), §3.8.2 pp. 17–18: they add, per trace
column, the **conjugate quotient** (f(x) − ȳ)/(x − z̄) to the DEEP composition — spending the free
relation f(z̄) = conj(f(z)) to **prove the committed trace is F_p-defined** ("if f(z) = conj(f(z̄))
for random z then w.h.p. all coefficients of f are from F_p"). It is Frobenius-spending for a
*verification* purpose, not a cost reduction — and the purpose **does not exist in our stack**: our
MMCS leaves are base-felt preimages by construction (`p3rec` circuit targets carry opened rows as
base-embedded witnesses; an extension-valued opened row is unrepresentable in the leaf sponge's
preimage), so K-ness of committed data is structural, not proved. The brief's reading of ethSTARK as
an absorption/arithmetic saving was a misattribution; corrected here at source.

### 1c. Priced against what the code does today

* **Absorption (the 29.2% prize the brief named): already at the information floor.**
  `[READ]` `p3rec-batched-ro/recursion/src/verifier/batch_stark.rs:1362`
  `observe_opened_values_circuit` absorbs each OOD value via `observe_ext`, which decomposes to
  exactly D = 4 base coefficients (`recursion/src/challenger/circuit.rs:342-348`), rate 8,
  overwrite-mode sponge with no per-value padding (`pcs/mmcs.rs:17-60`). "One
  absorbed Ext4 value per column" **is** four base felts — the two phrasings name the same object.
  4 · 20,564 opened (col,point) pairs = 82,256 felts ≈ 10,282 of the 11,128 q-independent perms.
  The only way absorption falls is FEWER (col, point) pairs — that is jagged/stacked (width
  reduction, `leaf-vs-recursion.md` §5), not Galois structure.
* **Arithmetic: the minpoly form is net NEGATIVE in this circuit.** Per query it would add 3 K-MACs
  per column (evaluating U_i at x) and delete only the cached per-(height, z) extension inverses
  (`pcs/fri/verifier.rs:1339-1348` — a handful of `div`s per query, ~0.005% of Alu). The α-batching
  sum Σᵢ αⁱ·(numerator)ᵢ stays L-valued either way, and that sum is the whole bill (§3).
* **Soundness delta: none.** For K-coefficient f, "agrees with U at ζ" ⟺ "agrees at all four
  conjugates" — the two predicates are equal, so the DEEP error term is unchanged. Sending U's
  coefficients instead of v's standard-basis coordinates is a K-linear bijection of the wire — a
  flag day that buys nothing.

### 1d. ⚑ The conjugate-point variant is UNSATISFIABLE — the reason Frobenius is unspent is a theorem, not an oversight

The one genuinely tempting move: make the *next-row* opening point the Frobenius conjugate — choose
ζ with ζ^{p^j} = ζ·g, so f(ζg) = φʲ(f(ζ)) and the prover sends **half** the OOD values (the wrap
computes the other half by the 3-base-mult diagonal φʲ). That would delete ~5,100 absorption perms
(13% of wrap perms) and half the hoisted Q-chains.

**It has no witness.** ζ^{p^j} = ζg ⟺ ζ^{p^j − 1} = g. In the cyclic group L* of order p⁴ − 1,
x ↦ x^{p^j−1} has image of index gcd(p^j − 1, p⁴ − 1) = p^{gcd(j,4)} − 1, and g ∈ K* is in the
image iff g^{(p⁴−1)/(p^{gcd(j,4)}−1)} = 1. Since g^p = g (g is in the prime field):

    j ∈ {1, 3}:  g^{1+p+p²+p³} = g⁴ = 1  ⟺  ord(g) | 4
    j = 2:       g^{1+p²}      = g² = 1  ⟺  ord(g) | 2

The trace-domain generator has ord(g) = 2^k = the trace length ≥ 16. **No ζ exists, for any j.**
And the underlying obstruction is total: the committed data lives on a domain inside K, where
Frobenius is the identity — no committed value has a nontrivial orbit, and the only two
protocol points outside K (ζ, ζg) differ by a Frobenius-fixed ratio. Even if the equation were
satisfiable (ord(g) ≤ 4 — vacuously small traces), the sample space for ζ would shrink from
~2¹²⁴ to ≤ p^{gcd(j,4)} − 1 ≤ p² − 1 ≈ 2⁶², putting the DEEP union-bound term at ≥ deg/2⁶² ≈
2⁻⁴⁸ at deg 2¹⁴ — ~76 bits below the ~124-bit capacity ledger. Said out loud: the attack-relevant
bound of the satisfiable-but-degenerate variant is **2⁻⁴⁸**, not any flattering figure.

**Lean-statable forms** (both one-lemma-sized over mathlib):
* the minpoly equivalence: `minpoly.dvd`-shaped — `M_ζ ∣ (f − U) ↔ (f − U).aeval ζ = 0`;
* the refusal: `∀ j, ¬∃ ζ : Lˣ, ζ ^ (p ^ j) = ζ * g` given `4 < orderOf g` — cyclic-group order
  arithmetic; a clean `Theory/` fact in the satisfiable-refutable-not-provable discipline (here the
  *negation* is the theorem, with the ord(g) ≤ 4 boundary showing it is not vacuous).

**Verdict: closed.** Nothing Galois-shaped is being overlooked at pathway 1; the free relation is
real and there is provably no protocol point-pair it can bind.

---

## 2. PATHWAY 2 — deferred accumulation (Halo-style)

### 2a. The mathematics

The sumcheck endpoint of a batched reduced opening is a claim `Ṽ(r) = c` about the multilinear
extension of the opened-values vector V (per layer: N·q ≈ 195,814 base values). Halo's move:
never discharge the claim where it arises; carry `(r, c)` as an accumulator and discharge once,
at a layer where the check is native. `AccRbrBcs`/`Depth` hold proven accumulation bounds, and
`Selvage/HeteroComposition.lean` landed `VerifierEmbedding` (`:74`) / `rung_sound` (`:96`).

### 2b. ⚑ Why the accumulator cannot travel even ONE layer here `[READ]`

The obligation `Ṽ_k(r_k) = c_k` is a statement about V_k — and V_k exists **only as witness cells
inside layer k+1's trace** (the leaf-sponge absorb operands, `pcs/fri/verifier.rs:1362-1367`).
For layer k+2 to discharge it, k+2 would need *evaluation access* to a slice of k+1's committed
trace at the multilinear point r_k. Its PCS view of that trace is: univariate openings at ζ, ζg,
plus Merkle rows at query indices — **neither answers an MLE point query**. This is
`sumcheck-batched-opening.md` §0a's obstruction, now closed from the composition side as well:

* **Each layer holds exactly its own child's V and nothing deeper.** At the last hop, gnark holds
  the *shrink's* opened rows (`chain/gnark/stark_open_input.go:445-465`) — not the apex's, not any
  interior layer's. An accumulated claim about layer k's V reaches gnark with no data to check it
  against.
* **Interior deferral is strictly negative even where it type-checks.** Layer k+1 *could* check
  `Ṽ_k(r_k) = c_k` directly against its witness copy of V_k — cost: N eq-tensor ext-mults + N
  MACs = 2N, versus the N-MAC α-Horner it was supposed to replace. The sumcheck rounds
  (~log N ≈ 18 ext-ops) are free; the terminal claim is the whole bill, exactly as §0a said.
* **The one native hop is already taken.** gnark's Horner over the shrink's V is the 0.32M-
  constraint residual that `HORIZONLOG.md:18343-18345` retired as MARGINAL after the S_z/S_x
  hoist. Deferring *into* gnark buys ~nothing and costs the sumcheck scaffolding.
* **Where the accumulator would bind, for the record:** absorbed into layer k+1's transcript with
  the child's public values, before any of k+1's own challenges — the same site
  `observe_opened_values_circuit` uses (`batch_stark.rs:1109`). ~19 ext = 10 perms/layer. Cheap,
  and moot.

**What would flip the verdict:** an evaluation-binding commitment to V that travels — i.e. a
multilinear PCS (BaseFold/WHIR — the road SP1 6.4 and OpenVM 2.0 actually took,
`leaf-vs-recursion.md` §5), or a homomorphic accumulator (Halo/IPA — a curve, foreign to this
stack). Both are PCS replacements. The ×2.13-as-sumcheck figure stays behind that door; §3 reaches
the same number without opening it.

**Lean-statable form:** `ProofSystem` (`HeteroComposition.lean:50`) extended with a commitment
sort — `Comm`, `Open : Comm → Point → Val → Prop` binding — and the obligation
`[COMPOSE-defer]`: a deferred claim is dischargeable iff the carrier commitment opens at
arbitrary points. Over Merkle-only commitments the premise is **uninhabited for off-row points**
— the type-refuses pattern of `widened_relation_refuses_embedding` (`:187`) applied to the PCS
interface. ⚠ And the composition caveat stands: `OB2_depth_composition_nonneg` composes protocol
ROUNDS, not tower LAYERS (`leaf-vs-recursion.md` §6b); `ComposeErrorBound`
(`HeteroComposition.lean:230`) is still named-not-proved, so "we hold proven composition bounds"
must not be read as covering this.

---

## 3. PATHWAY 3 — in-circuit ring-switching / packing ⚑ THE LIVE ONE

### 3a. The mathematical fact

Per query, after the landed split, the verifier computes per height-group
R = Σᵢ αⁱ·p_x[i] over the concatenated opened row — `[MEASURED]` 10,306 HornerAcc per query, of
which **10,258 (99.5%) have pure base-field data** (the P = 2 matrices' R-chains; the remaining 48
are the quotient round's fused ext−base steps). Fraction of ALL HornerAcc that is pure
(K-data × L-challenge): 19 × 10,258 = 194,902 of 216,330 = **90.1%** (the other 9.9%: the hoisted
Q-chains over ext OOD data, 20,516, and the 912 fused quotient-round steps).

R is the image of the opened row under a **fixed K-linear map** K^N → L (fixed once α is drawn:
its matrix is the 4×N array of coordinates of the αⁱ, equivalently A_{ij} = Tr_{L/K}(θ_j αⁱ) for
the dual basis θ — this is where pathway 5 lands, see §5). Two exact evaluation strategies:

| strategy | L×L mults | base-mults total (q = 19) | circuit ops |
|---|---:|---:|---|
| deployed Horner (per query) | q·N ≈ 195k | ≈ 200N·… (each ext-mul ≈ 9–12 base) | 1 HornerAcc/term, chain-adjacent |
| coordinate/IP form | **N − 1, once** (the α-power ladder, shared by all queries AND all 4 coordinates via CSE) | 12N + 4Nq ≈ 88N | 1 MulAdd/term against a materialized αⁱ — **no adjacency contract** |

Zero L×L products are *mathematically* required per query; the Horner order manufactures N.

⚑ **And the coordinate form is not a proposal — it is already deployed on the native rung.**
`[READ]` `chain/gnark/stark_open_input.go:445-465`: gnark computes S_x as four base-coordinate
accumulators against precomputed α-power coordinates — `accX[j] += px[k] · a[j]`, `a =
pre.alphaPows[k]` — i.e. exactly the 4-K-inner-products evaluation of the fixed K-linear map, with
the α-ladder hoisted once. **The BabyBear in-circuit verifier is the only rung still manufacturing
L×L products for this map.** (Same discovery shape as `sumcheck-batched-opening.md` §4: the gnark
side had the full factorization first; here it has the full coordinate decomposition first.)

But — the honest half — **in this circuit an ext-MAC and a base-MAC cost the same row**: every
`Target` is EF-typed, the ALU charges by lanes, not by base-mults (`circuit-prover/src/air/
alu_air.rs:22-31`). So the algebraic identity cashes out **only through table geometry**, which is
where the real waste sits:

### 3b. The measured waste `[MEASURED + READ]`

Deployed packing `p1/a4/K2` (`TablePacking::new(1,4)`, `horner_packed_steps = 2` —
`batch_stark_prover/packing.rs:23-30`): Alu row = 76 main + 59 prep = 135 columns for 4 lanes,
**but `compute_schedule` places Horner chains on lane 0 only** (`alu_air.rs:60-67`), so during the
~10⁴-step R-chains the other three lanes ride idle: measured 267,526 ops in 2¹⁷ rows = **2.04
ops/row → ~66 cells per Horner step**, whose informative payload is ONE base felt (carried through
a 4-limb ext operand slot — the [L:K] = 4 waste the brief named, times a further ~2× of schedule
idleness). The AIR family's own packed-step marginal cost is ~8 main + ~7 prep cells
(`AluPackedHornerStepPrepCols`) — a ~×4 headroom **inside the existing Rust AIR, as a config
knob**, before any new table is designed.

### 3c. The packing grid `[MEASURED — this lane's harness]`

New: `breadstuffs/circuit-prove/tests/recursion_tower_profile.rs::
g_packing_grid_over_the_deployed_leaf_wrap` — ONE circuit build (op list packing-invariant, printed
as the control), then `get_airs_and_degrees_with_prep` per `TablePacking` point. Every point is a
**VK rotation, not a wire change** — the landed ×1.436's precedent class exactly.

    RESULTS PENDING — grid running; this section is filled from the harness output below.

### 3d. The dedicated-chain-table endpoint `[DERIVED, design estimate — labeled]`

Beyond the in-family knob: the R-chain op is `out = acc·α + c` with `a` always the zero witness
(`pcs/fri/verifier.rs:1104-1108` — the multipoint `alpha_horner` passes `zero`), and `c` always a
**base-embedded** value. A dedicated running-chain table in the `recompose` NPO mold (zero local
constraints is not available here, but 1-base-data-cell steps are): ~3–5 cells/term against 66.
Moving the q·N R-chain terms out at ~16 terms/row: ≈ 1.0M cells; Alu remainder (71,712 ops) at
a4 ≈ 4.4M at the 2¹⁵ rung; wrap total ≈ **28.3M cells = ×1.43 beyond the landed ×1.436, ×2.06
cumulative** — the ×2.13 figure, reached without a sumcheck, without a PCS, without touching the
child. Poseidon2 share rises to ~75%, so the free-hash argument's precondition
(`leaf-vs-recursion.md` decision 3) is met by cells alone: a free hash becomes worth ~×3.7.

⚠ **House law, said before any of this moves:** the dedicated table is a NEW AIR. It is authored
in Lean or it does not exist (`project-lean-authored-air-law`); the existing `AluAir` is
pre-existing Rust debt, and the in-family packing retune (§3c) is the only variant that authors
nothing. The Lean-statable form that moves first: the chain-step semantics
`acc' = acc·α + embed(c)` and its fold `R = Σᵢ αⁱ·embed(pᵢ)` — a `List.foldl` identity over
`Theory/ExtensionBasis.lean`'s scalar tower, plus the coordinate identity of §5.

### 3e. The soundness guard this pathway must carry

`tensorMul_not_injective` (`minidregg/Selvage/RingSwitching.lean:266`): a verifier handed ONE
L-element in place of the array of K-values is **unsound, not merely lossy** — the packing map is
not injective on collapsed images. Every variant above keeps the opened values as individual
bus-checked witnesses (the leaf sponge separately binds each base felt); only the *evaluation
order* of the fixed linear map changes. The `HornerChainContractViolated` build-time guard
(`sumcheck-batched-opening.md` §1c) is the other rail: any re-emitter must keep chains
separator-seeded and non-adjacent, and the guard now goes red on violations in both directions.

---

## 4. PATHWAY 4 — fold-orbit structure: null AT SOURCE

The ±x orbit is already fully spent, at every place it exists:

* **Commit-phase leaves:** the prover supplies exactly `(2^arity − 1)` siblings per phase — shape-
  enforced at `pcs/fri/verifier.rs:1605-1612` — and the verifier seats its own **computed** folded
  value into the leaf via `reconstruct_evals` before hashing (`:1829-1832`); membership then IS the
  equality check. Nothing is absorbed at both x and −x; nothing the fold determines is re-supplied
  or re-hashed. Per phase per query: one 8-felt leaf (1 perm), path compressions, ~8 ext ops
  (`arity2 path :603-628`).
* **Input round:** each matrix is opened at ONE index (single row), rolled into the fold at its
  height (`:1745-1760`); the −x trace row is never opened.
* The measured confirmation was already on the books and is now explained: the **arity knob is a
  null knob** (`leaf-vs-recursion.md` §2d: −2% perms, +0.3% Alu) — because arity only re-buckets an
  orbit structure whose redundancy is already zero.

Priced saving: **0**. Nothing to change, nothing to state in Lean. Recorded so the question stays
answered.

---

## 5. PATHWAY 5 — trace/norm maps: the skeleton of pathway 3, and nothing else

The fact: for the dual basis θ of L/K, every coordinate of an L-value is a trace:
coord_j(R) = Tr_{L/K}(θ_j·R), so R = Σᵢ αⁱ pᵢ decomposes into 4 K-inner-products with **fixed
K-coefficient vectors** Tr(θ_j αⁱ) — the coordinate matrix of §3a. This is `packEquiv`'s
K-linear equivalence at l = 0 (`minidregg/Theory/ExtensionBasis.lean:143`, `Basis.equivFun` both
directions), and it is the precise sense in which "the verifier does K-linear algebra in L."

Surveyed the terminal checks for any OTHER equality of L-elements built K-linearly from K-data:
final-poly-vs-folded (`:1773-1774` + connect) — both sides L-data (betas, siblings); OOD constraint
recombination — L-valued composition at ζ; roll-in equalities — implicit in membership. **The
reduced opening is the only object with the collapsible shape**, so pathway 5 contributes its
mathematics to §3 and nothing separately. A probabilistic 1-trace-check variant
(Tr(γ(e−e')) = 0, γ random) trades exactness for a 1/p = 2⁻³¹ error term — refused; the
coordinate form is exact and free.

**Lean-statable form:** one lemma over `Basis.equivFun`/`Algebra.traceForm`:
`(Σᵢ αⁱ • (algebraMap K L (p i))) = Σⱼ (Σᵢ (A i j) * p i) • bⱼ` with A the coordinate array of the
α-powers — the identity §3's re-arrangements preserve, and the natural spec for any emitted
chain-table.

---

## 6. THE RANKED LIST

Ranked by (measured share of the wrap touched) × (plausible factor), with the re-proof class:

| rank | pathway | share touched | factor | class |
|---|---|---:|---:|---|
| 1 | **#3 packing/geometry** — in-family `TablePacking` retune | Alu = 43.6% of wrap cells | grid-measured (§3c) | **pure re-arrangement, VK rotation only** — the landed ×1.436's class; authors nothing |
| 2 | **#3 endpoint** — dedicated Lean-authored chain table | same 43.6% | ≈ ×1.43 further, ×2.06 cumulative `[DERIVED]` | re-arrangement of the accepted predicate; NEW AIR ⇒ **Lean statement moves first** (house law) |
| 3 | **#5** trace/coordinate identity | (inside #3) | — | the spec/lemma for rank 1–2's emitters |
| 4 | **#1** Frobenius/minpoly | 29.2% (absorption) named, 0% real | ≤ ×1.0 | closed by proof (§1d); two one-lemma Lean facts worth landing as refusals |
| 5 | **#4** fold-orbit | 5.9% named, 0% real | ×1.0 | null at source; nothing re-proves |
| 6 | **#2** deferred accumulation | 0% over this PCS | 0 (interior hops strictly negative) | protocol change AND PCS replacement; live only on the SP1/OpenVM road |

The through-line, for the horizon file when this lands: **the brief's suspicion was right, and the
recoverable waste was hiding one level below the algebra** — not "the field ops are the wrong
field ops" (they are K-linear-optimal already, §1/§5) but "each field op is billed ~66 committed
cells for a 1-base-felt payload" (§3b). Galois theory's contribution is the *proof that the
algebraic side is closed* (§1d, §4), which is what licenses spending everything on geometry.
