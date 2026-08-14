/-
# Selvage.RingSwitching — Diamond–Posen's compiler, its interface, and what it needs

**What this is built over, said out loud.** `Theory.ExtensionBasis` (mathlib
`Basis`/`Algebra`/`TensorProduct`), `Selvage.MultilinearExtension`'s `mle` and
`Selvage.EqPolynomial`'s `eqMle` (both stated over `[CommRing F]` — no
characteristic side condition anywhere), and `Selvage.MultilinearZeroTest`'s
`eqMle_zero_test` (`[Field F] [Fintype F]`).

**It does NOT touch `Selvage.Proximity`'s `FoldingData`.** That structure carries
`two_ne : (2 : F) ≠ 0` as a field, so it is UNINHABITABLE at characteristic two
(`Selvage.CharTwoWall.foldingData_charTwo_False`) and everything quantified over
it is vacuously true there on a green build. Nothing below mentions it, nothing
below needs `2 ≠ 0`, and §4's char-2 identity is FALSE outside characteristic
two — so the file cannot be silently reading as a prime-field result.

## The paper, read

Diamond–Posen, *Polylogarithmic Proofs for Multilinears over Binary Towers*
(eprint 2024/504). **Ring-switching (Construction 3.1) is a compiler**: given a
multilinear PCS `Π′` over a large field `L`, it emits a multilinear PCS `Π` over
a subfield `K`, with `deg(L / K) = 2^κ` and arity `ℓ′ = ℓ − κ`. Its two
correctness theorems are

* **Theorem 3.2** — if `Π′` is complete then `Π` is;
* **Theorem 3.5** — if `Π′` is secure then `Π` is, *proved by constructing an
  emulator*: `E` runs `Π′`'s emulator `E′` to get the packed `t′`, and then
  **"by reversing Definition 2.2" obtains `t` over `K`**, which it outputs.

Everything the compiler does rests on one object: a fixed `K`-basis
`(β_v)_{v ∈ B_κ}` of `L`. Definition 2.2 packs; Theorem 3.5 unpacks. Neither
step exists for a family that is not a basis, and **no `Basis` of an extension
over a subfield existed anywhere in this tree** until `Theory.ExtensionBasis`.

Soundness error added by the compiler: `(2·ℓ′ + κ) / |L|` — `κ/|L|` from
Schwartz–Zippel on the batching scalars `r″`, `2·ℓ′/|L|` from the `ℓ′`-round
degree-2 sumcheck.

## What is PROVED here

* §1 `packedTable` / `unpackTable` — Definition 2.2 and **its reversal, which is
  Theorem 3.5's step 3**, as mutually inverse maps; `emulator_unpack_unique`
  states the emulator's obligation in the form the proof uses (`∃!`), and
  `packed_mle_determines_source` lifts it through `mle`: **a packed
  `L`-multilinear determines its `K`-multilinear uniquely.**
* §2 `liftWord_eq_packedTable_zero` — `Selvage.SmallField`'s `liftWord` **is**
  ring-switching's packing map at `κ = 0`, i.e. at the trivial extension where
  it contracts nothing. `liftWord_not_packing` refuses it at every real
  extension. `unpackWord` supplies the missing direction.
* §3 The tensor algebra `A = L ⊗[K] L` is mathlib's; `φ₀ = includeLeft`,
  `φ₁ = includeRight`, and the `2^κ × 2^κ` `K`-array picture of Figure 9 is
  `Basis.tensorProduct`. **`tensorMul_not_injective`** proves the paper's
  Remark-3.3 observation (attributed there to Raju Krishnamoorthy): the
  multiplication map `h : L ⊗[K] L → L` is not injective, which is *why* the
  protocol must send `ŝ ∈ A` rather than the single field element
  `t(r_κ,…,r_{ℓ−1}) ∈ L`. A protocol design decision, as a theorem.
* §4 `eqMle_charTwo` — Remark 3.4's identity
  `eq~(X,Y) = ∏ (1 − Xᵢ − Yᵢ)`, valid **only** in characteristic two, and
  `eqMle_charTwo_fails_at_five` shows it is genuinely characteristic-dependent.
* §5 `ringSwitch_batching_bound` — **Theorem 3.5's Schwartz–Zippel leg, at the
  paper's `κ/|L|`**, discharged from `eqMle_zero_test`. This is the one
  probabilistic leg the compiler contributes that the tree could already prove.

## What is NAMED, not proved (§6)

`RingSwitchSecure` — Theorem 3.5 in full. Its discharged parts are cited in its
docstring; the undischarged part is the `ℓ′`-round **degree-2** sumcheck
transfer over `h = A · t′`, which the tree's `sumcheck_soundness` covers in
shape but which nothing here connects to the tensor-algebra identity (30). This
is the honest remainder, and it is undone work, not a theorem of the model.

## §7 — the handoff nobody had written

`RingSwitchTarget` is the interface a large-field PCS must satisfy to be `Π′`.
Its docstring lists, item by item, what `Selvage/AdditiveBaseFold.lean`'s
characteristic-2 BaseFold has to supply. That list is the seam between the two
lanes.
-/
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Algebra.Algebra.Bilinear
import Theory.ExtensionBasis
import Selvage.MultilinearZeroTest
import Selvage.SmallField

namespace Minidregg.Selvage

open Module
open Minidregg.Theory

/-! ## §1 Definition 2.2 and its reversal

The packing map itself is `Theory.packOf` / `Theory.packEquiv`; this section
gives it ring-switching's vocabulary and states the emulator's step as the
proposition Theorem 3.5's proof actually invokes. -/

section Packing

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {κ : ℕ}

/-- **Definition 2.2**, on Lagrange-coefficient tables: chunk the `ℓ`-cube as
`B_κ × B_{ℓ′}` and basis-combine each `κ`-chunk into one `L`-element. -/
noncomputable def packedTable (b : Basis (Fin κ → Bool) K L) (l : ℕ)
    (t : (Fin κ → Bool) × (Fin l → Bool) → K) : (Fin l → Bool) → L :=
  packOf (K := K) b l t

/-- **Theorem 3.5's step 3 — "by reversing Definition 2.2".** The emulator's
unpack. It exists because `b` is a `Basis`: spanning gives it a preimage,
independence makes the preimage unique. -/
noncomputable def unpackTable (b : Basis (Fin κ → Bool) K L) (l : ℕ)
    (t' : (Fin l → Bool) → L) : (Fin κ → Bool) × (Fin l → Bool) → K :=
  (packEquiv b l).symm t'

@[simp] theorem unpack_packedTable (b : Basis (Fin κ → Bool) K L) (l : ℕ)
    (t : (Fin κ → Bool) × (Fin l → Bool) → K) :
    unpackTable b l (packedTable b l t) = t := by
  have h : packedTable b l t = packEquiv b l t := (packEquiv_apply b l t).symm
  rw [unpackTable, h, LinearEquiv.symm_apply_apply]

@[simp] theorem packedTable_unpack (b : Basis (Fin κ → Bool) K L) (l : ℕ)
    (t' : (Fin l → Bool) → L) :
    packedTable b l (unpackTable b l t') = t' := by
  rw [packedTable, ← packEquiv_apply, unpackTable, LinearEquiv.apply_symm_apply]

/-- **The emulator's obligation, discharged.** Handed the packed table `t′` that
`E′` extracted, the ring-switching emulator has exactly one `K`-table to output.
Existence is what lets `E` return anything at all; uniqueness is what makes
`t(r) ≠ s` a meaningful event in the security experiment. Both are `Basis`. -/
theorem emulator_unpack_unique (b : Basis (Fin κ → Bool) K L) (l : ℕ)
    (t' : (Fin l → Bool) → L) : ∃! t, packedTable b l t = t' := by
  refine ⟨unpackTable b l t', packedTable_unpack b l t', fun u hu => ?_⟩
  rw [← hu, unpack_packedTable]

/-- **A packed `L`-multilinear determines its `K`-multilinear.** Through `mle`:
if two `K`-witnesses pack to `L`-multilinears with the same extension, they are
the same witness. This is the statement an extraction argument consumes when
the large-field scheme reports a POLYNOMIAL rather than a table. -/
theorem packed_mle_determines_source (b : Basis (Fin κ → Bool) K L) (l : ℕ)
    {t u : (Fin κ → Bool) × (Fin l → Bool) → K}
    (h : mle (packedTable b l t) = mle (packedTable b l u)) : t = u := by
  have := mle_injective (F := L) (m := l) h
  rw [← unpack_packedTable b l t, ← unpack_packedTable b l u, this]

end Packing

/-! ## §2 `liftWord` — the direction, and why it is the wrong one

`Selvage.SmallField.liftWord f = algebraMap ∘ f` maps a `K`-word to an `L`-word
of the SAME LENGTH. Ring-switching's packing maps a `K`-word to an `L`-word
`2^κ` times SHORTER. The two agree at exactly one place — `κ = 0` — and that is
the trivial extension, where the compiler saves nothing.

Diamond–Posen open §1 by rejecting precisely this construction: "One might
trivially attempt to commit to a tiny-field multilinear simply by embedding its
coefficients into an extension … it would impose an artificial penalty
proportional to the ratio between its input's original coefficient bitwidth and
the scheme's native field's bitwidth." That ratio is
`Theory.lift_overhead_factor`'s `2^κ`. -/

section Direction

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **`liftWord` IS the packing map at `κ = 0`.** With the one-element
coordinate family `β = (1)`, `packedTable` collapses to the coefficientwise
embedding. So the lift is not a *different* construction from ring-switching's
packing; it is its degenerate instance, at the one arity that contracts
nothing. -/
theorem liftWord_eq_packOf_zero (l : ℕ)
    (t : (Fin 0 → Bool) × (Fin l → Bool) → K) (w : Fin l → Bool) :
    packOf (K := K) (κ := 0) (fun _ => (1 : L)) l t w
      = liftWord (K := L) (fun p : (Fin 0 → Bool) × (Fin l → Bool) => t p)
          (default, w) := by
  simp only [packOf, liftWord, Finset.univ_unique, Finset.sum_singleton,
    Algebra.smul_def, mul_one]
  exact congrArg (fun v => algebraMap K L (t (v, w))) (Subsingleton.elim _ _)

/-- **TOOTH: the lift is refused as a packing map at every real extension.**
`packOf` at a basis is bijective (`Theory.packOf_bijective`); the
coefficientwise lift is not even surjective once `[L : K] > 1`. No reindexing
and no choice of basis repairs this — it is the direction that is wrong. -/
theorem liftWord_not_packing {ι : Type*} [Nonempty ι]
    (h : 1 < Module.finrank K L) :
    ¬ Function.Surjective (liftWord (ι := ι) (Fq := K) (K := L)) :=
  liftFun_not_surjective h

/-- **The missing direction, supplied.** Where `liftWord` widens each `K`
coefficient into an `L` element, `unpackWord` reads an `L` word back as its
`K`-coordinate table — this is the map ring-switching's emulator needs and the
one the tree did not have. -/
noncomputable def unpackWord {κ : ℕ} (b : Basis (Fin κ → Bool) K L) (l : ℕ) :
    ((Fin l → Bool) → L) → ((Fin κ → Bool) × (Fin l → Bool) → K) :=
  unpackTable b l

/-- `unpackWord` is a two-sided inverse of packing — stated so the pair can be
cited without unfolding either. -/
theorem unpackWord_bijective {κ : ℕ} (b : Basis (Fin κ → Bool) K L) (l : ℕ) :
    Function.Bijective (unpackWord b l) :=
  ⟨fun x y h => by
      rw [← packedTable_unpack b l x, ← packedTable_unpack b l y]
      exact congrArg _ h,
   fun t => ⟨packedTable b l t, unpack_packedTable b l t⟩⟩

end Direction

/-! ## §3 The tensor algebra `A = L ⊗_K L` (Subsection 2.5, Figure 9)

Each element of `A` is a `2^κ × 2^κ` array of `K`-elements, readable both
column-wise (a list of `L`-elements) and row-wise. `φ₀` inscribes an `L`-element
into the left column, `φ₁` into the top row; the protocol's first message `ŝ`
lives here. Mathlib supplies every piece: `Algebra.TensorProduct.includeLeft`,
`includeRight`, and `Basis.tensorProduct` for the array picture. -/

section TensorAlgebra

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {κ : ℕ}

open scoped TensorProduct

/-- `φ₀ : L ↪ A` — Subsection 2.5's column embedding. -/
noncomputable abbrev phi0 : L →ₐ[K] L ⊗[K] L := Algebra.TensorProduct.includeLeft

/-- `φ₁ : L ↪ A` — Subsection 2.5's row embedding. -/
noncomputable abbrev phi1 : L →ₐ[K] L ⊗[K] L := Algebra.TensorProduct.includeRight

/-- **Figure 9's `2^κ × 2^κ` `K`-array**, as a basis of the tensor algebra: an
element of `A` is exactly a `B_κ × B_κ` matrix of `K`-scalars. Mathlib's
`Basis.tensorProduct`; nothing to construct. -/
noncomputable def arrayBasis (b : Basis (Fin κ → Bool) K L) :
    Basis ((Fin κ → Bool) × (Fin κ → Bool)) K (L ⊗[K] L) :=
  b.tensorProduct b

/-- `dim_K A = (2^κ)²` — the array really has `2^κ` rows and `2^κ` columns. -/
theorem finrank_tensorAlgebra [Module.Finite K L] :
    Module.finrank K (L ⊗[K] L)
      = Module.finrank K L * Module.finrank K L :=
  Module.finrank_tensorProduct

/-- **Remark 3.3, proved: the multiplication map loses information.** `h : A → L`
(mathlib's `LinearMap.mul'`) sends `α ⊗ β ↦ α·β`; the paper observes that
`t(r_κ,…,r_{ℓ−1})` relates to the protocol's message `ŝ` exactly by `h`, "which
is of course not injective", and that this is why the verifier must be handed
the whole array. Here it is a dimension count: `(2^κ)² > 2^κ` for `κ ≥ 1`, so no
injective `K`-linear map `A → L` exists at all.

**Consequence for any implementation:** a ring-switching verifier that receives
a single `L`-element in place of `ŝ` is not a variant with a worse constant, it
is unsound — the information it needs does not survive the map. -/
theorem tensorMul_not_injective [Module.Finite K L]
    (h : 1 < Module.finrank K L) :
    ¬ Function.Injective (LinearMap.mul' K L) := by
  intro hinj
  have hle := LinearMap.finrank_le_finrank_of_injective
    (f := LinearMap.mul' K L) hinj
  rw [finrank_tensorAlgebra] at hle
  nlinarith [hle, h]

end TensorAlgebra

/-! ## §4 Remark 3.4's characteristic-2 identity

The verifier computes `e := eq~(φ₀(r_κ),…,φ₀(r_{ℓ−1}), φ₁(r′₀),…,φ₁(r′_{ℓ′−1}))`
inside `A`. Diamond–Posen give a concretely efficient procedure resting on an
identity that is "valid only in characteristic 2":

`eq~(X,Y) = ∏ᵢ ((1 − Xᵢ)(1 − Yᵢ) + XᵢYᵢ) = ∏ᵢ (1 − Xᵢ − Yᵢ)`.

Their algorithm — initialize `e := 1`, then `e −= e·φ₀(r_{κ+i}) + e·φ₁(r′ᵢ)` —
is exactly this product expanded, and it is why the verifier's cost is
`2·ℓ′·2^κ` `L`-multiplications rather than a general algebra multiplication per
round. -/

section CharTwo

/-- **Remark 3.4's identity.** In characteristic two the equality polynomial
collapses to a product of affine factors. -/
theorem eqMle_charTwo {F : Type*} [CommRing F] [CharP F 2] {m : ℕ}
    (z x : Fin m → F) : eqMle z x = ∏ i, (1 - z i - x i) := by
  refine Finset.prod_congr rfl fun i _ => ?_
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination (z i * x i) * h2

/-- **TOOTH: the identity is genuinely characteristic-dependent.** Over `F₅` the
two sides differ, so `eqMle_charTwo` is not a fact about equality polynomials
that merely happens to be stated with a `CharP` hypothesis — dropping the
hypothesis makes it FALSE, and an implementation that used the cheap product
form over a prime field would compute the wrong `e`. -/
theorem eqMle_charTwo_fails_at_five :
    eqMle (![2] : Fin 1 → ZMod 5) ![3] ≠ ∏ i, (1 - (![2] : Fin 1 → ZMod 5) i - (![3] : Fin 1 → ZMod 5) i) := by
  decide

end CharTwo

/-! ## §5 Theorem 3.5's batching leg, discharged

Step 3 of Construction 3.1 has the verifier sample batching scalars
`(r″₀,…,r″_{κ−1}) ← L^κ`. Theorem 3.5's proof forms

`S(X₀,…,X_{κ−1}) := Σ_{u ∈ B_κ} (ŝ_u − s_u) · eq~(u, X₀,…,X_{κ−1})`,

observes that `ŝ ≠ s` makes it not identically zero, and applies
Schwartz–Zippel to bound the bad set by `κ/|L|`.

`Selvage/MultilinearZeroTest.lean`'s `eqMle_zero_test` is precisely that bound.
The theorem below is the paper's leg in the paper's vocabulary. -/

section Batching

variable {L : Type} [Field L] [Fintype L] {κ : ℕ}

/-- **Theorem 3.5's Schwartz–Zippel leg, at the paper's bound.** If the prover's
first message `ŝ` differs from the honest `s` in its row decomposition, then the
verifier's batched value `s₀` coincides with the honest one for at most a
`κ/|L|` fraction of batching scalars.

`rowDiff u := ŝ_u − s_u` is the row-difference vector; `rowDiff ≠ 0` is exactly
the hypothesis `ŝ ≠ s` supplies. -/
theorem ringSwitch_batching_bound {rowDiff : (Fin κ → Bool) → L}
    (hne : rowDiff ≠ 0) :
    uniformProb (Fin κ → L)
        (fun r'' => ∑ u, eqMle r'' (cubePt u) * rowDiff u = 0)
      ≤ (κ : ℝ) / Fintype.card L :=
  eqMle_zero_test hne

end Batching

/-! ## §6 The compiler's interface, and Theorem 3.5 as a named obligation -/

section Interface

/-- **The large-field multilinear PCS interface that ring-switching compiles.**
Construction 3.1 touches `Π′` at exactly three points: `Setup′` (which fixes
`L` and the arity `ℓ′`), `Commit′` on the packed table, and the evaluation
protocol at the sumcheck's final point `r′` with claimed value `s′`. This
structure is that surface and no more.

Modelling note, deliberate: `accepts` is a PREDICATE, not a probability. The
probabilistic content of Definition 2.9 lives in `Extractable` below and in
`RingSwitchSecure`; keeping it out of the syntax is what lets the completeness
leg be checked at all. -/
structure LargeFieldMlePcs (L : Type) [Field L] where
  /-- Commitment handles. -/
  Root : Type
  /-- `Π′.Commit′` on an `ℓ′`-variate `L`-multilinear, in table form. -/
  commit : {l : ℕ} → ((Fin l → Bool) → L) → Root
  /-- `V′`'s verdict on (handle, evaluation point, claimed value). -/
  accepts : {l : ℕ} → Root → (Fin l → L) → L → Prop

variable {L : Type} [Field L]

/-- **Theorem 3.2's hypothesis**: `Π′` is complete — an honest commitment and a
true evaluation claim are accepted. -/
def LargeFieldMlePcs.Complete (S : LargeFieldMlePcs L) : Prop :=
  ∀ {l : ℕ} (t : (Fin l → Bool) → L) (r : Fin l → L),
    S.accepts (S.commit t) r (mle t r)

/-- **Theorem 3.5's hypothesis**, in the zero-error idealization of Definition
2.9. Faithful in one respect that matters: the extracted table is produced
**before** the evaluation point is seen (Definition 2.9's strict form, which
Diamond–Posen adopt precisely so that composition is easy), so the `∃ t` is
outside the `∀ r`.

⚠ HONEST LABEL, and it is undone work rather than a theorem of the model: the
real definition allows a negligible failure probability, and this collapses it
to zero. Transmuting it means stating the experiment over `Selvage/Rbr.lean`'s
`uniformProb` the way `sumcheck_soundness` does. Nothing here depends on the
collapse in a way that would hide a defect — `Complete` and `Extractable` are
hypotheses on `Π′`, so a weaker `Π′` simply fails to satisfy them. -/
def LargeFieldMlePcs.Extractable (S : LargeFieldMlePcs L) : Prop :=
  ∀ {l : ℕ} (rt : S.Root), ∃ t : (Fin l → Bool) → L,
    ∀ (r : Fin l → L) (s : L), S.accepts rt r s → mle t r = s

/-- **Construction 3.1's commitment leg.** The small-field scheme commits to a
`K`-multilinear by packing it and handing the result to `Π′`. This is the whole
of `Π.Commit`, and it is where "no embedding overhead" comes from: the object
`Π′` sees has `2^ℓ′` `L`-coefficients, i.e. the same bit count as the `2^ℓ`
`K`-coefficients it came from (`Theory.finrank_packed_eq`). -/
noncomputable def ringSwitchCommit {K : Type} [Field K] [Algebra K L] {κ : ℕ}
    (S : LargeFieldMlePcs L) (b : Basis (Fin κ → Bool) K L) (l : ℕ)
    (t : (Fin κ → Bool) × (Fin l → Bool) → K) : S.Root :=
  S.commit (packedTable b l t)

/-- **The commitment leg is injective in the `K`-witness whenever `Π′`'s is in
the `L`-witness** — the packing contributes no collisions of its own. The
converse direction is the content: a collision in the compiled scheme is a
collision in `Π′`, never an artefact of ring-switching. -/
theorem ringSwitchCommit_injective {K : Type} [Field K] [Algebra K L] {κ : ℕ}
    (S : LargeFieldMlePcs L) (b : Basis (Fin κ → Bool) K L) (l : ℕ)
    (hS : Function.Injective (S.commit (l := l))) :
    Function.Injective (ringSwitchCommit S b l) := by
  intro t u h
  have := hS h
  rw [← unpack_packedTable b l t, ← unpack_packedTable b l u, this]

/-- **Theorem 3.5, stated in full — a NAMED OBLIGATION, not a theorem.**

For every large-field scheme `Π′` that is complete and extractable, every
subfield basis, and every arity, the compiled scheme's adversary either has its
`K`-witness extracted correctly or falls in a bad set of measure at most
`(2·ℓ′ + κ)/|L|`.

What is already discharged, and can be cited when this is attacked:

* step 3 of the emulator — `emulator_unpack_unique` (and its `mle` form,
  `packed_mle_determines_source`);
* the `κ/|L|` batching leg — `ringSwitch_batching_bound`;
* the verifier's tensor-algebra evaluation being well-posed at all —
  `tensorMul_not_injective` says the cheaper single-`L`-element message cannot
  substitute for `ŝ`.

What is NOT: the `ℓ′`-round **degree-2** sumcheck transfer over
`h = A · t′`, contributing `2·ℓ′/|L|`, and its connection to the tensor-algebra
identity (30). `Selvage/Sumcheck.lean`'s `sumcheck_soundness` has the right
shape (`v·d/|F|` at `d = 2`) but nothing in this tree connects it to `A`'s row
and column decompositions. That connection is the remaining work, and it is
work, not a boundary of the model.

The statement below is the ASSEMBLY step, verbatim from the proof: given that
acceptance forces one of the two bad events, and given the sumcheck's own
bound, the accepting set over the verifier's joint randomness
`(r″, r′) ← L^κ × L^{ℓ′}` is bounded by the sum. Discharging it needs the
product-uniform marginalization and a union bound, neither of which exists
here; `ringSwitch_batching_bound` already supplies the `κ/|L|` half.

⚠ This is deliberately NOT `∃ err, err ≤ bound` or any other shape that a
reader could discharge by inspection: the hypotheses constrain a supplied
accepting set, and a wrong constant refutes it. -/
def RingSwitchSecure (L : Type) [Field L] [Fintype L] : Prop :=
  ∀ (κ l : ℕ) (rowDiff : (Fin κ → Bool) → L), rowDiff ≠ 0 →
    ∀ (launder : (Fin l → L) → Prop)
      (accept : (Fin κ → L) × (Fin l → L) → Prop),
      (∀ c, accept c →
          (∑ u, eqMle c.1 (cubePt u) * rowDiff u = 0) ∨ launder c.2) →
      uniformProb (Fin l → L) launder ≤ (2 * l : ℝ) / Fintype.card L →
      uniformProb ((Fin κ → L) × (Fin l → L)) accept
        ≤ (2 * l + κ : ℝ) / Fintype.card L

/-- **The obligation's hypotheses are inhabited.** Taking the accepting set to
be exactly the batching failure and the sumcheck to launder nothing satisfies
both premises, so `RingSwitchSecure` is not a statement about an empty
hypothesis family — the failure mode where an obligation is "true" because
nothing can ever satisfy its antecedent. -/
theorem ringSwitchSecure_hypotheses_inhabited {L : Type} [Field L] [Fintype L]
    {κ l : ℕ} (rowDiff : (Fin κ → Bool) → L) :
    (∀ c : (Fin κ → L) × (Fin l → L),
        (∑ u, eqMle c.1 (cubePt u) * rowDiff u = 0) →
        (∑ u, eqMle c.1 (cubePt u) * rowDiff u = 0) ∨ (False : Prop))
      ∧ uniformProb (Fin l → L) (fun _ => False)
          ≤ (2 * l : ℝ) / Fintype.card L := by
  refine ⟨fun _ h => Or.inl h, ?_⟩
  have hz : uniformProb (Fin l → L) (fun _ => False) = 0 := by
    simp [uniformProb]
  rw [hz]
  positivity

end Interface

/-! ## §7 The handoff: what a characteristic-2 BaseFold must provide

`Selvage/AdditiveBaseFold.lean` is building the other end — BaseFold's descent
over the additive (LCH) tower, with `Theory.friFold` in place of the
multiplicative even/odd split. Diamond–Posen's own stated compilation target is
"a characteristic-2 adaptation of BaseFold", so the two ends meet here. This
section says exactly what that end has to hand over. -/

section Handoff

variable {L : Type} [Field L] [CharP L 2]

/-- **The interface a characteristic-2 BaseFold must satisfy to be `Π′`.**

Bundling `Complete` and `Extractable` with the scheme is the whole formal
obligation; the rest of the handoff is shape, and it is listed here because
shape mismatches are what actually break a composition:

1. **Arity.** `Π′` is invoked at `ℓ′ = ℓ − κ` variables, never at `ℓ`. For the
   deployed Binius shape (`K = T₀`, `L = T₇`, `Theory.binius_shape_finrank`)
   that is `κ = 7`: a 2^20-coefficient bit-multilinear is committed as a
   2^13-coefficient `GF(2^128)`-multilinear.
2. **Table form, not codeword form.** `commit` takes the Lagrange coefficient
   table `(Fin l → Bool) → L`. `AdditiveBaseFold`'s `lchLevelWord` is an
   evaluation word on the level-`n` additive domain; the bridge to the table is
   its `booleanMobiusPolynomial`/`tableOfPoly` layer, which is characteristic-
   free and already cited there as porting verbatim.
3. **Evaluation at an arbitrary `r′ ∈ L^{ℓ′}`, off the domain.** The sumcheck
   hands `Π′` a point sampled from `L`, not a domain point. `lchLevelWord_terminal`
   terminates at `mle (tableOfPoly m p) r`, which is the right shape.
4. ⚑ **The transcript must bind the ORDERED basis `β`, not just its span.**
   `AdditiveBaseFold`'s `keystone_basis_ambiguity` exhibits one codeword on one
   domain that is an honest commitment to two different tables under two
   orderings of the same `GF(2)`-basis. Ring-switching's `Extractable` is
   FALSE for a scheme with that ambiguity — extraction is not unique — so this
   is a blocking prerequisite, not a hygiene note.
5. **No `FoldingData`.** The compiler is characteristic-agnostic, but the
   binary instantiation is not: any `Π′` reached through
   `Selvage.Proximity`'s `FoldingData` is vacuous at `CharP L 2`
   (`Selvage.CharTwoWall.foldingData_charTwo_False`). `Π′` must come through
   the additive cone.
6. **A `Basis` on the same `L`.** `Theory.towerCubeBasis j d` supplies it for
   any two tower levels, with `κ = d` exactly (`Theory.towerExt_finrank`). The
   basis `Theory.cubeBasis` produces is `Classical.choice`'s; pinning it to the
   Fan–Paar coordinates (`Theory.BinaryTowerFanPaarCodec`) is what makes the
   prover's packing cheap, and is not needed for soundness. -/
structure RingSwitchTarget (L : Type) [Field L] [CharP L 2] where
  /-- The large-field scheme. -/
  pcs : LargeFieldMlePcs L
  /-- Theorem 3.2's hypothesis. -/
  complete : pcs.Complete
  /-- Theorem 3.5's hypothesis (Definition 2.9, strict form). -/
  extractable : pcs.Extractable

/-- **Satisfiable: the interface is not vacuous.** The trivial scheme that
commits a table to itself and accepts exactly the true evaluations meets both
obligations at any characteristic-2 field. It is not a PCS — its handles are
the whole witness, so it is not succinct and not binding in any useful sense —
but it proves `RingSwitchTarget` is inhabited, so `RingSwitchSecure`'s
hypotheses are not silently empty and a lane cannot discharge the handoff by
producing an uninhabitable interface. -/
noncomputable def trivialTarget : RingSwitchTarget L where
  pcs :=
    { Root := Σ l : ℕ, (Fin l → Bool) → L
      commit := fun {l} t => ⟨l, t⟩
      accepts := fun {l} rt r s =>
        ∃ h : rt.1 = l, mle (h ▸ rt.2) r = s }
  complete := fun t r => ⟨rfl, rfl⟩
  extractable := fun {l} rt => by
    classical
    by_cases hl : rt.1 = l
    · exact ⟨hl ▸ rt.2, fun r s hacc => by
        obtain ⟨h, hval⟩ := hacc
        rw [← hval]⟩
    · exact ⟨0, fun r s hacc => absurd hacc.choose hl⟩

end Handoff

/-! ## §8 Axiom pins -/

/-- info: 'Minidregg.Selvage.unpack_packedTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unpack_packedTable
/-- info: 'Minidregg.Selvage.packedTable_unpack' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms packedTable_unpack
/-- info: 'Minidregg.Selvage.emulator_unpack_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms emulator_unpack_unique
/-- info: 'Minidregg.Selvage.packed_mle_determines_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms packed_mle_determines_source
/-- info: 'Minidregg.Selvage.liftWord_eq_packOf_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms liftWord_eq_packOf_zero
/-- info: 'Minidregg.Selvage.liftWord_not_packing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms liftWord_not_packing
/-- info: 'Minidregg.Selvage.unpackWord_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms unpackWord_bijective
/-- info: 'Minidregg.Selvage.tensorMul_not_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms tensorMul_not_injective
/-- info: 'Minidregg.Selvage.eqMle_charTwo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eqMle_charTwo
/-- info: 'Minidregg.Selvage.eqMle_charTwo_fails_at_five' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eqMle_charTwo_fails_at_five
/-- info: 'Minidregg.Selvage.ringSwitch_batching_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ringSwitch_batching_bound
/-- info: 'Minidregg.Selvage.ringSwitchCommit_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ringSwitchCommit_injective
/-- info: 'Minidregg.Selvage.ringSwitchSecure_hypotheses_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ringSwitchSecure_hypotheses_inhabited
/-- info: 'Minidregg.Selvage.trivialTarget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms trivialTarget

end Minidregg.Selvage
