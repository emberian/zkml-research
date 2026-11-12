/-
# Theory.ExtensionBasis — the subfield/extension `Basis` connector (ring-switching)

**What this is built over, said out loud.** This file stands on `Mathlib`'s
`Basis` / `Module.Finite` / `Algebra` and on `Theory.BinaryTower` (mathlib's
`GaloisField 2 (2^k)`). It does **not** touch `Selvage.Proximity`'s
`FoldingData`, whose `two_ne : (2 : F) ≠ 0` structure field is UNINHABITABLE in
characteristic 2 — anything built over that carrier is vacuously true at a
binary field. Nothing here mentions it, nothing here needs `2 ≠ 0`, and the
concrete instantiations below are the characteristic-2 tower itself, so the
statements are inhabited where they claim to be.

## Why this file exists

Diamond–Posen, *Polylogarithmic Proofs for Multilinears over Binary Towers*
(eprint 2024/504), Construction 3.1 — "ring-switching" — is a **compiler**: it
eats a multilinear PCS over a large field `L` and emits one over a subfield `K`.
Its whole coordinate machinery is a fixed `K`-basis `(β_v)_{v ∈ B_κ}` of `L`,
where `B_κ = {0,1}^κ` and `deg(L / K) = 2^κ`. Definition 2.2 packs a `K`-valued
`ℓ`-variate multilinear into an `L`-valued `(ℓ − κ)`-variate one by
basis-combining each `2^κ`-element chunk; Theorem 3.5's emulator recovers `t`
from `t'` "by reversing Definition 2.2".

**That reversal is the load-bearing step, and it exists exactly because `(β_v)`
is a `Basis` and not merely a family.** Spanning gives the emulator a preimage
at all; independence makes it the only one. A family that is neither gives a
protocol that compiles and extracts nothing (`packOf_not_injective_of_repeat`
below is that failure, exhibited).

## What is PROVED here (mathlib reuse; the connector is assembly, not invention)

* `cubeBasis` — the `B_κ`-indexed `K`-basis of `L`, from
  `Module.finBasisOfFinrankEq` reindexed along `Fin (2^κ) ≃ (Fin κ → Bool)`.
  Mathlib had all of it; this is the reindexing nobody had written.
* `packOf` — Definition 2.2's packing map, stated for an ARBITRARY family, so
  that the failure modes are expressible.
* `packEquiv` / `packCube` — the same map at a `Basis`, as a `K`-linear
  EQUIVALENCE; `packCube` is the `ℓ = κ + ℓ'` form. `.symm` IS Theorem 3.5's
  "reversing Definition 2.2", so the emulator's step 3 is a mathlib inverse.
* `finrank_packed_eq` — **zero embedding overhead, as a dimension identity**:
  the packed target `(B_ℓ' → L)` carries exactly `2^(κ+ℓ')` `K`-coordinates,
  the same count as the source `(B_ℓ → K)`. Proved FROM the equivalence.
* `finrank_lifted_eq` + `lift_overhead_factor` — and the element-wise lift's
  target carries `2^κ` TIMES as many. That ratio is the embedding overhead
  ring-switching abolishes, and it is why an element-wise lift cannot be the
  packing map.
* Tower instantiation: `towerAlgebra`, `towerExt_finrank`
  (`[T_{j+d} : T_j] = 2^d` — every sub-level extension of the binary tower has
  degree an exact power of two, so `κ = d` and `B_κ` is literally the `d`-cube),
  `towerCubeBasis`, and the deployed Binius shape `T₀ ⊂ T₇` (κ = 7, deg 128).

## Teeth — each is an instantiation that must be REFUSED

* `no_cubeBasis_of_finrank_ne` — a wrong `κ` admits no cube-indexed basis at
  all. (`finrank ≠ 2^κ` ⇒ `¬ Nonempty (Basis (Fin κ → Bool) K L)`.)
* `packOf_not_injective_of_repeat` — a coordinate family with a repeated
  element packs two DISTINCT `K`-witnesses onto the same `L`-object. The
  emulator cannot reverse it; a scheme built on it extracts nothing while
  typechecking.
* `algebraMap_not_surjective` / `liftFun_not_surjective` — the element-wise
  lift `f ↦ algebraMap ∘ f` is not surjective once `1 < [L : K]`, hence is not
  a packing map in any degree above the trivial one. This is the direction
  error: it widens each coefficient (overhead `2^κ`) instead of contracting
  chunks (overhead `1`).

## Honest residual

The `Basis` produced by `cubeBasis` is `Module.finBasisOfFinrankEq`'s — chosen
by `Classical.choice`, hence NOT the Fan–Paar tower basis the deployed
arithmetic uses. Every statement here is basis-INDEPENDENT (they quantify over
`b`), so pinning `b` to the Fan–Paar coordinates
(`Theory.BinaryTowerFanPaarCodec`) is a separate, purely constructive job; the
compiler's interface does not depend on which basis is chosen, but the
PROVER's cost does.
-/
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.FieldTheory.Finiteness
import Theory.BinaryTower

namespace Minidregg.Theory

open Module

/-! ## §1 The cube-indexed basis of an extension over its subfield

Diamond–Posen index their `K`-basis of `L` by `B_κ = {0,1}^κ`, not by
`Fin (2^κ)`, because packing consumes exactly `κ` of the multilinear's
variables. Mathlib supplies the basis (`Module.finBasisOfFinrankEq`); the cube
indexing is a `Basis.reindex`. -/

section CubeBasis

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

/-- `Fin (2^κ) ≃ B_κ`: the cube on `κ` bits has `2^κ` points. -/
noncomputable def finCubeEquiv (κ : ℕ) : Fin (2 ^ κ) ≃ (Fin κ → Bool) :=
  Fintype.equivOfCardEq (by simp)

/-- **The `B_κ`-indexed `K`-basis of `L`** — Diamond–Posen's `(β_v)_{v ∈ B_κ}`.
Requires the degree witness `[L : K] = 2^κ`; without it the cube index is the
wrong size and no such basis exists (`no_cubeBasis_of_finrank_ne`). -/
noncomputable def cubeBasis [Module.Finite K L] {κ : ℕ}
    (hdeg : Module.finrank K L = 2 ^ κ) : Basis (Fin κ → Bool) K L :=
  (Module.finBasisOfFinrankEq K L hdeg).reindex (finCubeEquiv κ)

variable {K L}

/-- **TOOTH: a wrong `κ` is refused.** If the degree is not `2^κ` then there is
no `B_κ`-indexed `K`-basis of `L` at all — a cube-indexed coordinate map at the
wrong arity cannot be built, it does not merely fail to be useful. -/
theorem no_cubeBasis_of_finrank_ne {κ : ℕ} (h : Module.finrank K L ≠ 2 ^ κ) :
    ¬ Nonempty (Basis (Fin κ → Bool) K L) := by
  rintro ⟨b⟩
  exact h (by rw [Module.finrank_eq_card_basis b]; simp)

end CubeBasis

/-! ## §2 Definition 2.2 — packing, and its reversal

`t'(X₀,…,X_{ℓ'−1}) := Σ_{v ∈ B_κ} t(v₀,…,v_{κ−1}, X₀,…,X_{ℓ'−1}) · β_v`.

At the level of Lagrange-coefficient vectors this is: split the `ℓ`-cube index
as `B_κ × B_{ℓ'}`, and basis-combine each `κ`-chunk into one `L`-element. -/

section Packing

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {κ : ℕ}

/-- **Definition 2.2's packing map, for an ARBITRARY family `β`.** Stated
without a `Basis` hypothesis on purpose: the failure modes below are exactly
the ones a non-basis family produces, and they are invisible if the definition
can only be written at a basis. -/
noncomputable def packOf (β : (Fin κ → Bool) → L) (l : ℕ) :
    ((Fin κ → Bool) × (Fin l → Bool) → K) → ((Fin l → Bool) → L) :=
  fun t w => ∑ v, t (v, w) • β v

/-- **Packing at a basis, as a `K`-linear EQUIVALENCE.** The forward map is
Definition 2.2; `.symm` is Theorem 3.5's "reversing Definition 2.2", i.e. the
emulator's step 3. Both directions exist because `b` spans (a preimage exists)
and is independent (it is unique) — the two halves of `Basis`, each consumed by
one leg of the reduction. -/
noncomputable def packEquiv (b : Basis (Fin κ → Bool) K L) (l : ℕ) :
    ((Fin κ → Bool) × (Fin l → Bool) → K) ≃ₗ[K] ((Fin l → Bool) → L) where
  toFun t := fun w => b.equivFun.symm fun v => t (v, w)
  map_add' t u := by
    funext w
    exact map_add b.equivFun.symm (fun v => t (v, w)) (fun v => u (v, w))
  map_smul' c t := by
    funext w
    exact map_smul b.equivFun.symm c (fun v => t (v, w))
  invFun t' := fun p => b.equivFun (t' p.2) p.1
  left_inv t := by
    funext p
    simp only [LinearEquiv.apply_symm_apply]
  right_inv t' := by
    funext w
    exact b.equivFun.symm_apply_apply (t' w)

/-- The equivalence's forward map IS Definition 2.2's sum. -/
theorem packEquiv_apply (b : Basis (Fin κ → Bool) K L) (l : ℕ)
    (t : (Fin κ → Bool) × (Fin l → Bool) → K) :
    packEquiv b l t = packOf (K := K) b l t := by
  funext w
  show b.equivFun.symm (fun v => t (v, w)) = ∑ v, t (v, w) • b v
  exact b.equivFun_symm_apply (fun v => t (v, w))

/-- Packing at a basis is bijective — the statement Theorem 3.5's emulator
needs, with no hypothesis left over. -/
theorem packOf_bijective (b : Basis (Fin κ → Bool) K L) (l : ℕ) :
    Function.Bijective (packOf (K := K) b l) := by
  have h : packOf (K := K) b l = packEquiv b l :=
    funext fun t => (packEquiv_apply b l t).symm
  rw [h]
  exact (packEquiv b l).toEquiv.bijective

/-- **TOOTH: a repeated coordinate destroys extraction.** If `β` takes the same
value at two distinct cube points, two DISTINCT `K`-witnesses pack to the same
`L`-object. Theorem 3.5's emulator, handed `t'`, cannot say which `t` the
adversary committed — the reduction's conclusion is unavailable, and nothing
about the type of `packOf` reveals it. -/
theorem packOf_not_injective_of_repeat (β : (Fin κ → Bool) → L)
    {v₁ v₂ : Fin κ → Bool} (hne : v₁ ≠ v₂) (heq : β v₁ = β v₂) (l : ℕ) :
    ¬ Function.Injective (packOf (K := K) β l) := by
  intro hinj
  have hpk : packOf (K := K) β l (fun p => if p.1 = v₁ then (1 : K) else 0)
      = packOf (K := K) β l (fun p => if p.1 = v₂ then (1 : K) else 0) := by
    funext w
    simp [packOf, ite_smul, heq]
  have := congrFun (hinj hpk) (v₁, fun _ => false)
  simp [hne] at this

end Packing

/-! ## §3 The `ℓ = κ + ℓ'` form, and the direction error

Ring-switching's arity bookkeeping is `ℓ' = ℓ − κ`. Stated positively: an
`ℓ = κ + ℓ'`-variate `K`-multilinear packs into an `ℓ'`-variate `L`-multilinear.
The cube index splits accordingly. -/

section Arity

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {κ : ℕ}

/-- The `(κ + l)`-cube splits as `B_κ × B_l`. -/
def cubeSplit (κ l : ℕ) : (Fin (κ + l) → Bool) ≃ (Fin κ → Bool) × (Fin l → Bool) :=
  (Equiv.arrowCongr finSumFinEquiv (Equiv.refl Bool)).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin κ) (Fin l) Bool)

/-- **Packing in arity form.** `(B_{κ+ℓ'} → K) ≃ₗ[K] (B_{ℓ'} → L)`: the
coefficient vector of a `(κ+ℓ')`-variate `K`-multilinear is `K`-linearly
equivalent to that of an `ℓ'`-variate `L`-multilinear. -/
noncomputable def packCube (b : Basis (Fin κ → Bool) K L) (l : ℕ) :
    ((Fin (κ + l) → Bool) → K) ≃ₗ[K] ((Fin l → Bool) → L) :=
  (LinearEquiv.funCongrLeft K K (cubeSplit κ l).symm).trans (packEquiv b l)

/-- **Zero embedding overhead, as a dimension identity.** The packed target
carries exactly `2^(κ+ℓ')` `K`-coordinates — the same number the unpacked
`K`-multilinear's coefficient vector carries. This is the paper's "commitment
cost on each `K`-multilinear equals the original scheme's cost on an
`L`-multilinear of equal size in bits", proved rather than asserted, and it is
proved FROM the packing equivalence, so it cannot drift away from it. -/
theorem finrank_packed_eq (b : Basis (Fin κ → Bool) K L) (l : ℕ) :
    Module.finrank K ((Fin l → Bool) → L) = 2 ^ (κ + l) := by
  rw [← (packCube b l).finrank_eq, Module.finrank_fintype_fun_eq_card]
  simp

/-- The source's dimension, for the comparison below. -/
theorem finrank_source_eq (l : ℕ) :
    Module.finrank K ((Fin l → Bool) → K) = 2 ^ l := by
  rw [Module.finrank_fintype_fun_eq_card]; simp

/-- **The element-wise lift's target, measured.** Lifting a `B_ℓ`-indexed
`K`-word coefficientwise into `L` lands in `B_ℓ → L`, which carries
`2^κ · 2^ℓ` `K`-coordinates. -/
theorem finrank_lifted_eq (b : Basis (Fin κ → Bool) K L) (l : ℕ) :
    Module.finrank K ((Fin l → Bool) → L) = 2 ^ κ * 2 ^ l := by
  rw [finrank_packed_eq b l, pow_add]

/-- **The overhead factor, named.** The element-wise lift multiplies the
committed `K`-dimension by `2^κ = [L : K]`; packing leaves it fixed
(`finrank_packed_eq` against `finrank_source_eq` at `l := κ + ℓ'`). `2^κ` IS
"embedding overhead", and it is why `liftWord`-shaped maps point the wrong way
for ring-switching: they are the construction Diamond–Posen §1 rejects. -/
theorem lift_overhead_factor (b : Basis (Fin κ → Bool) K L) (l : ℕ) :
    Module.finrank K ((Fin l → Bool) → L)
      = 2 ^ κ * Module.finrank K ((Fin l → Bool) → K) := by
  rw [finrank_lifted_eq b l, finrank_source_eq]

/-- **TOOTH: the base embedding is not surjective above degree one.** -/
theorem algebraMap_not_surjective (h : 1 < Module.finrank K L) :
    ¬ Function.Surjective (algebraMap K L) := by
  intro hs
  have hb : Function.Bijective (Algebra.linearMap K L) :=
    ⟨(algebraMap K L).injective, hs⟩
  have := (LinearEquiv.ofBijective (Algebra.linearMap K L) hb).finrank_eq
  rw [Module.finrank_self] at this
  omega

/-- **TOOTH: the element-wise lift is refused as a packing map.** `packOf` at a
basis is bijective (`packOf_bijective`); the coefficientwise lift is not even
surjective once `[L : K] > 1`. So no reindexing, no choice of basis, and no
amount of type-level agreement can make the lift serve as Definition 2.2's
packing: it is the wrong direction, and the refusal is a theorem. -/
theorem liftFun_not_surjective {ι : Type*} [Nonempty ι]
    (h : 1 < Module.finrank K L) :
    ¬ Function.Surjective (fun (f : ι → K) (i : ι) => algebraMap K L (f i)) := by
  intro hs
  refine algebraMap_not_surjective h fun y => ?_
  obtain ⟨f, hf⟩ := hs (fun _ => y)
  exact ⟨f (Classical.arbitrary ι), congrFun hf (Classical.arbitrary ι)⟩

end Arity

/-! ## §4 The binary tower supplies the connector

`|T_k| = 2^(2^k)`, so `[T_{j+d} : T_j] = 2^d`: **every sub-level extension of
the binary tower has degree an exact power of two**, and `κ = d` — the packing
arity is literally the number of tower levels crossed. That is the coincidence
ring-switching is built on and the reason `B_κ` (rather than `Fin (2^κ)`) is
the right index type: crossing `d` levels consumes `d` multilinear variables.

The `Algebra` instance is a `local instance` on purpose. `towerAlgebra j 0`
would overlap `Algebra.id` at `d = 0` (`j + 0` reduces to `j`), and a silent
instance diamond there is exactly the class of defect this repo keeps paying
for. Nothing below is stated at `d = 0`; consumers `letI` it. -/

section Tower

/-- The tower level `T_{j+d}` as a `T_j`-algebra, via the chain embedding. -/
@[reducible] noncomputable def towerAlgebra (j d : ℕ) :
    Algebra (binaryTower j) (binaryTower (j + d)) :=
  RingHom.toAlgebra (binaryTowerEmbedChain j d).toRingHom

attribute [local instance] towerAlgebra

/-- **`[T_{j+d} : T_j] = 2^d`.** From the cardinalities alone:
`2^(2^(j+d)) = (2^(2^j))^r` forces `2^j · r = 2^(j+d)`, i.e. `r = 2^d`. -/
theorem towerExt_finrank (j d : ℕ) :
    Module.finrank (binaryTower j) (binaryTower (j + d)) = 2 ^ d := by
  have hcard := Module.natCard_eq_pow_finrank
    (K := binaryTower j) (V := binaryTower (j + d))
  rw [binaryTower_card, binaryTower_card, ← pow_mul] at hcard
  have hexp : 2 ^ (j + d)
      = 2 ^ j * Module.finrank (binaryTower j) (binaryTower (j + d)) :=
    Nat.pow_right_injective (le_refl 2) hcard
  have hj : (0 : ℕ) < 2 ^ j := pow_pos (by norm_num) j
  have : 2 ^ j * 2 ^ d
      = 2 ^ j * Module.finrank (binaryTower j) (binaryTower (j + d)) := by
    rw [← pow_add]; exact hexp
  exact (Nat.eq_of_mul_eq_mul_left hj this).symm

/-- **The tower's cube-indexed basis** — the connector, instantiated. Crossing
`d` levels of the binary tower gives a `B_d`-indexed `T_j`-basis of `T_{j+d}`,
which is precisely Diamond–Posen's `(β_v)_{v ∈ B_κ}` at `κ = d`. -/
noncomputable def towerCubeBasis (j d : ℕ) :
    Basis (Fin d → Bool) (binaryTower j) (binaryTower (j + d)) :=
  cubeBasis _ _ (towerExt_finrank j d)

/-- **Satisfiable keystone — the deployed Binius shape.** `K = T₀ = GF(2)`,
`L = T₇ = GF(2^128)`: degree 128, `κ = 7`, so a bit-valued multilinear packs
seven variables into a `GF(2^128)`-valued one. This is the extension every
Binius deployment actually uses, and the connector exists at it. -/
theorem binius_shape_finrank :
    Module.finrank (binaryTower 0) (binaryTower (0 + 7)) = 128 := by
  rw [towerExt_finrank]; norm_num

/-- The same shape, as an inhabited basis. -/
noncomputable def biniusCubeBasis :
    Basis (Fin 7 → Bool) (binaryTower 0) (binaryTower (0 + 7)) :=
  towerCubeBasis 0 7

/-- **TEETH at the tower: the lift is refused here too.** `[T₇ : T₀] = 128 > 1`,
so the coefficientwise `GF(2) → GF(2^128)` lift is not surjective and cannot be
the packing map for the deployed shape. -/
theorem binius_lift_refused {ι : Type*} [Nonempty ι] :
    ¬ Function.Surjective
        (fun (f : ι → binaryTower 0) (i : ι) =>
          algebraMap (binaryTower 0) (binaryTower (0 + 7)) (f i)) :=
  liftFun_not_surjective (by rw [binius_shape_finrank]; norm_num)

/-- **Zero embedding overhead at the deployed shape.** A `2^ℓ'`-coefficient
`GF(2^128)`-word carries `128 · 2^ℓ'` `GF(2)`-coordinates — exactly the bit
count of the `2^(7+ℓ')`-coefficient `GF(2)`-multilinear it packs. -/
theorem binius_packed_dimension (l : ℕ) :
    Module.finrank (binaryTower 0) ((Fin l → Bool) → binaryTower (0 + 7))
      = 2 ^ (7 + l) :=
  finrank_packed_eq biniusCubeBasis l

end Tower

/-! ## §5 Axiom pins -/

/-- info: 'Minidregg.Theory.no_cubeBasis_of_finrank_ne' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms no_cubeBasis_of_finrank_ne
/-- info: 'Minidregg.Theory.packEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms packEquiv_apply
/-- info: 'Minidregg.Theory.packOf_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms packOf_bijective
/-- info: 'Minidregg.Theory.packOf_not_injective_of_repeat' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms packOf_not_injective_of_repeat
/-- info: 'Minidregg.Theory.finrank_packed_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms finrank_packed_eq
/-- info: 'Minidregg.Theory.lift_overhead_factor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms lift_overhead_factor
/-- info: 'Minidregg.Theory.algebraMap_not_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms algebraMap_not_surjective
/-- info: 'Minidregg.Theory.liftFun_not_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms liftFun_not_surjective
/-- info: 'Minidregg.Theory.towerExt_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms towerExt_finrank
/-- info: 'Minidregg.Theory.binius_shape_finrank' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms binius_shape_finrank
/-- info: 'Minidregg.Theory.binius_lift_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms binius_lift_refused
/-- info: 'Minidregg.Theory.binius_packed_dimension' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms binius_packed_dimension

end Minidregg.Theory
