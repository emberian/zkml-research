/-
# Theory.BinaryTowerFanPaar — [BTOWER-fanpaar] the Fan–Paar generator recursion
and the fast tower multiplication it enables (why Binius is fast).

Builds on `Theory.BinaryTower` (T_k = `GaloisField 2 (2^k)`, `binaryTowerEmbed`
the level embedding, `FanPaarRecursion` the stated target).

## What is PROVED here (unconditional)

* `fpGen k : T_{k+1}` — the Fan–Paar generator sequence, BUILT (not assumed):
  `fpGen 0` is the concrete witness of `binaryTower_one_fanpaar_base`
  (x₀² + x₀ + 1 = 0 in GF(4)); `fpGen (k+1)` is a genuine root in T_{k+2} of
  X² + embed(fpGen k)·X + 1, produced by `exists_fanpaar_step_root` (an
  irreducible factor of the quadratic is adjoined and embedded over T_{k+1}
  via `FiniteField.nonempty_algHom_of_finrank_dvd`, using [T_{k+2}:T_{k+1}]=2).
* `fpGen_base`, `fpGen_step` — the two RECURSION RELATIONS of
  `FanPaarRecursion`, discharged for ALL k. `fanPaar_relations` packages them.
* `fpGen_ne_zero` / `fpGen_ne_one` / `fpGen_not_in_prime_field` — TEETH: every
  generator lies outside the prime field; the relations are load-bearing.
* `towerMulStep` — the ONE-LEVEL Fan–Paar/Karatsuba multiply: a T_{k+1} product
  via T_k products on coordinate pairs, reduced by fpGen k² = embed(g_k)·fpGen k + 1.
  `towerPack_towerMulStep` proves it EQUALS the field product under the packing
  T_k × T_k → T_{k+1}, (a,b) ↦ embed a + embed b · fpGen k — for ALL k,
  unconditionally. This is the algorithmic content of the Fan–Paar recursion.
* `towerMul` + `towerMul_eq_mul` — at any level where fpGen k ∉ range(embed k)
  (the packing is then a BIJECTION, `towerPack_bijective`), the packed
  step IS the field multiplication of T_{k+1}.
* Keystones at the concrete bottom: `fpGen_zero_not_mem_range` /
  `fpGen_one_not_mem_range` (x₀ ∉ GF(2) in GF(4); x₁ ∉ GF(4) in GF(16) — the
  Wiedemann irreducibility, computed via pow_card), hence `towerMul` with
  `towerMul_eq_mul` is REAL on GF(4) and GF(16), and
  `fpGen_adjoin_zero` / `fpGen_adjoin_one` (x₀ generates GF(4), x₁ generates
  GF(16) — the generation clause at the bottom two levels).

## Honest residuals (STATED, named, not proved)

* **[BTOWER-fanpaar-basis]** `FanPaarTowerBasis` — fpGen k ∉ range(embed k) for
  ALL k: X² + gₖ·X + 1 stays irreducible at every level (Wiedemann 1988's trace
  induction Tr(xₖ) = 1). Proved here at k = 0, 1; the general chain is the ONE
  residual from which everything else follows.
* **[BTOWER-fanpaar-gen]** `FanPaarGeneration` — adjoin(fpGen k) = ⊤ for all k.
  `fanPaarGeneration_of_towerBasis` REDUCES it to the basis residual (the
  induction step `fpGen_adjoin_succ` is proved); with it,
  `fanPaarRecursion_of_generation` DISCHARGES `FanPaarRecursion` outright.
* **[BTOWER-mult-full]** `TowerMulFull` — the packing is bijective at every
  level (so the recursive multiply is total all the way down).
  `towerMulFull_of_towerBasis` reduces this, too, to `FanPaarTowerBasis`.

Candidate-independent FIELD MATH — imports Mathlib + Theory only (boundary
enforced by `scripts/check-import-boundary.sh`).
-/
import Theory.BinaryTower
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.SplittingField.Construction
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.Set.Card
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.LinearCombination

namespace Minidregg.Theory

open Polynomial

/-! ### Existence of the step root: X² + c·X + 1 splits one level up -/

/-- **The Fan–Paar step root exists.** For any c ∈ T_{k+1}, the quadratic
X² + embed(c)·X + 1 has a root in T_{k+2}: an irreducible factor of the
quadratic over T_{k+1} has degree 1 or 2, both dividing [T_{k+2} : T_{k+1}] = 2,
so the field it cuts out embeds T_{k+1}-linearly into T_{k+2}
(`FiniteField.nonempty_algHom_of_finrank_dvd`), carrying its root along. -/
theorem exists_fanpaar_step_root (k : ℕ) (c : binaryTower (k + 1)) :
    ∃ y : binaryTower (k + 2), y ^ 2 + binaryTowerEmbed (k + 1) c * y + 1 = 0 := by
  classical
  letI : Algebra (binaryTower (k + 1)) (binaryTower (k + 2)) :=
    (binaryTowerEmbed (k + 1)).toRingHom.toAlgebra
  haveI : IsScalarTower (ZMod 2) (binaryTower (k + 1)) (binaryTower (k + 2)) :=
    IsScalarTower.of_algebraMap_eq fun x => ((binaryTowerEmbed (k + 1)).commutes x).symm
  -- the relative degree is 2
  have hFL : Module.finrank (binaryTower (k + 1)) (binaryTower (k + 2)) = 2 := by
    have h := Module.finrank_mul_finrank (ZMod 2) (binaryTower (k + 1)) (binaryTower (k + 2))
    rw [binaryTower_finrank, binaryTower_finrank] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos (k + 1)) (by rw [h, pow_succ])
  set p : (binaryTower (k + 1))[X] := X ^ 2 + C c * X + 1 with hp
  have hpm : p.Monic := by rw [hp]; monicity!
  have hpd : p.natDegree = 2 := by rw [hp]; compute_degree!
  have hpu : ¬IsUnit p := by
    intro h
    have := natDegree_eq_zero_of_isUnit h
    omega
  have hqi : Irreducible p.factor := irreducible_factor p
  haveI : Fact (Irreducible p.factor) := ⟨hqi⟩
  have hqdvd : p.factor ∣ p := factor_dvd_of_not_isUnit hpu
  have hq0 : p.factor ≠ 0 := hqi.ne_zero
  have hqd2 : p.factor.natDegree ∣ 2 := by
    have hle : p.factor.natDegree ≤ 2 := by
      have := natDegree_le_of_dvd hqdvd hpm.ne_zero
      omega
    have hpos : 0 < p.factor.natDegree := hqi.natDegree_pos
    rcases (by omega : p.factor.natDegree = 1 ∨ p.factor.natDegree = 2) with h | h
    · rw [h]; norm_num
    · rw [h]
  have hfin : Module.finrank (binaryTower (k + 1)) (AdjoinRoot p.factor) =
      p.factor.natDegree := by
    rw [(AdjoinRoot.powerBasis hq0).finrank, AdjoinRoot.powerBasis_dim]
  obtain ⟨ψ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := binaryTower (k + 1)) (K := AdjoinRoot p.factor) (L := binaryTower (k + 2))
    (by rw [hfin, hFL]; exact hqd2)
  refine ⟨ψ (AdjoinRoot.root p.factor), ?_⟩
  have hroot0 : aeval (AdjoinRoot.root p.factor) p = 0 := by
    obtain ⟨r, hr⟩ := hqdvd
    have hz : aeval (AdjoinRoot.root p.factor) p.factor = 0 := by
      rw [aeval_def, AdjoinRoot.algebraMap_eq]
      exact AdjoinRoot.eval₂_root p.factor
    calc aeval (AdjoinRoot.root p.factor) p
        = aeval (AdjoinRoot.root p.factor) (p.factor * r) := congrArg _ hr
      _ = 0 := by rw [map_mul, hz, zero_mul]
  have hy : aeval (ψ (AdjoinRoot.root p.factor)) p = 0 := by
    rw [aeval_algHom_apply, hroot0, map_zero]
  have hy' : aeval (ψ (AdjoinRoot.root p.factor))
      (X ^ 2 + C c * X + 1 : (binaryTower (k + 1))[X]) = 0 :=
    (congrArg (aeval (ψ (AdjoinRoot.root p.factor))) hp).symm.trans hy
  simpa only [map_add, map_mul, map_pow, map_one, aeval_X, aeval_C,
    RingHom.algebraMap_toAlgebra, AlgHom.coe_toRingHom] using hy'

/-! ### The Fan–Paar generator sequence, BUILT -/

/-- **The Fan–Paar generators.** `fpGen 0` is the concrete GF(4) witness of
`binaryTower_one_fanpaar_base`; `fpGen (k+1)` is a root in T_{k+2} of
X² + embed(fpGen k)·X + 1 (`exists_fanpaar_step_root`). Chosen once via
`choose` — any root works (the two roots are y and y⁻¹). -/
noncomputable def fpGen : (k : ℕ) → binaryTower (k + 1)
  | 0 => binaryTower_one_fanpaar_base.choose
  | k + 1 => (exists_fanpaar_step_root k (fpGen k)).choose

/-- **Base recursion relation**: x₀² + x₀ + 1 = 0 in GF(4). -/
theorem fpGen_base : fpGen 0 ^ 2 + fpGen 0 + 1 = 0 :=
  binaryTower_one_fanpaar_base.choose_spec.1

theorem fpGen_zero_ne_zero : fpGen 0 ≠ 0 :=
  binaryTower_one_fanpaar_base.choose_spec.2.1

theorem fpGen_zero_ne_one : fpGen 0 ≠ 1 :=
  binaryTower_one_fanpaar_base.choose_spec.2.2

/-- **Step recursion relation**: x_{k+1}² + embed(x_k)·x_{k+1} + 1 = 0 in
T_{k+2} — for ALL k. -/
theorem fpGen_step (k : ℕ) :
    fpGen (k + 1) ^ 2 + binaryTowerEmbed (k + 1) (fpGen k) * fpGen (k + 1) + 1 = 0 :=
  (exists_fanpaar_step_root k (fpGen k)).choose_spec

/-- TEETH: no generator is 0 (a root of X² + c·X + 1 at 0 would give 1 = 0). -/
theorem fpGen_ne_zero : ∀ k, fpGen k ≠ 0
  | 0 => fpGen_zero_ne_zero
  | k + 1 => fun h => by
    have hstep := fpGen_step k
    rw [h] at hstep
    simp at hstep

/-- TEETH: no generator is 1. -/
theorem fpGen_ne_one : ∀ k, fpGen k ≠ 1
  | 0 => fpGen_zero_ne_one
  | k + 1 => fun h => by
    have hstep := fpGen_step k
    rw [h] at hstep
    have h2 : (2 : binaryTower (k + 2)) = 0 := binaryTower_two_eq_zero (k + 2)
    have hx0 : binaryTowerEmbed (k + 1) (fpGen k) = 0 := by
      linear_combination hstep - h2
    have hzero : fpGen k = 0 := by
      apply binaryTowerEmbed_injective (k + 1)
      rw [hx0, map_zero]
    exact fpGen_ne_zero k hzero

/-- **TEETH: every generator lies OUTSIDE the prime field** — the recursion
relation is load-bearing, not satisfied by a scalar. -/
theorem fpGen_not_in_prime_field (k : ℕ) (b : ZMod 2) :
    algebraMap (ZMod 2) (binaryTower (k + 1)) b ≠ fpGen k := by
  have hb : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  rcases hb b with rfl | rfl
  · rw [map_zero]; exact (fpGen_ne_zero k).symm
  · rw [map_one]; exact (fpGen_ne_one k).symm

/-! ### The one-level Fan–Paar / Karatsuba multiplication step -/

/-- The reduction coefficient at level k: the relation is
fpGen k² = embed(towerMulCoeff k)·fpGen k + 1, with coefficient 1 at the
bottom and fpGen (k−1) above (this is what unifies base and step). -/
noncomputable def towerMulCoeff : (k : ℕ) → binaryTower k
  | 0 => 1
  | k + 1 => fpGen k

@[simp] theorem towerMulCoeff_zero : towerMulCoeff 0 = 1 := rfl

@[simp] theorem towerMulCoeff_succ (k : ℕ) : towerMulCoeff (k + 1) = fpGen k := rfl

/-- The unified quadratic relation at every level:
fpGen k² + embed(towerMulCoeff k)·fpGen k + 1 = 0. -/
theorem fpGen_quadratic (k : ℕ) :
    fpGen k ^ 2 + binaryTowerEmbed k (towerMulCoeff k) * fpGen k + 1 = 0 := by
  cases k with
  | zero => simpa using fpGen_base
  | succ k => exact fpGen_step k

/-- **The packing** T_k × T_k → T_{k+1}: (a, b) ↦ embed(a) + embed(b)·fpGen k —
the Fan–Paar coordinate representation of one tower level over the previous. -/
noncomputable def towerPack (k : ℕ) (a : binaryTower k × binaryTower k) :
    binaryTower (k + 1) :=
  binaryTowerEmbed k a.1 + binaryTowerEmbed k a.2 * fpGen k

/-- **The one-level Fan–Paar/Karatsuba multiply** on coordinate pairs:
(a₁ + a₂y)(b₁ + b₂y) with y² = g·y + 1 needs the three Karatsuba products
a₁b₁, a₂b₂, (a₁+a₂)(b₁+b₂) plus one multiplication by the reduction
coefficient g = towerMulCoeff k — all in T_k. This recursive structure is the
fast tower arithmetic (each level costs ~3 multiplications of the level below,
plus a cheap coefficient multiply). -/
noncomputable def towerMulStep (k : ℕ) (a b : binaryTower k × binaryTower k) :
    binaryTower k × binaryTower k :=
  (a.1 * b.1 + a.2 * b.2,
    (a.1 + a.2) * (b.1 + b.2) + a.1 * b.1 + a.2 * b.2 + a.2 * b.2 * towerMulCoeff k)

/-- **CORRECTNESS of the fast multiply, for ALL k, unconditionally**: under the
packing, the one-level Fan–Paar step IS the field product of T_{k+1}. -/
theorem towerPack_towerMulStep (k : ℕ) (a b : binaryTower k × binaryTower k) :
    towerPack k (towerMulStep k a b) = towerPack k a * towerPack k b := by
  obtain ⟨a₁, a₂⟩ := a
  obtain ⟨b₁, b₂⟩ := b
  have hy := fpGen_quadratic k
  have h2 : (2 : binaryTower (k + 1)) = 0 := binaryTower_two_eq_zero (k + 1)
  simp only [towerPack, towerMulStep, map_add, map_mul]
  linear_combination
    (-(binaryTowerEmbed k a₂ * binaryTowerEmbed k b₂)) * hy +
      (binaryTowerEmbed k a₂ * binaryTowerEmbed k b₂ +
        (binaryTowerEmbed k a₁ * binaryTowerEmbed k b₁ +
          binaryTowerEmbed k a₂ * binaryTowerEmbed k b₂ +
          binaryTowerEmbed k a₂ * binaryTowerEmbed k b₂ *
            binaryTowerEmbed k (towerMulCoeff k)) * fpGen k) * h2

/-- The packing is INJECTIVE whenever fpGen k avoids the embedded previous
level (else fpGen k = embed((a₁+b₁)/(a₂+b₂)) would land in the range). -/
theorem towerPack_injective {k : ℕ} (h : fpGen k ∉ (binaryTowerEmbed k).range) :
    Function.Injective (towerPack k) := by
  have h2k : (2 : binaryTower k) = 0 := binaryTower_two_eq_zero k
  have h2 : (2 : binaryTower (k + 1)) = 0 := binaryTower_two_eq_zero (k + 1)
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hab
  simp only [towerPack] at hab
  by_cases hd : a₂ = b₂
  · subst hd
    have h1 : binaryTowerEmbed k a₁ = binaryTowerEmbed k b₁ := by
      linear_combination hab
    have := binaryTowerEmbed_injective k h1
    subst this
    rfl
  · exfalso
    apply h
    have hne : a₂ + b₂ ≠ 0 := fun h0 => hd (by linear_combination h0 - b₂ * h2k)
    have hEne : binaryTowerEmbed k (a₂ + b₂) ≠ 0 := fun h0 =>
      hne (binaryTowerEmbed_injective k (by rw [h0, map_zero]))
    rw [AlgHom.mem_range]
    refine ⟨(a₁ + b₁) / (a₂ + b₂), ?_⟩
    rw [map_div₀, div_eq_iff hEne, map_add, map_add]
    linear_combination -hab + (binaryTowerEmbed k a₁ - binaryTowerEmbed k b₂ * fpGen k) * h2

/-- The packing is a BIJECTION where fpGen k avoids the embedded previous level
(injective + |T_k|² = |T_{k+1}|): T_{k+1} = T_k ⊕ T_k·fpGen k, the tower
basis. -/
theorem towerPack_bijective {k : ℕ} (h : fpGen k ∉ (binaryTowerEmbed k).range) :
    Function.Bijective (towerPack k) := by
  rw [Nat.bijective_iff_injective_and_card]
  refine ⟨towerPack_injective h, ?_⟩
  rw [Nat.card_prod, binaryTower_card, binaryTower_card, ← pow_add]
  congr 1
  rw [pow_succ, mul_two]

/-- Unpack: the inverse of the packing (exists where the packing is a
bijection). -/
noncomputable def towerUnpack {k : ℕ} (h : fpGen k ∉ (binaryTowerEmbed k).range)
    (u : binaryTower (k + 1)) : binaryTower k × binaryTower k :=
  (Equiv.ofBijective _ (towerPack_bijective h)).symm u

theorem towerPack_towerUnpack {k : ℕ} (h : fpGen k ∉ (binaryTowerEmbed k).range)
    (u : binaryTower (k + 1)) : towerPack k (towerUnpack h u) = u :=
  (Equiv.ofBijective _ (towerPack_bijective h)).apply_symm_apply u

/-- **The fast tower multiplication** at a level with the tower basis: unpack
both operands into T_k coordinates, run the one-level Fan–Paar/Karatsuba step,
pack the result. -/
noncomputable def towerMul {k : ℕ} (h : fpGen k ∉ (binaryTowerEmbed k).range)
    (u v : binaryTower (k + 1)) : binaryTower (k + 1) :=
  towerPack k (towerMulStep k (towerUnpack h u) (towerUnpack h v))

/-- **CORRECTNESS: the fast multiply IS the field product** — proven against
the actual field structure of `binaryTower (k+1)`, no model gap. -/
theorem towerMul_eq_mul {k : ℕ} (h : fpGen k ∉ (binaryTowerEmbed k).range)
    (u v : binaryTower (k + 1)) : towerMul h u v = u * v := by
  unfold towerMul
  rw [towerPack_towerMulStep, towerPack_towerUnpack, towerPack_towerUnpack]

/-! ### The concrete bottom: the tower basis at k = 0 and k = 1 -/

/-- T₀ = GF(2) concretely: every element is 0 or 1 (from u² = u). -/
theorem binaryTower_zero_eq_zero_or_one (u : binaryTower 0) : u = 0 ∨ u = 1 := by
  letI : Fintype (binaryTower 0) := Fintype.ofFinite _
  have hcard : Fintype.card (binaryTower 0) = 2 := by
    rw [← Nat.card_eq_fintype_card]; exact binaryTower_zero_card
  have hpow : u ^ Fintype.card (binaryTower 0) = u := FiniteField.pow_card u
  rw [hcard] at hpow
  have h2 : (2 : binaryTower 0) = 0 := binaryTower_two_eq_zero 0
  have key : u * (u + 1) = 0 := by linear_combination hpow + u * h2
  rcases mul_eq_zero.mp key with h | h
  · exact Or.inl h
  · exact Or.inr (by linear_combination h - h2)

/-- **The tower basis at the bottom**: x₀ ∉ embed(GF(2)) — X² + X + 1 is
irreducible over GF(2) (its root is neither 0 nor 1). -/
theorem fpGen_zero_not_mem_range : fpGen 0 ∉ (binaryTowerEmbed 0).range := by
  rw [AlgHom.mem_range]
  rintro ⟨u, hu⟩
  rcases binaryTower_zero_eq_zero_or_one u with rfl | rfl
  · rw [map_zero] at hu; exact fpGen_zero_ne_zero hu.symm
  · rw [map_one] at hu; exact fpGen_zero_ne_one hu.symm

/-- **The tower basis at level one (Wiedemann irreducibility, computed)**:
x₁ ∉ embed(GF(4)) — X² + x₀·X + 1 has no root in GF(4). A root u would give
u⁴ = u + x₀ (reducing u⁴ by u² = x₀u + 1 and x₀² = x₀ + 1), so u⁴ = u forces
x₀ = 0, contradiction. -/
theorem fpGen_one_not_mem_range : fpGen 1 ∉ (binaryTowerEmbed 1).range := by
  rw [AlgHom.mem_range]
  rintro ⟨u, hu⟩
  have hstep := fpGen_step 0
  rw [← hu] at hstep
  have hF : u ^ 2 + fpGen 0 * u + 1 = 0 := by
    apply binaryTowerEmbed_injective 1
    rw [map_add, map_add, map_mul, map_pow, map_one, map_zero]
    exact hstep
  letI : Fintype (binaryTower 1) := Fintype.ofFinite _
  have hcard : Fintype.card (binaryTower 1) = 4 := by
    rw [← Nat.card_eq_fintype_card]; exact binaryTower_one_card
  have hpow : u ^ (4 : ℕ) = u := by rw [← hcard]; exact FiniteField.pow_card u
  have h2 : (2 : binaryTower 1) = 0 := binaryTower_two_eq_zero 1
  have hx := fpGen_base
  refine fpGen_zero_ne_zero ?_
  linear_combination hpow - (u ^ 2 - fpGen 0 * u + fpGen 0 ^ 2 - 1) * hF +
    ((fpGen 0 - 1) * u + 1) * hx - ((fpGen 0 - 1) * u + 1) * h2

/-- KEYSTONE (satisfiable, [BTOWER-mult-full] at k = 0): the level-0 packing
GF(2) × GF(2) → GF(4) is a bijection — the tower basis {1, x₀} is real. -/
theorem towerPack_zero_bijective : Function.Bijective (towerPack 0) :=
  towerPack_bijective fpGen_zero_not_mem_range

/-- KEYSTONE (satisfiable, [BTOWER-mult-full] at k = 1): the level-1 packing
GF(4) × GF(4) → GF(16) is a bijection — the tower basis {1, x₁} is real. -/
theorem towerPack_one_bijective : Function.Bijective (towerPack 1) :=
  towerPack_bijective fpGen_one_not_mem_range

/-- **The fast multiply on GF(4) is real**: the level-0 packing is a bijection
and `towerMul fpGen_zero_not_mem_range` multiplies GF(4) via GF(2)
coordinates — keystone instance of `towerMul_eq_mul`. -/
theorem towerMul_gf4_eq_mul (u v : binaryTower 1) :
    towerMul fpGen_zero_not_mem_range u v = u * v :=
  towerMul_eq_mul fpGen_zero_not_mem_range u v

/-- **The fast multiply on GF(16) is real**: the level-1 packing is a bijection
and `towerMul fpGen_one_not_mem_range` multiplies GF(16) via GF(4)
coordinates — keystone instance of `towerMul_eq_mul`. -/
theorem towerMul_gf16_eq_mul (u v : binaryTower 2) :
    towerMul fpGen_one_not_mem_range u v = u * v :=
  towerMul_eq_mul fpGen_one_not_mem_range u v

/-! ### Generation: adjoin(fpGen k) = ⊤ — base, induction step, and the
concrete first two levels -/

/-- Every subalgebra of a tower level is closed under inverses
(x⁻¹ = x^(q−2) — powers stay inside). -/
theorem binaryTower_subalgebra_inv_mem {m : ℕ}
    (A : Subalgebra (ZMod 2) (binaryTower m)) {x : binaryTower m} (hx : x ∈ A) :
    x⁻¹ ∈ A := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [inv_zero]; exact A.zero_mem
  · letI : Fintype (binaryTower m) := Fintype.ofFinite _
    have hone : x ^ (Fintype.card (binaryTower m) - 1) = 1 :=
      FiniteField.pow_card_sub_one_eq_one x hx0
    have hcard : 1 < Fintype.card (binaryTower m) := Fintype.one_lt_card
    have hinv : x⁻¹ = x ^ (Fintype.card (binaryTower m) - 2) := by
      apply inv_eq_of_mul_eq_one_right
      rw [← pow_succ']
      rw [show Fintype.card (binaryTower m) - 2 + 1 =
        Fintype.card (binaryTower m) - 1 from by omega]
      exact hone
    rw [hinv]
    exact pow_mem hx _

/-- **Counting criterion for ⊤**: a subalgebra of T_m with more than
√|T_m| = 2^(2^m − 1)·√2 elements (stated squared: |A|² > 2^(2^m)) is
everything. A is an intermediate FIELD (inverse-closed), so |T_m| = |A|^d;
|A|² > |T_m| forces d = 1. -/
theorem binaryTower_subalgebra_eq_top {m : ℕ}
    {A : Subalgebra (ZMod 2) (binaryTower m)}
    (h : 2 ^ 2 ^ m < Nat.card A ^ 2) : A = ⊤ := by
  set E : IntermediateField (ZMod 2) (binaryTower m) :=
    A.toIntermediateField fun x hx => binaryTower_subalgebra_inv_mem A hx with hE
  have hset : (E : Set (binaryTower m)) = (A : Set (binaryTower m)) := rfl
  have hcardEA : Nat.card E = Nat.card A :=
    congrArg (fun s : Set (binaryTower m) => Nat.card s) hset
  have htower : Nat.card (binaryTower m) =
      Nat.card E ^ Module.finrank E (binaryTower m) :=
    Module.natCard_eq_pow_finrank
  rw [binaryTower_card] at htower
  rw [← hcardEA] at h
  have ha1 : 1 ≤ Nat.card E := Nat.card_pos
  have h2m : 1 < 2 ^ 2 ^ m := Nat.one_lt_two_pow (pow_ne_zero m two_ne_zero)
  rcases Nat.lt_or_ge (Module.finrank E (binaryTower m)) 2 with hd | hd
  · interval_cases hdm : Module.finrank ↥E (binaryTower m)
    · rw [pow_zero] at htower; omega
    · rw [pow_one] at htower
      -- |A| = |T_m|: the subalgebra is everything
      have hAcard : Nat.card A = 2 ^ 2 ^ m := by rw [← hcardEA]; omega
      apply SetLike.ext'
      rw [Algebra.coe_top]
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ Set.finite_univ
      rw [Set.ncard_univ, binaryTower_card, ← Nat.card_coe_set_eq]
      exact le_of_eq hAcard.symm
  · exfalso
    have hle : Nat.card E ^ 2 ≤ Nat.card E ^ Module.finrank E (binaryTower m) :=
      Nat.pow_le_pow_right ha1 hd
    omega

/-- **Generation at the bottom**: x₀ generates GF(4) over GF(2) —
{0, 1, x₀} are three distinct elements of adjoin(x₀), and 3² > 4. -/
theorem fpGen_adjoin_zero :
    Algebra.adjoin (ZMod 2) {fpGen 0} = (⊤ : Subalgebra (ZMod 2) (binaryTower 1)) := by
  set A := Algebra.adjoin (ZMod 2) {fpGen 0} with hA
  apply binaryTower_subalgebra_eq_top
  have hsub : ({0, 1, fpGen 0} : Set (binaryTower 1)) ⊆ (A : Set (binaryTower 1)) := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · exact A.zero_mem
    · exact A.one_mem
    · exact Algebra.self_mem_adjoin_singleton _ _
  have hcard3 : ({0, 1, fpGen 0} : Set (binaryTower 1)).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        push Not
        exact ⟨zero_ne_one, (fpGen_zero_ne_zero).symm⟩),
      Set.ncard_insert_of_notMem (by
        simp only [Set.mem_singleton_iff]
        exact (fpGen_zero_ne_one).symm),
      Set.ncard_singleton]
  have hle : 3 ≤ (A : Set (binaryTower 1)).ncard := by
    rw [← hcard3]
    exact Set.ncard_le_ncard hsub (Set.toFinite _)
  have hAA : Nat.card A = (A : Set (binaryTower 1)).ncard := Nat.card_coe_set_eq _
  have : (2 : ℕ) ^ 2 ^ 1 = 4 := by norm_num
  rw [this]
  nlinarith
/-- **The generation induction step**: if fpGen (k+1) avoids the embedded
T_{k+1} and fpGen k generates T_{k+1}, then fpGen (k+1) generates T_{k+2}.
The adjoin contains y and y⁻¹, hence embed(fpGen k) = y + y⁻¹, hence (by the
induction hypothesis, mapped through the embedding) all of embed(T_{k+1}) —
strictly more, so its cardinality beats √|T_{k+2}| and the counting criterion
closes it. -/
theorem fpGen_adjoin_succ {k : ℕ}
    (hnm : fpGen (k + 1) ∉ (binaryTowerEmbed (k + 1)).range)
    (ih : Algebra.adjoin (ZMod 2) {fpGen k} =
      (⊤ : Subalgebra (ZMod 2) (binaryTower (k + 1)))) :
    Algebra.adjoin (ZMod 2) {fpGen (k + 1)} =
      (⊤ : Subalgebra (ZMod 2) (binaryTower (k + 2))) := by
  set A := Algebra.adjoin (ZMod 2) {fpGen (k + 1)} with hA
  have hy : fpGen (k + 1) ∈ A := Algebra.self_mem_adjoin_singleton _ _
  have hyinv : (fpGen (k + 1))⁻¹ ∈ A := binaryTower_subalgebra_inv_mem A hy
  -- embed(fpGen k) = y + y⁻¹ lands in A
  have hy0 : fpGen (k + 1) ≠ 0 := fpGen_ne_zero (k + 1)
  have h2 : (2 : binaryTower (k + 2)) = 0 := binaryTower_two_eq_zero (k + 2)
  have hc : binaryTowerEmbed (k + 1) (fpGen k) = fpGen (k + 1) + (fpGen (k + 1))⁻¹ := by
    have hrel := fpGen_step k
    have hmul : fpGen (k + 1) *
        (fpGen (k + 1) + binaryTowerEmbed (k + 1) (fpGen k)) = 1 := by
      linear_combination hrel - h2
    rw [inv_eq_of_mul_eq_one_right hmul]
    linear_combination (-(fpGen (k + 1))) * h2
  have hcA : binaryTowerEmbed (k + 1) (fpGen k) ∈ A := by
    rw [hc]; exact A.add_mem hy hyinv
  -- the whole embedded previous level is inside A
  have hrange : (binaryTowerEmbed (k + 1)).range ≤ A := by
    rw [← Algebra.map_top, ← ih, AlgHom.map_adjoin, Set.image_singleton]
    exact Algebra.adjoin_le (Set.singleton_subset_iff.mpr hcA)
  -- strictly: fpGen (k+1) ∈ A \ range
  have hss : ((binaryTowerEmbed (k + 1)).range : Set (binaryTower (k + 2))) ⊂
      (A : Set (binaryTower (k + 2))) :=
    ⟨hrange, fun habs => hnm (habs hy)⟩
  have hlt : ((binaryTowerEmbed (k + 1)).range : Set (binaryTower (k + 2))).ncard <
      (A : Set (binaryTower (k + 2))).ncard :=
    Set.ncard_lt_ncard hss (Set.toFinite _)
  have hr : ((binaryTowerEmbed (k + 1)).range : Set (binaryTower (k + 2))).ncard =
      2 ^ 2 ^ (k + 1) := by
    rw [AlgHom.coe_range, ← Nat.card_coe_set_eq,
      Nat.card_range_of_injective (binaryTowerEmbed_injective (k + 1)), binaryTower_card]
  apply binaryTower_subalgebra_eq_top
  have hAA : Nat.card A = (A : Set (binaryTower (k + 2))).ncard := Nat.card_coe_set_eq _
  have hpow : (2 : ℕ) ^ 2 ^ (k + 2) = (2 ^ 2 ^ (k + 1)) ^ 2 := by
    rw [← pow_mul, ← pow_succ]
  rw [hpow]
  have : 2 ^ 2 ^ (k + 1) < Nat.card A := by omega
  exact Nat.pow_lt_pow_left this (by norm_num)

/-- **Generation at level one (keystone)**: x₁ generates GF(16) over GF(2). -/
theorem fpGen_adjoin_one :
    Algebra.adjoin (ZMod 2) {fpGen 1} = (⊤ : Subalgebra (ZMod 2) (binaryTower 2)) :=
  fpGen_adjoin_succ fpGen_one_not_mem_range fpGen_adjoin_zero

/-! ### Named residuals and the conditional discharge of FanPaarRecursion -/

/-- **[BTOWER-fanpaar-basis] (RESIDUAL).** The tower-basis / irreducibility
chain: EVERY Fan–Paar generator avoids the embedded previous level — i.e.
X² + gₖ·X + 1 is irreducible over T_{k+1} at every level. TRUE (Wiedemann
1988, by the trace induction Tr_{T_{k+1}}(xₖ) = 1); PROVED here at k = 0
(`fpGen_zero_not_mem_range`) and k = 1 (`fpGen_one_not_mem_range`). This is
the ONE remaining gap: both [BTOWER-fanpaar-gen] and [BTOWER-mult-full]
reduce to it (theorems below). -/
def FanPaarTowerBasis : Prop :=
  ∀ k, fpGen k ∉ (binaryTowerEmbed k).range

/-- **[BTOWER-fanpaar-gen] (RESIDUAL).** The generation clause of
`FanPaarRecursion` for the BUILT generator sequence: adjoin(fpGen k) = ⊤ at
every level. PROVED at k = 0 (`fpGen_adjoin_zero`) and k = 1
(`fpGen_adjoin_one`); reduced to [BTOWER-fanpaar-basis] in general
(`fanPaarGeneration_of_towerBasis` — the induction step is proved). -/
def FanPaarGeneration : Prop :=
  ∀ k, Algebra.adjoin (ZMod 2) {fpGen k} =
    (⊤ : Subalgebra (ZMod 2) (binaryTower (k + 1)))

/-- **[BTOWER-mult-full] (RESIDUAL).** The packing is bijective at EVERY level:
T_{k+1} = T_k ⊕ T_k·fpGen k throughout the tower, so the recursive fast
multiply is total all the way down. PROVED at k = 0, 1 (via
`towerPack_bijective` + the two basis keystones); reduced to
[BTOWER-fanpaar-basis] in general (`towerMulFull_of_towerBasis`). -/
def TowerMulFull : Prop :=
  ∀ k, Function.Bijective (towerPack k)

/-- [BTOWER-fanpaar-gen] reduces to [BTOWER-fanpaar-basis]: given the
irreducibility chain, generation follows by induction (base
`fpGen_adjoin_zero`, step `fpGen_adjoin_succ`). -/
theorem fanPaarGeneration_of_towerBasis (h : FanPaarTowerBasis) :
    FanPaarGeneration := by
  intro k
  induction k with
  | zero => exact fpGen_adjoin_zero
  | succ k ih => exact fpGen_adjoin_succ (h (k + 1)) ih

/-- [BTOWER-mult-full] reduces to [BTOWER-fanpaar-basis]. -/
theorem towerMulFull_of_towerBasis (h : FanPaarTowerBasis) : TowerMulFull :=
  fun k => towerPack_bijective (h k)

/-- **The recursion relations of [BTOWER-fanpaar], DISCHARGED for all k**: a
generator sequence satisfying the base and step clauses of
`FanPaarRecursion` exists — it is `fpGen`, built above. (The generation
clause is [BTOWER-fanpaar-gen].) -/
theorem fanPaar_relations :
    ∃ gen : (k : ℕ) → binaryTower (k + 1),
      (gen 0 ^ 2 + gen 0 + 1 = 0) ∧
      (∀ k, gen (k + 1) ^ 2 +
        binaryTowerEmbed (k + 1) (gen k) * gen (k + 1) + 1 = 0) :=
  ⟨fpGen, fpGen_base, fpGen_step⟩

/-- **Conditional discharge of [BTOWER-fanpaar]**: `FanPaarRecursion` follows
from the generation residual alone — the witness is `fpGen` with its proved
relations. -/
theorem fanPaarRecursion_of_generation (h : FanPaarGeneration) :
    FanPaarRecursion :=
  ⟨fpGen, fpGen_base, fpGen_step, h⟩

/-- **Conditional discharge of [BTOWER-fanpaar] from the ONE sharp residual**:
the irreducibility chain [BTOWER-fanpaar-basis] implies the full
`FanPaarRecursion`. -/
theorem fanPaarRecursion_of_towerBasis (h : FanPaarTowerBasis) :
    FanPaarRecursion :=
  fanPaarRecursion_of_generation (fanPaarGeneration_of_towerBasis h)

end Minidregg.Theory
