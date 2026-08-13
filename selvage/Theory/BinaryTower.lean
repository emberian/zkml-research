/-
# Theory.BinaryTower — [OB-8-tower] the binary-tower field substrate (Binius path).

The Fan–Paar / Wiedemann binary tower: T₀ = GF(2) and each level a quadratic
extension, T_{k+1} = T_k[x]/(x² + x_k·x + 1), so T_k = GF(2^(2^k)). This is the
alternative deployed-field substrate to BabyBear⁴ — the GF(2)-tower path that
Binius-style arithmetization rides (bits ARE field elements; embedding overhead
collapses).

Candidate-independent FIELD MATH — imports Mathlib only (boundary enforced by
`scripts/check-import-boundary.sh`).

## What is PROVED here (mathlib reuse, no re-derivation)

* `binaryTower k` — the level-k carrier, **mathlib's `GaloisField 2 (2 ^ k)`**
  (the splitting field of `X^(2^(2^k)) − X` over `ZMod 2`): a REAL field
  construction, reused rather than re-derived. Field/CharP/Finite/Algebra
  instances flow from mathlib's derived instances.
* `binaryTower_card` — |T_k| = 2^(2^k); `binaryTower_finrank` — [T_k : GF(2)] = 2^k.
* `binaryTower_char_two` + teeth `binaryTower_one_add_one_eq_zero` (1 + 1 = 0).
* `binaryTowerEmbed k : T_k →ₐ[GF(2)] T_{k+1}` — the level embedding (a real
  field hom, from `FiniteField.nonempty_algHom_of_finrank_dvd`; 2^k ∣ 2^(k+1)),
  `binaryTowerEmbed_injective`, and TEETH `binaryTowerEmbed_not_surjective`
  (every level is a PROPER extension — the tower genuinely grows).
* `binaryTowerEmbedChain j d : T_j →ₐ[GF(2)] T_{j+d}` — the tower AS a chain.
* Keystones: T₀ = GF(2), T₁ = GF(4), T₂ = GF(16) (cards 2/4/16 computed);
  `binaryTower_one_properly_extends_gf2` (GF(4) has an element outside the
  prime field); `binaryTower_one_fanpaar_base` (∃ x ∈ GF(4), x² + x + 1 = 0,
  x ∉ {0,1} — the BASE of the Fan–Paar recursion, actually inhabited).
* `binaryTower_rs_eval_injective` — evaluation at n distinct tower points is
  injective on polynomials of degree < n: the abstract Theory-side half of the
  Reed–Solomon bridge.

## Honest residuals (STATED, named, not proved)

* **[BTOWER-fanpaar]** `FanPaarRecursion` — the explicit presentation: a
  generator sequence x_k with x₀² + x₀ + 1 = 0, x_{k+1}² + x_k·x_{k+1} + 1 = 0,
  each generating its level over GF(2). (True for any choice of level
  embeddings — Wiedemann 1988; the quadratic X² + x_k·X + 1 is irreducible over
  T_{k+1} and T_{k+2} is its splitting field over the embedded T_{k+1}. The
  base clause IS discharged concretely: `binaryTower_one_fanpaar_base`.)
  Discharging the full recursion is what yields the O(2^k log-ish)
  tower-multiplication algorithm Binius uses; without it we have the fields and
  the tower but not the FAST arithmetic.
* **[BTOWER-rs]** `TowerRSDistance` (the Theory-side distance statement) — RS
  over T_k is the Binius code substrate: degree-< d evaluation words at n ≤
  2^(2^k) distinct points form an MDS code of distance n − d + 1. The
  Theory-side injectivity half is proved (`binaryTower_rs_eval_injective`); the
  REAL residual is the Selvage-side wiring — instantiating Selvage/ReedSolomon at
  alphabet `binaryTower k` — which this file CANNOT state (Theory imports
  Mathlib only; the boundary law forbids naming Selvage). That instantiation is
  the intended bridge and lands on the Selvage side.
-/
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.SetTheory.Cardinal.Finite

namespace Minidregg.Theory

/-- Level `k` of the binary tower: the field with `2^(2^k)` elements, carried by
**mathlib's `GaloisField 2 (2 ^ k)`** — the splitting field of `X^(2^(2^k)) − X`
over `ZMod 2`. A reducible alias so every mathlib instance (Field, `CharP _ 2`,
`Finite`, `Algebra (ZMod 2)`, …) and theorem about `GaloisField` applies
directly: maximal reuse, zero re-derivation. -/
abbrev binaryTower (k : ℕ) : Type := GaloisField 2 (2 ^ k)

/-! ### The field, its size, its characteristic -/

/-- |T_k| = 2^(2^k): level `k` really is GF(2^(2^k)). -/
theorem binaryTower_card (k : ℕ) : Nat.card (binaryTower k) = 2 ^ 2 ^ k :=
  GaloisField.card 2 (2 ^ k) (pow_ne_zero k (by norm_num))

/-- [T_k : GF(2)] = 2^k — the GF(2)-dimension doubles each level. -/
theorem binaryTower_finrank (k : ℕ) :
    Module.finrank (ZMod 2) (binaryTower k) = 2 ^ k :=
  GaloisField.finrank 2 (pow_ne_zero k (by norm_num))

/-- Every tower level has characteristic 2 (mathlib's derived instance,
re-exported as a theorem). -/
theorem binaryTower_char_two (k : ℕ) : CharP (binaryTower k) 2 :=
  inferInstance

/-- TEETH for characteristic 2: `1 + 1 = 0` — genuinely a GF(2)-algebra, not a
field that merely carries a `CharP` label. -/
theorem binaryTower_one_add_one_eq_zero (k : ℕ) :
    (1 : binaryTower k) + 1 = 0 :=
  CharTwo.add_self_eq_zero 1

/-- `2 = 0` at every level. -/
theorem binaryTower_two_eq_zero (k : ℕ) : (2 : binaryTower k) = 0 :=
  CharTwo.two_eq_zero

/-! ### The tower structure: level embeddings -/

/-- **The level embedding** T_k ↪ T_{k+1}: a GF(2)-algebra homomorphism (hence a
field embedding). Exists because [T_k : GF(2)] = 2^k divides 2^(k+1) =
[T_{k+1} : GF(2)] (`FiniteField.nonempty_algHom_of_finrank_dvd`); chosen once
via `Classical.choice` (finite-field embeddings are non-canonical — any Galois
conjugate works equally). -/
noncomputable def binaryTowerEmbed (k : ℕ) :
    binaryTower k →ₐ[ZMod 2] binaryTower (k + 1) :=
  Classical.choice <| FiniteField.nonempty_algHom_of_finrank_dvd <| by
    rw [binaryTower_finrank, binaryTower_finrank]
    exact pow_dvd_pow 2 (Nat.le_succ k)

/-- The level embedding is injective (any ring hom out of a field is). -/
theorem binaryTowerEmbed_injective (k : ℕ) :
    Function.Injective (binaryTowerEmbed k) :=
  (binaryTowerEmbed k).toRingHom.injective

/-- **TEETH: the tower genuinely grows.** No level embedding is surjective —
T_k sits inside T_{k+1} as a PROPER subfield (2^(2^k) < 2^(2^(k+1))). The
tower is a real chain, not a ladder of isomorphisms. -/
theorem binaryTowerEmbed_not_surjective (k : ℕ) :
    ¬ Function.Surjective (binaryTowerEmbed k) := by
  intro hs
  have hle : Nat.card (binaryTower (k + 1)) ≤ Nat.card (binaryTower k) :=
    Nat.card_le_card_of_surjective _ hs
  rw [binaryTower_card, binaryTower_card] at hle
  exact absurd hle <| not_le.mpr <|
    Nat.pow_lt_pow_right one_lt_two (Nat.pow_lt_pow_right one_lt_two k.lt_succ_self)

/-- The tower as a CHAIN: the composite embedding T_j ↪ T_{j+d}, iterating the
level embeddings. `d = 0` is the identity; `d+1` composes one more level. -/
noncomputable def binaryTowerEmbedChain (j : ℕ) :
    (d : ℕ) → (binaryTower j →ₐ[ZMod 2] binaryTower (j + d))
  | 0 => AlgHom.id _ _
  | d + 1 => (binaryTowerEmbed (j + d)).comp (binaryTowerEmbedChain j d)

/-- Every chain embedding is injective. -/
theorem binaryTowerEmbedChain_injective (j d : ℕ) :
    Function.Injective (binaryTowerEmbedChain j d) :=
  (binaryTowerEmbedChain j d).toRingHom.injective

/-! ### Keystones (satisfiable): the concrete bottom of the tower -/

/-- T₀ = GF(2): the base of the tower has exactly 2 elements. -/
theorem binaryTower_zero_card : Nat.card (binaryTower 0) = 2 := by
  rw [binaryTower_card]; norm_num

/-- T₁ = GF(4), concretely: 4 elements. -/
theorem binaryTower_one_card : Nat.card (binaryTower 1) = 4 := by
  rw [binaryTower_card]; norm_num

/-- T₂ = GF(16), concretely: 16 elements. -/
theorem binaryTower_two_card : Nat.card (binaryTower 2) = 16 := by
  rw [binaryTower_card]; norm_num

/-- A nonzero element of GF(4) (the field is nontrivial). -/
theorem binaryTower_one_nonzero : (1 : binaryTower 1) ≠ 0 := one_ne_zero

/-- A nonzero element of GF(16). -/
theorem binaryTower_two_nonzero : (1 : binaryTower 2) ≠ 0 := one_ne_zero

/-- **TEETH for the concrete inclusion T₁ ⊊ T₂**: 4 < 16, so the embedding
`binaryTowerEmbed 1 : GF(4) →ₐ GF(16)` (injective, not surjective by
`binaryTowerEmbed_not_surjective 1`) is a proper inclusion. -/
theorem binaryTower_one_card_lt_two_card :
    Nat.card (binaryTower 1) < Nat.card (binaryTower 2) := by
  rw [binaryTower_one_card, binaryTower_two_card]; omega

/-- **TEETH: GF(4) properly extends GF(2)** — an element outside the prime
field exists (by counting: the prime field contributes at most 2 of the 4
elements). The first extension step is genuine. -/
theorem binaryTower_one_properly_extends_gf2 :
    ∃ x : binaryTower 1, ∀ b : ZMod 2, algebraMap (ZMod 2) (binaryTower 1) b ≠ x := by
  by_contra h
  push Not at h
  have hle : Nat.card (binaryTower 1) ≤ Nat.card (ZMod 2) :=
    Nat.card_le_card_of_surjective _ h
  rw [binaryTower_one_card, Nat.card_zmod] at hle
  omega

/-- **The Fan–Paar BASE is inhabited**: GF(4) contains x with `x² + x + 1 = 0`
and `x ∉ {0, 1}` — the generator x₀ of the first tower level exists concretely.
(Proof: any element outside the prime field works, since `x⁴ = x` factors as
`x·(x+1)·(x²+x+1) = 0` in characteristic 2.) This discharges the base clause of
[BTOWER-fanpaar] `FanPaarRecursion`; the inductive step remains residual. -/
theorem binaryTower_one_fanpaar_base :
    ∃ x : binaryTower 1, x ^ 2 + x + 1 = 0 ∧ x ≠ 0 ∧ x ≠ 1 := by
  obtain ⟨x, hx⟩ := binaryTower_one_properly_extends_gf2
  have hx0 : x ≠ 0 := fun h => hx 0 (by rw [map_zero, h])
  have hx1 : x ≠ 1 := fun h => hx 1 (by rw [map_one, h])
  letI : Fintype (binaryTower 1) := Fintype.ofFinite _
  have hcard4 : Fintype.card (binaryTower 1) = 4 := by
    rw [← Nat.card_eq_fintype_card]; exact binaryTower_one_card
  have hpow : x ^ (4 : ℕ) = x := by rw [← hcard4]; exact FiniteField.pow_card x
  have h2 : (2 : binaryTower 1) = 0 := CharTwo.two_eq_zero
  have key : x * ((x + 1) * (x ^ 2 + x + 1)) = 0 := by
    linear_combination hpow + (x ^ 3 + x ^ 2 + x) * h2
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h hx0
  rcases mul_eq_zero.mp h with h | h
  · exact absurd (by linear_combination h - h2) hx1
  · exact ⟨x, h, hx0, hx1⟩

/-! ### The Reed–Solomon bridge (Theory-side half) -/

/-- **RS evaluation over the tower is injective** on low-degree polynomials:
two polynomials of degree < n agreeing at n distinct points of T_k are equal.
This is the abstract, candidate-independent half of the Binius code substrate —
an RS codeword over T_k (the evaluation table of a low-degree polynomial)
determines its message polynomial. The Selvage-side instantiation is
[BTOWER-rs]. -/
theorem binaryTower_rs_eval_injective {k n : ℕ} {α : Fin n → binaryTower k}
    (hα : Function.Injective α) {p q : Polynomial (binaryTower k)}
    (hp : p.degree < n) (hq : q.degree < n)
    (h : ∀ i, p.eval (α i) = q.eval (α i)) : p = q := by
  refine Polynomial.eq_of_degrees_lt_of_eval_index_eq Finset.univ hα.injOn ?_ ?_
    fun i _ => h i
  · simpa using hp
  · simpa using hq

/-! ### Named residuals — stated, satisfiable, NOT proved -/

/-- **[BTOWER-fanpaar] (RESIDUAL).** The explicit Fan–Paar / Wiedemann
presentation of the tower: a generator sequence xₖ ∈ T_{k+1} with

* base: x₀² + x₀ + 1 = 0 (inhabited: `binaryTower_one_fanpaar_base`),
* step: x_{k+1}² + xₖ·x_{k+1} + 1 = 0 (each level = previous level adjoin one
  root of X² + xₖ·X + 1, read through the level embedding),
* generation: each xₖ generates its level as a GF(2)-algebra.

Satisfiable (Wiedemann 1988): X² + xₖ·X + 1 is irreducible over T_{k+1}, and
T_{k+2} — the unique quadratic extension inside the algebraic closure — splits
it, for ANY choice of level embedding; xₖ generates because
x_{k−1} = xₖ + xₖ⁻¹ recovers the whole chain. Discharging this is what yields
the fast recursive tower-multiplication algorithm (the Binius arithmetic);
until then we have the fields and the tower, not the FAST multiplication. -/
def FanPaarRecursion : Prop :=
  ∃ gen : (k : ℕ) → binaryTower (k + 1),
    (gen 0 ^ 2 + gen 0 + 1 = 0) ∧
    (∀ k, gen (k + 1) ^ 2 + binaryTowerEmbed (k + 1) (gen k) * gen (k + 1) + 1 = 0) ∧
    (∀ k, Algebra.adjoin (ZMod 2) {gen k} = (⊤ : Subalgebra (ZMod 2) (binaryTower (k + 1))))

/-- **[BTOWER-rs] (RESIDUAL).** Reed–Solomon over the tower is the Binius code
substrate: words of degree-< d polynomials evaluated at n distinct points of
T_k (n ≤ 2^(2^k) points exist, by `binaryTower_card`) form a distance-(n−d+1)
code — two distinct codewords disagree in MORE than n − d positions (stated
`n < Nat.card {disagreement positions} + d`). The injectivity consequence is
already proved
(`binaryTower_rs_eval_injective`); this full distance statement, and above all
its Selvage-side instantiation (Selvage/ReedSolomon at alphabet `binaryTower k`,
which the Theory boundary forbids naming here), is the residual bridge. -/
def TowerRSDistance : Prop :=
  ∀ (k d n : ℕ) (α : Fin n → binaryTower k), Function.Injective α →
    ∀ p q : Polynomial (binaryTower k), p.degree < d → q.degree < d → d ≤ n →
      p ≠ q →
      n < Nat.card {i : Fin n // p.eval (α i) ≠ q.eval (α i)} + d

end Minidregg.Theory
