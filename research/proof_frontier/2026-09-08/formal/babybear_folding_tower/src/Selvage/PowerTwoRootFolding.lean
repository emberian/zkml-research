/-
# Existing binary FoldingTower from a certified power-of-two root

The level types are existing PowerTwoFriLevels. Domains are natural powers;
squaring reduces exponents modulo the next size, and negation adds half the
current size. This matches the existing coherent sampler's modulo indexing.
No bit-reversed runtime array equivalence is asserted here.
-/
import Selvage.HalfThresholdFriCoherent
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

namespace Minidregg.Selvage
namespace PowerTwoRootFolding

variable {F : Type*} [Field F] {ell m : ℕ} {g : F}

/-- Root at level n, obtained by n squarings of the initial domain root. -/
def levelRoot (g : F) (n : ℕ) : F := g^(2^n)

/-- Statement-first interface: exact natural-power domains and modulo projection. -/
def TowerContract (g : F) (T : FoldingTower F (PowerTwoFriLevels ell) m) : Prop :=
  (∀ n i, T.dom n i = (levelRoot g n)^i.val) ∧
    ∀ j (hj : j < m) i, ((T.data j hj).sq i).val = i.val % 2^(ell-(j+1))

/-- Each supported level root has the exact shrinking order. -/
theorem levelRoot_primitive (hg : IsPrimitiveRoot g (2^ell))
    (n : ℕ) (hn : n ≤ ell) : IsPrimitiveRoot (levelRoot g n) (2^(ell-n)) := by
  apply IsPrimitiveRoot.pow (by positivity : 0 < 2^ell) hg
  rw [← pow_add]
  congr 1
  omega

/-- Natural exponents reduce modulo the actual order. -/
theorem levelRoot_pow_mod (hg : IsPrimitiveRoot g (2^ell))
    (n : ℕ) (hn : n ≤ ell) (a : ℕ) :
    (levelRoot g n)^(a % 2^(ell-n)) = (levelRoot g n)^a := by
  simpa only [← (levelRoot_primitive hg n hn).eq_orderOf] using
    pow_mod_orderOf (levelRoot g n) a

/-- Existing level types embedded into the field by natural generator powers.
The proof handles even the singleton levels after the tower endpoint. -/
def domain (hg : IsPrimitiveRoot g (2^ell)) (n : ℕ) : PowerTwoFriLevels ell n ↪ F where
  toFun i := (levelRoot g n)^i.val
  inj' := by
    intro i j hij
    apply Fin.ext
    by_cases hn : n ≤ ell
    · exact (levelRoot_primitive hg n hn).pow_inj i.isLt j.isLt hij
    · have hz : ell-n = 0 := Nat.sub_eq_zero_of_le (by omega)
      have hi := i.isLt
      have hj := j.isLt
      simp only [hz, pow_zero] at hi hj
      omega

/-- A binary transition halves the domain size exactly. -/
theorem size_halves (n : ℕ) (hn : n < ell) :
    2^(ell-n) = 2^(ell-(n+1))*2 := by
  rw [show ell-n = (ell-(n+1))+1 by omega, pow_succ]

/-- Projection to the squared domain: reduce the exponent modulo half-size. -/
def squareIndex (ell n : ℕ) (i : PowerTwoFriLevels ell n) :
    PowerTwoFriLevels ell (n+1) :=
  ⟨i.val % 2^(ell-(n+1)), Nat.mod_lt _ (by positivity)⟩

/-- Choose the root in the first natural-order half. -/
def sectionIndex (n : ℕ) (hn : n < ell) (k : PowerTwoFriLevels ell (n+1)) :
    PowerTwoFriLevels ell n :=
  ⟨k.val, by have hk := k.isLt; rw [size_halves n hn]; omega⟩

/-- Negation is a half-turn in the natural exponent index. -/
def negativeIndex (ell n : ℕ) (i : PowerTwoFriLevels ell n) :
    PowerTwoFriLevels ell n :=
  ⟨(i.val+2^(ell-(n+1))) % 2^(ell-n), Nat.mod_lt _ (by positivity)⟩

/-- The opposite half's representative of a selected fibre. -/
def pairedIndex (n : ℕ) (hn : n < ell) (k : PowerTwoFriLevels ell (n+1)) :
    PowerTwoFriLevels ell n :=
  ⟨k.val+2^(ell-(n+1)), by have hk := k.isLt; rw [size_halves n hn]; omega⟩

/-- Repeated squaring advances the level root exactly once. -/
theorem levelRoot_succ (g : F) (n : ℕ) : levelRoot g (n+1) = (levelRoot g n)^2 := by
  unfold levelRoot
  rw [← pow_mul, pow_succ]

/-- A half-turn of each nonterminal level is -1. -/
theorem levelRoot_half_turn (hg : IsPrimitiveRoot g (2^ell))
    (n : ℕ) (hn : n < ell) : (levelRoot g n)^(2^(ell-(n+1))) = -1 := by
  apply IsPrimitiveRoot.eq_neg_one_of_two_right
  exact IsPrimitiveRoot.pow (by positivity : 0 < 2^(ell-n))
    (levelRoot_primitive hg n (Nat.le_of_lt hn)) (size_halves n hn)

/-- Negation of a selected first-half representative is the matching second-half index. -/
theorem negative_section (n : ℕ) (hn : n < ell) (k : PowerTwoFriLevels ell (n+1)) :
    negativeIndex ell n (sectionIndex n hn k) = pairedIndex n hn k := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt (pairedIndex n hn k).isLt

/-- Construct the existing FoldingData, deriving all fibre and denominator laws. -/
def data (hg : IsPrimitiveRoot g (2^ell)) (htwo : (2 : F) ≠ 0)
    (n : ℕ) (hn : n < ell) : FoldingData F (domain hg n) (domain hg (n+1)) where
  neg := negativeIndex ell n
  dom_neg := by
    intro i
    change (levelRoot g n)^((i.val+2^(ell-(n+1))) % 2^(ell-n)) =
      -(levelRoot g n)^i.val
    rw [levelRoot_pow_mod hg n (Nat.le_of_lt hn), pow_add, levelRoot_half_turn hg n hn]
    ring
  sq := squareIndex ell n
  domSq_sq := by
    intro i
    change (levelRoot g (n+1))^(i.val % 2^(ell-(n+1))) = ((levelRoot g n)^i.val)^2
    rw [levelRoot_pow_mod hg (n+1) (by omega), levelRoot_succ]
    exact pow_right_comm _ _ _
  sec := sectionIndex n hn
  sq_sec := by
    intro k
    apply Fin.ext
    exact Nat.mod_eq_of_lt k.isLt
  dom_ne_zero := fun i => pow_ne_zero _ (pow_ne_zero _ (hg.ne_zero (by positivity)))
  two_ne := htwo

/-- The actual existing FoldingTower, with coherent level embeddings shared definitionally. -/
def tower (hg : IsPrimitiveRoot g (2^ell)) (htwo : (2 : F) ≠ 0)
    (hm : m ≤ ell) : FoldingTower F (PowerTwoFriLevels ell) m where
  dom := domain hg
  data := fun j hj => data hg htwo j (lt_of_lt_of_le hj hm)

/-- The constructed tower realizes its exact-domain/index contract. -/
theorem tower_contract (hg : IsPrimitiveRoot g (2^ell)) (htwo : (2 : F) ≠ 0)
    (hm : m ≤ ell) : TowerContract g (tower hg htwo hm) :=
  ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩

/-- Existing coherent modulo indices select exactly the iterated squared domain point. -/
theorem coherent_index_powers (hg : IsPrimitiveRoot g (2^ell)) (hm : m ≤ ell)
    (j : Fin m) (seed : PowerTwoFriLevels ell 1) :
    (domain hg (j+1)) (powerTwoRoundIndex hm j seed) =
      ((domain hg 1) seed)^(2^(j : ℕ)) := by
  change (levelRoot g (j+1))^(seed.val % 2^(ell-(j+1))) =
    ((levelRoot g 1)^seed.val)^(2^(j : ℕ))
  rw [levelRoot_pow_mod hg (j+1) (by omega)]
  have hroot : levelRoot g (j+1) = (levelRoot g 1)^(2^(j : ℕ)) := by
    unfold levelRoot
    rw [← pow_mul]
    congr 1
    simp [pow_succ, Nat.mul_comm]
  rw [hroot]
  exact pow_right_comm _ _ _

/-- Natural-order fold equality with the actual half-separated source entries. -/
theorem fold_pair (hg : IsPrimitiveRoot g (2^ell)) (htwo : (2 : F) ≠ 0)
    (n : ℕ) (hn : n < ell) (w : PowerTwoFriLevels ell n → F) (a : F)
    (k : PowerTwoFriLevels ell (n+1)) :
    fold (data hg htwo n hn) w a k =
      (w (sectionIndex n hn k) + w (pairedIndex n hn k))/2 +
        a*((w (sectionIndex n hn k) - w (pairedIndex n hn k)) /
          (2*(levelRoot g n)^k.val)) := by
  change (w (sectionIndex n hn k) + w (negativeIndex ell n (sectionIndex n hn k)))/2 +
    a*((w (sectionIndex n hn k) - w (negativeIndex ell n (sectionIndex n hn k))) /
      (2*(domain hg n) (sectionIndex n hn k))) = _
  rw [negative_section]
  rfl

end PowerTwoRootFolding
end Minidregg.Selvage

/-! ## Exact theorem dependency reports -/
/-- info: 'Minidregg.Selvage.PowerTwoRootFolding.levelRoot_primitive' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.PowerTwoRootFolding.levelRoot_primitive
/-- info: 'Minidregg.Selvage.PowerTwoRootFolding.levelRoot_pow_mod' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.PowerTwoRootFolding.levelRoot_pow_mod
/-- info: 'Minidregg.Selvage.PowerTwoRootFolding.size_halves' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.PowerTwoRootFolding.size_halves
/-- info: 'Minidregg.Selvage.PowerTwoRootFolding.levelRoot_succ' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.PowerTwoRootFolding.levelRoot_succ
/-- info: 'Minidregg.Selvage.PowerTwoRootFolding.levelRoot_half_turn' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.PowerTwoRootFolding.levelRoot_half_turn
/-- info: 'Minidregg.Selvage.PowerTwoRootFolding.negative_section' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.PowerTwoRootFolding.negative_section
/-- info: 'Minidregg.Selvage.PowerTwoRootFolding.tower_contract' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.PowerTwoRootFolding.tower_contract
/-- info: 'Minidregg.Selvage.PowerTwoRootFolding.coherent_index_powers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.PowerTwoRootFolding.coherent_index_powers
/-- info: 'Minidregg.Selvage.PowerTwoRootFolding.fold_pair' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.PowerTwoRootFolding.fold_pair
