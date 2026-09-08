/-
[DERIVED statement-first] The bit-reversed binary runtime query's pair seed
feeds the existing powerTwoRoundIndex, without changing the tower or sampler.
The 20-bit premise witness and wrong-row falsifier below exercise this exact map.
This is index arithmetic, not a challenger or Rust execution refinement.
-/
import Theory.BitReverseFriTransport
import Selvage.HalfThresholdFriCoherent

namespace Minidregg.Selvage.P3FriQueryTransport

open Minidregg.Theory.BitReverseFriTransport

set_option autoImplicit false

def pairSeed (ell index : Nat) : PowerTwoFriLevels ell 1 :=
  ⟨reverseIndex (ell - 1) (index / 2), reverseIndex_lt _ _⟩

def ExistingCoherentTransport : Prop :=
  ∀ (ell m : Nat) (hm : m ≤ ell) (j : Fin m) (index : Fin (2 ^ ell)),
    (powerTwoRoundIndex hm j (pairSeed ell index.val)).val =
      reverseIndex (ell - (j.val + 1)) (index.val / 2 ^ (j.val + 1))

theorem existing_coherent_transport : ExistingCoherentTransport := by
  intro ell m hm j index
  exact binary_coherent_index ell j.val index.val (by omega) index.isLt

theorem actual_dimension_premises :
    19 ≤ 20 ∧ 18 < 19 ∧ 181 < 2 ^ 20 := by decide +kernel

theorem actual_dimension_subject :
    (powerTwoRoundIndex (ell := 20) (m := 19) (by decide)
      (⟨2, by decide⟩ : Fin 19) (pairSeed 20 181)).val =
      reverseIndex 17 (181 / 8) :=
  existing_coherent_transport 20 19 (by decide) ⟨2, by decide⟩ ⟨181, by decide⟩

theorem natural_untransported_index_refused :
    (powerTwoRoundIndex (ell := 20) (m := 19) (by decide)
      (⟨2, by decide⟩ : Fin 19) (pairSeed 20 181)).val ≠ 181 % 2 ^ 17 := by
  decide +kernel

#print axioms existing_coherent_transport
#print axioms actual_dimension_premises
#print axioms actual_dimension_subject
#print axioms natural_untransported_index_refused

end Minidregg.Selvage.P3FriQueryTransport
