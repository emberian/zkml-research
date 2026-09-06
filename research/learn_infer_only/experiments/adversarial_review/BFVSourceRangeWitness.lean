/- Reviewer tooth: a coherent alternate correction quotient survives every
integer balance except the necessary correction-remainder range row. -/
import Compiler.FheSourceCertificateWitness

namespace BFVSourceRangeWitness
open Minidregg.Compiler.FheSourceCertificate
open Minidregg.Compiler.FheRnsScale

def alternate : Fin 21 → Nat :=
  let x := sourceValues capturedResidues
  Function.update (Function.update (Function.update (Function.update x
    15 (x 15-1)) 16 (x 16+2^128)) 18 172480) 19 (deployedQ.toNat-1-172480)

theorem correction_range_is_necessary :
    (∀ j : Fin 12, j ≠ 9 →
      leftConstant j+dot (leftMatrix j) alternate =
      rightConstant j+dot (rightMatrix j) alternate) ∧
    ¬ Balanced alternate ∧ alternate 18=172480 := by
  unfold Minidregg.Compiler.FheSourceCertificate.Balanced
  decide

/-- info: 'BFVSourceRangeWitness.correction_range_is_necessary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms BFVSourceRangeWitness.correction_range_is_necessary

end BFVSourceRangeWitness
