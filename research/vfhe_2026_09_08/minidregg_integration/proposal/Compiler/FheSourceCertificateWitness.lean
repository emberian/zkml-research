/- A side-effect-free, kernel-checked actual source matrix witness. The larger
full emitted-assignment checker replay is recorded execution evidence separately. -/
import Compiler.FheSourceCertificateLayout
namespace Minidregg.Compiler.FheSourceCertificate
open Minidregg.Compiler.FheRnsScale
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

def sourceValues (r : Fin 6 → ℤ) : Fin 21 → ℕ := fun j =>
  let cv := honestCertificate r
  let y := deployedOutput r % deployedQ
  match j.val with
  | 0 => (r 0).toNat | 1 => (r 1).toNat | 2 => (r 2).toNat
  | 3 => (r 3).toNat | 4 => (r 4).toNat | 5 => (r 5).toNat
  | 6 => (deployedBase 0-1-r 0).toNat | 7 => (deployedBase 1-1-r 1).toNat
  | 8 => (deployedBase 2-1-r 2).toNat | 9 => (deployedBase 3-1-r 3).toNat
  | 10 => (deployedBase 4-1-r 4).toNat | 11 => (deployedBase 5-1-r 5).toNat
  | 12 => cv.v.toNat | 13 => cv.garnerRemainder.toNat
  | 14 => (2*(2^126)-1-cv.garnerRemainder).toNat
  | 15 => (cv.w+wOffset).toNat | 16 => cv.correctionRemainder.toNat
  | 17 => (2*(2^127)-1-cv.correctionRemainder).toNat
  | 18 => y.toNat | 19 => (deployedQ-1-y).toNat
  | _ => (cv.outputQuotient+uOffset).toNat

/-- Kernel-checked nonzero matrix witness and capacity inhabitation; emitted checker
acceptance of this same witness is executed below and recorded separately. -/
theorem captured_balance_inhabited : Balanced (sourceValues capturedResidues) ∧
    (∀ j, sourceValues capturedResidues j < 64^22) ∧
    sourceValues capturedResidues 18=172481 := by
  unfold Balanced
  decide

end Minidregg.Compiler.FheSourceCertificate

-- AXIOM PINS: actual checked print output.

/-- info: 'Minidregg.Compiler.FheSourceCertificate.captured_balance_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Compiler.FheSourceCertificate.captured_balance_inhabited
