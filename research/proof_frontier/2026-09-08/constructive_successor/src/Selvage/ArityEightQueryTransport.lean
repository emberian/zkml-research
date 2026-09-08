/- Existing coherent query seeds transport the new one-scalar arity-eight
consumer exactly. The p3 index statement is arithmetic, not Rust refinement. -/
import Selvage.ArityEightBabyBear
import Selvage.P3FriQueryTransport

namespace Minidregg.Selvage.ArityEight
open scoped Classical

/-- Transport any challenge/row event through the existing third binary-level
query projection. Discarded quotient bits cancel exactly in finite probability. -/
theorem coherent_block_uniform {F : Type} [Fintype F] {q : ℕ}
    (p : F × (Fin q → PowerTwoFriLevels 20 3) → Prop) :
    uniformProb (F × (Fin q → PowerTwoFriLevels 20 1))
      (fun x => p (x.1,powerTwoCoherentRound (m := 19) (by decide)
        (⟨2,by decide⟩ : Fin 19) x.2)) =
      uniformProb (F × (Fin q → PowerTwoFriLevels 20 3)) p := by
  let s := powerTwoBatchSplitEquiv (qCount := q) (ell := 20) (m := 19)
    (by decide) (⟨2,by decide⟩ : Fin 19)
  let e : (F × (Fin q → PowerTwoFriLevels 20 1)) ≃
      ((Fin q → Fin (2^2)) × (F × (Fin q → PowerTwoFriLevels 20 3))) := {
    toFun := fun x => ((s x.2).1,(x.1,(s x.2).2))
    invFun := fun x => (x.2.1,s.symm (x.1,x.2.2))
    left_inv := fun x => by simp
    right_inv := fun x => by simp }
  calc
    _ = uniformProb (F × (Fin q → PowerTwoFriLevels 20 1))
        (fun x => p (e x).2) := by
      apply uniformProb_congr
      intro x
      dsimp [e,s]
      have hs := powerTwoBatchSplitEquiv_snd (show 19 ≤ 20 by decide)
        (⟨2,by decide⟩ : Fin 19) x.2
      exact iff_of_eq (congrArg (fun r => p (x.1,r)) hs.symm)
    _ = uniformProb ((Fin q → Fin (2^2)) × (F × (Fin q → PowerTwoFriLevels 20 3)))
        (fun x => p x.2) := uniformProb_equiv e (fun x => p x.2)
    _ = _ := uniformProb_prod_snd p

/-- The p3 query's first width-eight row is exactly the transported coherent
seed at level three: divide its runtime index by eight, then reverse 17 bits. -/
theorem p3_first_block_row (index : Fin (2^20)) :
    (powerTwoRoundIndex (ell := 20) (m := 19) (by decide)
      (⟨2,by decide⟩ : Fin 19) (P3FriQueryTransport.pairSeed 20 index.val)).val =
      Minidregg.Theory.BitReverseFriTransport.reverseIndex 17 (index.val/8) :=
  P3FriQueryTransport.existing_coherent_transport 20 19 (by decide) ⟨2,by decide⟩ index

/-- Actual BabyBear arity-eight crossing under the existing coherent seed
sampler. It uses one scalar beta and a pre-beta injected word. -/
theorem babyBear_coherent_first_injected_crossing
    (f : Fin (2^20) → BabyBearExt4.Ext4) (g : Fin (2^17) → BabyBearExt4.Ext4)
    (next : BabyBearExt4.Ext4 → Fin (2^17) → BabyBearExt4.Ext4) (q : ℕ)
    (hfar : ¬close (2/5:ℝ)
      (reedSolomonCode (BabyBearExt4.MultiplicativeTower.tower.dom 0) (2^19)) f) :
    uniformProb (BabyBearExt4.Ext4 × (Fin q → PowerTwoFriLevels 20 1))
      (fun x => Crossing
        (reedSolomonCode (BabyBearExt4.MultiplicativeTower.tower.dom 3) (2^16)) (1/10:ℝ)
        (fun β i => fold8
          (BabyBearExt4.MultiplicativeTower.tower.data 0 (by decide))
          (BabyBearExt4.MultiplicativeTower.tower.data 1 (by decide))
          (BabyBearExt4.MultiplicativeTower.tower.data 2 (by decide)) f β i + β^8*g i)
        next q (x.1,powerTwoCoherentRound (m := 19) (by decide) (⟨2,by decide⟩ : Fin 19) x.2)) ≤
      (2^20:ℝ)/(BabyBearExt4.modulus^4:ℕ) + (9/10:ℝ)^q := by
  rw [coherent_block_uniform]
  exact BabyBear.first_injected_crossing f g next q hfar

end Minidregg.Selvage.ArityEight


/-- info: 'Minidregg.Selvage.ArityEight.coherent_block_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.coherent_block_uniform

/-- info: 'Minidregg.Selvage.ArityEight.p3_first_block_row' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.p3_first_block_row

/-- info: 'Minidregg.Selvage.ArityEight.babyBear_coherent_first_injected_crossing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.ArityEight.babyBear_coherent_first_injected_crossing

