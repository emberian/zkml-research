/-
# The full-UD coherent budget with arbitrary prefix-selected roots

Reuses the frozen full-UD schedule and actual BabyBear extension carrier.
The additional selected-root double-opening probability remains explicit.
No new numerical security claim or efficient extraction claim is made.
-/
import Selvage.FriRootResolutionSoundness
import Selvage.FullUDSamplingBudget

namespace Minidregg.Selvage
namespace FriRootResolution

section Generic
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {Root Op : ℕ → Type}

/-- The full-UD schedule discharges every gap/fold premise for the raw-root
verifier while preserving the exact binding-failure event. -/
theorem fullUD_coherent_sound
    (S : ∀ n, OpeningScheme (Root n) F (PowerTwoFriLevels 20 n) (Op n))
    (T : FoldingTower F (PowerTwoFriLevels 20) 19)
    (st : Strategy F Root) (qCount : ℕ)
    (hfar0 : ¬ close (2/5 : ℝ)
      (reedSolomonCode (T.dom 0) (fullUDSamplingDegree 0))
      (OpeningResolution.word (S 0) 0 (st 0 (fun i => i.elim0)))) :
    uniformProb ((Fin 19 → F) × (Fin qCount → PowerTwoFriLevels 20 1))
      (fun x => CoherentAccepts S T fullUDSamplingDegree st
        (by decide) qCount x.1 x.2) ≤
      (19 : ℝ) * (2^20 : ℕ) / (Fintype.card F : ℝ) + (94/95 : ℝ)^qCount +
        uniformProb (Fin 19 → F) (BadRoots S st) := by
  exact le_trans (coherent_probability_reduction S T fullUDSamplingDegree st
    (by decide) qCount)
    (add_le_add (fullUDSampling_coherent_sound
      (fun n => idealCommitment F (PowerTwoFriLevels 20 n)) T
      (resolvedTranscript S st) qCount hfar0) le_rfl)
end Generic

section ActualBabyBear
variable {Root Op : ℕ → Type}

/-- The existing concrete carrier/query budget transfers with an explicit,
unpriced binding-event probability. The theorem does not assert total 55-bit security. -/
theorem babyBear_coherent_sound
    (S : ∀ n, OpeningScheme (Root n) BabyBearExt4.Ext4
      (PowerTwoFriLevels 20 n) (Op n))
    (T : FoldingTower BabyBearExt4.Ext4 (PowerTwoFriLevels 20) 19)
    (st : Strategy BabyBearExt4.Ext4 Root)
    (hfar0 : ¬ close (2/5 : ℝ)
      (reedSolomonCode (T.dom 0) (fullUDSamplingDegree 0))
      (OpeningResolution.word (S 0) 0 (st 0 (fun i => i.elim0)))) :
    uniformProb
      ((Fin 19 → BabyBearExt4.Ext4) × (Fin 3603 → PowerTwoFriLevels 20 1))
      (fun x => CoherentAccepts S T fullUDSamplingDegree st
        (by decide) 3603 x.1 x.2) ≤ 1/(2^55 : ℝ) +
      uniformProb (Fin 19 → BabyBearExt4.Ext4) (BadRoots S st) := by
  exact le_trans (coherent_probability_reduction S T fullUDSamplingDegree st
    (by decide) 3603)
    (add_le_add (fullUDSampling_babyBear_55
      (fun n => idealCommitment BabyBearExt4.Ext4 (PowerTwoFriLevels 20 n))
      T (resolvedTranscript S st) hfar0) le_rfl)

/-- The corresponding exact-position-binding specialization needs no
honest-image equation for any level root. Deployment binding remains separate. -/
theorem babyBear_coherent_sound_binding
    (S : ∀ n, OpeningScheme (Root n) BabyBearExt4.Ext4
      (PowerTwoFriLevels 20 n) (Op n))
    (hb : ∀ n, (S n).PositionBinding)
    (T : FoldingTower BabyBearExt4.Ext4 (PowerTwoFriLevels 20) 19)
    (st : Strategy BabyBearExt4.Ext4 Root)
    (hfar0 : ¬ close (2/5 : ℝ)
      (reedSolomonCode (T.dom 0) (fullUDSamplingDegree 0))
      (OpeningResolution.word (S 0) 0 (st 0 (fun i => i.elim0)))) :
    uniformProb
      ((Fin 19 → BabyBearExt4.Ext4) × (Fin 3603 → PowerTwoFriLevels 20 1))
      (fun x => CoherentAccepts S T fullUDSamplingDegree st
        (by decide) 3603 x.1 x.2) ≤ 1/(2^55 : ℝ) := by
  have hbad : uniformProb (Fin 19 → BabyBearExt4.Ext4) (BadRoots S st) = 0 :=
    uniformProb_false (no_bad_of_binding S hb st)
  simpa only [hbad, add_zero] using babyBear_coherent_sound S T st hfar0
end ActualBabyBear

end FriRootResolution
end Minidregg.Selvage

/-! ## Exact theorem dependency reports -/
/-- info: 'Minidregg.Selvage.FriRootResolution.fullUD_coherent_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.fullUD_coherent_sound
/-- info: 'Minidregg.Selvage.FriRootResolution.babyBear_coherent_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.babyBear_coherent_sound
/-- info: 'Minidregg.Selvage.FriRootResolution.babyBear_coherent_sound_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.babyBear_coherent_sound_binding
