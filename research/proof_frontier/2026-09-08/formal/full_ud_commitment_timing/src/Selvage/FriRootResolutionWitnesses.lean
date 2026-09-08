/- Statement witnesses for arbitrary roots, real prefix adaptation, and timing teeth. -/
import Selvage.FriRootResolutionSoundness

namespace Minidregg.Selvage
namespace FriRootResolution
namespace Witnesses

set_option maxHeartbeats 800000

open OpeningResolution ProximityExample

abbrev WitnessRoot (n : ℕ) :=
  ((levels n → ZMod 5) × Bool) ⊕ (levels n → ZMod 5)

def scheme (n : ℕ) : OpeningScheme (WitnessRoot n) (ZMod 5) (levels n) (Option Unit) :=
  transparent (tagged (ZMod 5) (levels n)).toOpeningScheme

/-- A genuinely adaptive strategy: the initial off-image root contains X,
while the transparent terminal word is the challenge itself. -/
def strategy : Strategy (ZMod 5) WitnessRoot
  | 0, _ => Sum.inl (xWord, true)
  | 1, p => Sum.inr (fun _ => p 0)
  | _ + 2, _ => Sum.inr (fun i => i.elim0)

/-- The initial ordinary root has no preimage under the raw tagged commit. -/
theorem initial_root_off_image :
    ¬ ∃ w, (xWord, true) = (tagged (ZMod 5) (levels 0)).commit w := by
  rintro ⟨w, hw⟩
  have htag := congrArg Prod.snd hw
  cases htag

/-- The existing multiplicative folding data folds X to the challenge. -/
theorem fold_x_challenge (a : ZMod 5) : fold data0 xWord a = fun _ => a := by
  have heven : foldEven data0 xWord = fun _ => 0 := by decide
  have hodd : foldOdd data0 xWord = fun _ => 1 := by decide
  funext k
  simp [fold, heven, hodd]

/-- A final word chosen after the first challenge varies with that challenge. -/
theorem adaptive_word_witness (p : Fin 1 → ZMod 5) :
    (resolvedTranscript scheme strategy).word 1 p = fun _ => p 0 := by
  exact word_transparent _ _ _

/-- The adaptive witness is not representable by a single fixed final word. -/
theorem fixed_transcript_falsifier :
    ¬ ∃ w : levels 1 → ZMod 5, ∀ p : Fin 1 → ZMod 5,
      (resolvedTranscript scheme strategy).word 1 p = w := by
  rintro ⟨w, hw⟩
  have hzero := hw (fun _ => 0)
  have hone := hw (fun _ => 1)
  rw [adaptive_word_witness] at hzero hone
  have h := congrFun (hzero.trans hone.symm) (⟨0, by decide⟩ : levels 1)
  norm_num at h

/-- A root selected before any challenge cannot equal that future challenge
on every execution. This refutes moving level zero past challenge zero. -/
theorem future_challenge_falsifier :
    ¬ ∃ w : Unit → ZMod 5, ∀ r : Fin 1 → ZMod 5, w () = r 0 := by
  rintro ⟨w, hw⟩
  have h := (hw (fun _ => 0)).symm.trans (hw (fun _ => 1))
  norm_num at h

/-- The raw verifier premise is inhabited with one actual FRI round, arbitrary
positive or zero query count, an off-image root, and adaptive transparent final word. -/
theorem sampled_acceptance_inhabited (qCount : ℕ) (r : Fin 1 → ZMod 5)
    (Q : FriIndependentQuerySchedule levels 1 qCount) :
    SampledAccepts scheme ldtTower degSched strategy qCount r Q := by
  constructor
  · intro j
    fin_cases j
    let w := fold data0 xWord (r 0)
    refine ⟨fun a => {
      left := xWord (data0.sec (Q 0 a))
      right := xWord (data0.neg (data0.sec (Q 0 a)))
      next := w (Q 0 a)
      leftPath := some ()
      rightPath := some ()
      nextPath := none }, fun a => ?_⟩
    refine ⟨rfl, rfl, ?_, rfl⟩
    change r 0 = fold data0 xWord (r 0) (Q 0 a)
    rw [fold_x_challenge]
  · refine ⟨(fun _ => r 0), ?_, fun _ => ⟨none, rfl⟩⟩
    change (fun _ => r 0) ∈ reedSolomonCode dom1 1
    rw [← fold_x_challenge (r 0)]
    exact fold_preserves_code (d := 1) data0 xWord_mem (r 0)

/-- The witness schemes have proved position binding, including transparent roots. -/
theorem scheme_binding (n : ℕ) : (scheme n).PositionBinding :=
  transparent_binding _ (tagged (ZMod 5) (levels n)).binding

/-- No collision branch is needed for the concrete adaptive witness. -/
theorem witness_no_bad (r : Fin 1 → ZMod 5) : ¬ BadRoots scheme strategy r :=
  no_bad_of_binding scheme scheme_binding strategy r

/-- The proved reduction fires on the actual accepted off-image/adaptive witness. -/
theorem reduction_inhabited (qCount : ℕ) (r : Fin 1 → ZMod 5)
    (Q : FriIndependentQuerySchedule levels 1 qCount) :
    FriAdaptiveSampledAccepts (fun n => idealCommitment (ZMod 5) (levels n))
      ldtTower degSched (resolvedTranscript scheme strategy) qCount r Q ∨
        BadRoots scheme strategy r :=
  sound_reduction scheme ldtTower degSched strategy qCount r Q
    (sampled_acceptance_inhabited qCount r Q)

/-- The reduction actually reaches ideal acceptance on the admitted witness. -/
theorem ideal_acceptance_witness (qCount : ℕ) (r : Fin 1 → ZMod 5)
    (Q : FriIndependentQuerySchedule levels 1 qCount) :
    FriAdaptiveSampledAccepts (fun n => idealCommitment (ZMod 5) (levels n))
      ldtTower degSched (resolvedTranscript scheme strategy) qCount r Q :=
  (reduction_inhabited qCount r Q).resolve_right (witness_no_bad r)

end Witnesses
end FriRootResolution
end Minidregg.Selvage

/-! ## Exact theorem dependency reports -/
/-- info: 'Minidregg.Selvage.FriRootResolution.Witnesses.initial_root_off_image' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.Witnesses.initial_root_off_image
/-- info: 'Minidregg.Selvage.FriRootResolution.Witnesses.fold_x_challenge' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.Witnesses.fold_x_challenge
/-- info: 'Minidregg.Selvage.FriRootResolution.Witnesses.adaptive_word_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.Witnesses.adaptive_word_witness
/-- info: 'Minidregg.Selvage.FriRootResolution.Witnesses.fixed_transcript_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.Witnesses.fixed_transcript_falsifier
/-- info: 'Minidregg.Selvage.FriRootResolution.Witnesses.future_challenge_falsifier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.Witnesses.future_challenge_falsifier
/-- info: 'Minidregg.Selvage.FriRootResolution.Witnesses.sampled_acceptance_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.Witnesses.sampled_acceptance_inhabited
/-- info: 'Minidregg.Selvage.FriRootResolution.Witnesses.scheme_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.Witnesses.scheme_binding
/-- info: 'Minidregg.Selvage.FriRootResolution.Witnesses.witness_no_bad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.Witnesses.witness_no_bad
/-- info: 'Minidregg.Selvage.FriRootResolution.Witnesses.reduction_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.Witnesses.reduction_inhabited
/-- info: 'Minidregg.Selvage.FriRootResolution.Witnesses.ideal_acceptance_witness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.Witnesses.ideal_acceptance_witness
