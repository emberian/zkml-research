/-
# Finite coherent-query soundness for arbitrary prefix-selected roots

The additional term is the probability that a root selected in this execution
admits two accepted values. It is deliberately unpriced and uses semantic
canonical resolution, not an efficient cryptographic extractor. The FRI
challenge/query term is exactly the existing coherent consumer's bound.
-/
import Selvage.FriRootResolution

namespace Minidregg.Selvage
namespace FriRootResolution

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {Root Op : ℕ → Type} {ell m : ℕ}

/-- Raw acceptance with the existing coherent modulo query schedule. -/
def CoherentAccepts
    (S : ∀ n, OpeningScheme (Root n) F (PowerTwoFriLevels ell n) (Op n))
    (T : FoldingTower F (PowerTwoFriLevels ell) m) (deg : ℕ → ℕ)
    (st : Strategy F Root) (hmell : m ≤ ell) (qCount : ℕ)
    (r : Fin m → F) (seed : Fin qCount → PowerTwoFriLevels ell 1) : Prop :=
  SampledAccepts S T deg st qCount r (powerTwoCoherentSchedule hmell seed)

omit [DecidableEq F] in
/-- Lossless finite event reduction, before inserting any proximity or
binding estimate. Original opening witnesses are retained by the raw event. -/
theorem coherent_probability_reduction
    (S : ∀ n, OpeningScheme (Root n) F (PowerTwoFriLevels ell n) (Op n))
    (T : FoldingTower F (PowerTwoFriLevels ell) m) (deg : ℕ → ℕ)
    (st : Strategy F Root) (hmell : m ≤ ell) (qCount : ℕ) :
    uniformProb ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => CoherentAccepts S T deg st hmell qCount x.1 x.2) ≤
    uniformProb ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => FriAdaptiveCoherentAccepts
        (fun n => idealCommitment F (PowerTwoFriLevels ell n)) T deg
        (resolvedTranscript S st) hmell qCount x.1 x.2) +
    uniformProb (Fin m → F) (BadRoots S st) := by
  have hsplit := le_trans (uniformProb_mono fun (x : (Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1)) hx =>
    sound_reduction S T deg st qCount x.1
      (powerTwoCoherentSchedule hmell x.2) hx) (uniformProb_or_le _ _)
  have hbad : uniformProb ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => BadRoots S st x.1) = uniformProb (Fin m → F) (BadRoots S st) := by
    let e := Equiv.prodComm (Fin m → F) (Fin qCount → PowerTwoFriLevels ell 1)
    calc
      _ = uniformProb ((Fin qCount → PowerTwoFriLevels ell 1) × (Fin m → F))
          (fun x => BadRoots S st x.2) := by
        simpa [e] using uniformProb_equiv e (fun x => BadRoots S st x.2)
      _ = _ := uniformProb_prod_snd _
  simpa only [hbad] using hsplit

/-- Existing coherent FRI soundness plus the explicit selected-root binding
failure probability. No honest-image or future-independent-word premise. -/
theorem coherent_sound
    (S : ∀ n, OpeningScheme (Root n) F (PowerTwoFriLevels ell n) (Op n))
    (T : FoldingTower F (PowerTwoFriLevels ell) m) (deg : ℕ → ℕ)
    (st : Strategy F Root) (hmell : m ≤ ell)
    (radius : ℕ → ℝ) (foldRadius : Fin m → ℝ)
    (qCount : ℕ) {tau : ℝ} {b : ℕ}
    (htau : tau ≤ 1) (hfinal : 0 ≤ radius m)
    (hgap : ∀ j : Fin m, radius (j + 1) + tau ≤ foldRadius j)
    (hfold : ∀ j : Fin m,
      FoldDistanceTransition (T.data j j.isLt) (deg j) (deg (j + 1))
        (radius j) (foldRadius j) b)
    (hfar0 : ¬ close (radius 0) (reedSolomonCode (T.dom 0) (deg 0))
      (OpeningResolution.word (S 0) 0 (st 0 (fun i => i.elim0)))) :
    uniformProb ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => CoherentAccepts S T deg st hmell qCount x.1 x.2) ≤
      (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ) + (1 - tau) ^ qCount +
        uniformProb (Fin m → F) (BadRoots S st) := by
  exact le_trans (coherent_probability_reduction S T deg st hmell qCount)
    (add_le_add (friAdaptive_coherent_sampled_sound
      (fun n => idealCommitment F (PowerTwoFriLevels ell n)) T deg
      (resolvedTranscript S st) hmell radius foldRadius qCount
      htau hfinal hgap hfold hfar0) le_rfl)

/-- Under exact position binding, arbitrary malicious roots carry the same
finite challenge/query bound as the existing committed-word consumer. -/
theorem coherent_sound_binding
    (S : ∀ n, OpeningScheme (Root n) F (PowerTwoFriLevels ell n) (Op n))
    (hb : ∀ n, (S n).PositionBinding)
    (T : FoldingTower F (PowerTwoFriLevels ell) m) (deg : ℕ → ℕ)
    (st : Strategy F Root) (hmell : m ≤ ell)
    (radius : ℕ → ℝ) (foldRadius : Fin m → ℝ)
    (qCount : ℕ) {tau : ℝ} {b : ℕ}
    (htau : tau ≤ 1) (hfinal : 0 ≤ radius m)
    (hgap : ∀ j : Fin m, radius (j + 1) + tau ≤ foldRadius j)
    (hfold : ∀ j : Fin m,
      FoldDistanceTransition (T.data j j.isLt) (deg j) (deg (j + 1))
        (radius j) (foldRadius j) b)
    (hfar0 : ¬ close (radius 0) (reedSolomonCode (T.dom 0) (deg 0))
      (OpeningResolution.word (S 0) 0 (st 0 (fun i => i.elim0)))) :
    uniformProb ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => CoherentAccepts S T deg st hmell qCount x.1 x.2) ≤
      (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ) + (1 - tau) ^ qCount := by
  have hbad : uniformProb (Fin m → F) (BadRoots S st) = 0 :=
    uniformProb_false (no_bad_of_binding S hb st)
  simpa only [hbad, add_zero] using coherent_sound S T deg st hmell
    radius foldRadius qCount htau hfinal hgap hfold hfar0

end FriRootResolution
end Minidregg.Selvage

/-! ## Exact theorem dependency reports -/
/-- info: 'Minidregg.Selvage.FriRootResolution.coherent_probability_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.coherent_probability_reduction
/-- info: 'Minidregg.Selvage.FriRootResolution.coherent_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.coherent_sound
/-- info: 'Minidregg.Selvage.FriRootResolution.coherent_sound_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.coherent_sound_binding
