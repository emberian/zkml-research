/-
# Prefix-selected malicious roots reduce to the existing adaptive FRI consumer

Root strategies choose level n using exactly the first n challenges, before
queries. No honest root preimage or committed word is supplied. Canonical
opening resolution produces an existing ideal `FriAdaptiveTranscript`.
Accepted raw queries imply ideal acceptance or an explicit two-opening event.
Transparent terminal roots represent a revealed final evaluation word.

This is a finite semantic reduction. The classical resolver is not claimed to
be efficient; the double-opening event has no asserted cryptographic price.
-/
import Selvage.OpeningResolution
import Selvage.HalfThresholdFriCoherent

namespace Minidregg.Selvage
namespace FriRootResolution

open OpeningResolution

variable {F : Type*} [Field F]
variable {ι Root Op : ℕ → Type*} {m : ℕ}

/-- Level-n roots depend on exactly n past challenges, with no query seed. -/
abbrev Strategy (F : Type*) (Root : ℕ → Type*) :=
  ∀ n, (Fin n → F) → Root n

/-- Select one strategy root from a full challenge tuple. -/
def rootAt (st : Strategy F Root) (r : Fin m → F) (n : ℕ) (hn : n ≤ m) : Root n :=
  st n (friPrefix r n hn)

/-- No image premise: resolve each prefix-selected root and commit its word
under the existing ideal identity scheme. Original roots remain in the raw event. -/
noncomputable def resolvedTranscript
    (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n)) (st : Strategy F Root) :
    FriAdaptiveTranscript (fun n => idealCommitment F (ι n)) where
  word n p := word (S n) 0 (st n p)
  root n p := word (S n) 0 (st n p)
  root_eq_commit _ _ := rfl

/-- A binding failure is retained at a root actually selected by this
challenge execution. It may use two alternative accepted opening paths. -/
def BadRoots (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n))
    (st : Strategy F Root) (r : Fin m → F) : Prop :=
  ∃ n, ∃ hn : n ≤ m, DoubleOpening (S n) (rootAt st r n hn)

/-- The terminal word is in the existing Reed--Solomon code and is fully
attributed to the final root. For a transparent final root, equality supplies
these openings; no final Merkle commitment is needed. -/
def TerminalAccepts (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n))
    (st : Strategy F Root) (r : Fin m → F) (dom : ι m ↪ F) (d : ℕ) : Prop :=
  ∃ w, w ∈ reedSolomonCode dom d ∧
    ∀ i, ∃ o, (S m).verifyOpen (rootAt st r m le_rfl) i (w i) o

/-- Existing opened-query verification, with raw prefix-selected roots. -/
def RoundAccepts (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (st : Strategy F Root) (r : Fin m → F)
    (j : Fin m) {qCount : ℕ} (q : Fin qCount → ι (j + 1)) : Prop :=
  FriRoundQueriesAccept (S j) (S (j + 1)) (T.data j j.isLt)
    (rootAt st r j (Nat.le_of_lt j.isLt))
    (rootAt st r (j + 1) (Nat.succ_le_iff.mpr j.isLt)) (r j) q

/-- Raw sampled acceptance keeps opening witnesses and terminal attribution. -/
def SampledAccepts (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (deg : ℕ → ℕ) (st : Strategy F Root)
    (qCount : ℕ) (r : Fin m → F) (Q : FriIndependentQuerySchedule ι m qCount) : Prop :=
  (∀ j, RoundAccepts S T st r j (Q j)) ∧ TerminalAccepts S st r (T.dom m) (deg m)

/-- Statement-first: raw acceptance reduces to the existing adaptive
consumer or a retained binding failure, with no committed-word premise. -/
def SoundReduction (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (deg : ℕ → ℕ) (st : Strategy F Root) : Prop :=
  ∀ qCount r Q, SampledAccepts S T deg st qCount r Q →
    FriAdaptiveSampledAccepts (fun n => idealCommitment F (ι n)) T deg
      (resolvedTranscript S st) qCount r Q ∨ BadRoots S st r

/-- Canonical words obey the existing prefix-measurability theorem. No
future challenge or query index is used in their construction. -/
theorem resolved_word_prefix (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n))
    (st : Strategy F Root) {r r' : Fin m → F} {n : ℕ} {hn hn' : n ≤ m}
    (h : ∀ j : Fin m, (j : ℕ) < n → r j = r' j) :
    (resolvedTranscript S st).wordAt r n hn =
      (resolvedTranscript S st).wordAt r' n hn' :=
  FriAdaptiveTranscript.wordAt_congr _ h

/-- Terminal attribution fixes the final resolved word whenever that root
has no double opening. -/
theorem terminal_resolves (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n))
    (st : Strategy F Root) (r : Fin m → F) (dom : ι m ↪ F) (d : ℕ)
    (hfree : ¬ BadRoots S st r) (hterm : TerminalAccepts S st r dom d) :
    (resolvedTranscript S st).wordAt r m le_rfl ∈ reedSolomonCode dom d := by
  obtain ⟨w, hw, hopen⟩ := hterm
  have heq : (resolvedTranscript S st).wordAt r m le_rfl = w := by
    funext i
    obtain ⟨o, ho⟩ := hopen i
    exact (eq_word_of_no_double (S m) 0
      (fun h => hfree ⟨m, le_rfl, h⟩) ho).symm
  rw [heq]
  exact hw

/-- Each accepted raw fibre gives an accepted existing ideal fibre unless
one of its roots admits two accepted values at the same position. -/
theorem round_resolves (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (st : Strategy F Root) (r : Fin m → F)
    (j : Fin m) {qCount : ℕ} (q : Fin qCount → ι (j + 1))
    (hfree : ¬ BadRoots S st r) (hopen : RoundAccepts S T st r j q) :
    FriAdaptiveRoundQueriesAccept (fun n => idealCommitment F (ι n)) T
      (resolvedTranscript S st) r j q := by
  obtain ⟨o, ho⟩ := hopen
  let resolvedOpening (a : Fin qCount) : FriQueryOpening F Unit Unit := {
    left := (o a).left
    right := (o a).right
    next := (o a).next
    leftPath := ()
    rightPath := ()
    nextPath := () }
  refine ⟨resolvedOpening, fun a => ?_⟩
  obtain ⟨hl, hr, hn, heq⟩ := ho a
  have hbig : ¬ DoubleOpening (S j) (rootAt st r j (Nat.le_of_lt j.isLt)) :=
    fun h => hfree ⟨j, Nat.le_of_lt j.isLt, h⟩
  have hsmall : ¬ DoubleOpening (S (j + 1))
      (rootAt st r (j + 1) (Nat.succ_le_iff.mpr j.isLt)) :=
    fun h => hfree ⟨j + 1, Nat.succ_le_iff.mpr j.isLt, h⟩
  exact ⟨(eq_word_of_no_double (S j) 0 hbig hl).symm,
    (eq_word_of_no_double (S j) 0 hbig hr).symm,
    (eq_word_of_no_double (S (j + 1)) 0 hsmall hn).symm, heq⟩

/-- The raw-to-ideal adaptive reduction consumes the existing verifier. -/
theorem sound_reduction (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (deg : ℕ → ℕ) (st : Strategy F Root) :
    SoundReduction S T deg st := by
  intro qCount r Q hraw
  by_cases hbad : BadRoots S st r
  · exact Or.inr hbad
  · exact Or.inl ⟨fun j => round_resolves S T st r j (Q j) hbad (hraw.1 j),
      terminal_resolves S st r (T.dom m) (deg m) hbad hraw.2⟩

omit [Field F] in
/-- Perfect binding removes the bad-root branch without requiring roots
in the honest image. -/
theorem no_bad_of_binding (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n))
    (hb : ∀ n, (S n).PositionBinding) (st : Strategy F Root) (r : Fin m → F) :
    ¬ BadRoots S st r := by
  rintro ⟨n, hn, h⟩
  exact no_double_of_binding (S n) (hb n) _ h

/-! ## Transparent terminal specialization -/

/-- A transparent terminal word satisfies attribution exactly when it passes
its Reed--Solomon check. Only the equality of the revealed word is consumed. -/
theorem transparent_terminal (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n))
    (st : Strategy F (fun n => Root n ⊕ (ι n → F))) (r : Fin m → F)
    (dom : ι m ↪ F) (d : ℕ) (w : ι m → F)
    (hrt : rootAt st r m le_rfl = Sum.inr w) :
    TerminalAccepts (fun n => transparent (S n)) st r dom d ↔
      w ∈ reedSolomonCode dom d := by
  constructor
  · rintro ⟨v, hv, hopen⟩
    have heq : w = v := by
      funext i
      obtain ⟨o, ho⟩ := hopen i
      simpa [hrt, transparent] using ho
    rwa [heq]
  · intro hw
    exact ⟨w, hw, fun i => ⟨none, by simp [hrt, transparent]⟩⟩

end FriRootResolution
end Minidregg.Selvage

/-! ## Exact theorem dependency reports -/
/-- info: 'Minidregg.Selvage.FriRootResolution.resolved_word_prefix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.resolved_word_prefix
/-- info: 'Minidregg.Selvage.FriRootResolution.terminal_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.terminal_resolves
/-- info: 'Minidregg.Selvage.FriRootResolution.round_resolves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.round_resolves
/-- info: 'Minidregg.Selvage.FriRootResolution.sound_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.sound_reduction
/-- info: 'Minidregg.Selvage.FriRootResolution.no_bad_of_binding' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.no_bad_of_binding
/-- info: 'Minidregg.Selvage.FriRootResolution.transparent_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.FriRootResolution.transparent_terminal
