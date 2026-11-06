/-
Computational binding adapters for the existing commitment and audit interfaces.
The conditional adapter is deliberately stronger than a one-shot CR assumption.
The global adapter pays a finite-horizon damage term, without conditioning the
comparison process on a future good event. See BindingGame for checked algebra.
-/
import Selvage.BindingGame
import Selvage.CollisionResistanceROM
import Selvage.AuditSampling

namespace Minidregg.Selvage

set_option autoImplicit false

namespace ComputationalBinding

variable {Ω Code Root F ι Op : Type} [Fintype Ω] [Nonempty Ω]

/-- An adversary's concrete two-opening output, with all witness bytes retained. -/
structure Attempt (Root F ι Op : Type) where
  root : Root
  index : ι
  left : F
  right : F
  leftOpening : Op
  rightOpening : Op

def Attempt.Wins (S : OpeningScheme Root F ι Op) (a : Attempt Root F ι Op) : Prop :=
  S.verifyOpen a.root a.index a.left a.leftOpening ∧
  S.verifyOpen a.root a.index a.right a.rightOpening ∧ a.left ≠ a.right

/-- Exact position binding is the zero-event idealization, not the definition
of computational security. In a compressing scheme this universal property can
fail while resource-limited attempts have small success probability. -/
theorem perfect_iff_no_attempt (S : OpeningScheme Root F ι Op) :
    S.PositionBinding ↔ ∀ a : Attempt Root F ι Op, ¬ a.Wins S := by
  constructor
  · intro hb a h
    exact h.2.2 (hb a.root a.index a.left a.right a.leftOpening a.rightOpening h.1 h.2.1)
  · intro hb rt i v v' o o' h h'
    by_contra hne
    exact hb ⟨rt, i, v, v', o, o'⟩ ⟨h, h', hne⟩

/-- Concrete flat-opening reduction: the output pair is the two supplied words,
not an unbounded search for a collision of the fixed hash. -/
theorem flat_attempt_collision {N : ℕ} (H : (ι → F) → Fin N)
    (a : Attempt (Fin N) F ι (ι → F)) (h : a.Wins (roScheme F ι H)) :
    a.leftOpening ≠ a.rightOpening ∧ H a.leftOpening = H a.rightOpening := by
  refine ⟨?_, h.1.1.trans h.2.1.1.symm⟩
  intro heq
  exact h.2.2 (h.1.2.symm.trans ((congrFun heq a.index).trans h.2.1.2))

/-- Same global experiment, actual transformed code, two output hash queries
included. `extraSteps` must cover the concrete output encoding/comparison cost. -/
theorem flat_binding_advantage {N : ℕ} (H : Ω → (ι → F) → Fin N)
    (G : BindingGame.Experiment Ω Code (Attempt (Fin N) F ι (ι → F)))
    (a : Code) (q t extraSteps : ℕ) (ε : ℝ)
    (hbudget : G.Within a q t)
    (hCR : (G.map (fun x => (x.leftOpening, x.rightOpening)) 2 extraSteps).SecureAt
      (fun ω pair => pair.1 ≠ pair.2 ∧ H ω pair.1 = H ω pair.2)
      (q + 2) (t + extraSteps) ε) :
    G.advantage (fun ω out => out.Wins (roScheme F ι (H ω))) a ≤ ε := by
  apply BindingGame.advantage_reduction G
    (G.map (fun x => (x.leftOpening, x.rightOpening)) 2 extraSteps)
    (fun ω out => out.Wins (roScheme F ι (H ω)))
    (fun ω pair => pair.1 ≠ pair.2 ∧ H ω pair.1 = H ω pair.2)
    id a (q + 2) (t + extraSteps) ε hCR
  · exact G.within_map _ 2 extraSteps a q t hbudget
  · intro ω h
    exact flat_attempt_collision (H ω) (G.run a ω) h

/-- The common finite probability vocabulary agrees with AuditSampling's. -/
theorem prob_eq_uniformProb (p : Ω → Prop) :
    BindingGame.prob p = uniformProb Ω p := by
  classical
  exact (uniformProb_eq_avg_indicator p).symm

/-- A separate admissible bounded adversary for EVERY history is required.
A global success bound alone does not prove this premise: conditioning on an
already discovered collision can make the next-round success probability one. -/
theorem bindLeg_of_history_game {Result : Type}
    (G : BindingGame.Experiment Ω Code Result) (bad : Ω → Result → Prop)
    (R : Round Ω) (A : AuditParams) (q t : ℕ) (code : List Ω → Code)
    (hsecure : G.SecureAt bad q t A.εbind)
    (hbudget : ∀ h, G.Within (code h) q t)
    (hcover : ∀ h ω, R.bindBreak h ω = true → bad ω (G.run (code h) ω)) :
    Round.BindLeg A R := by
  intro h
  rw [← prob_eq_uniformProb]
  exact le_trans (BindingGame.prob_mono (hcover h)) (hsecure (code h) (hbudget h))

/-- The adapter feeds the EXISTING detection theorem; it does not restate the
whole conclusion as an assumption. Checker, beacon and semantic miss-decomposition
remain independently required. No cryptographic term is silently set to zero. -/
theorem sequential_of_history_game {Result : Type}
    (G : BindingGame.Experiment Ω Code Result) (bad : Ω → Result → Prop)
    (R : Round Ω) (A : AuditParams) (q t : ℕ) (code : List Ω → Code)
    (hsecure : G.SecureAt bad q t A.εbind)
    (hbudget : ∀ h, G.Within (code h) q t)
    (hcover : ∀ h ω, R.bindBreak h ω = true → bad ω (G.run (code h) ω))
    (hbeacon : Round.BeaconLeg A R) (hcheck : Round.ChkLeg A R)
    (hmiss : Round.MissDecomp R) (hq : 0 < A.q) (n : ℕ) :
    expOver Ω n (fun h => (R.count h : ℝ)) [] ≤ 1 / A.q :=
  Round.sequential_bound_of_legs
    ⟨hbeacon, hcheck, bindLeg_of_history_game G bad R A q t code hsecure hbudget hcover, hmiss⟩ hq n

/-- Finite history expectation is linear; stated here to avoid changing the
existing AuditSampling file during another lane's flag day. -/
theorem expOver_add (f g : List Ω → ℝ) (n : ℕ) (h : List Ω) :
    expOver Ω n (fun x => f x + g x) h = expOver Ω n f h + expOver Ω n g h := by
  have hneg : expOver Ω n (fun x => -g x) h = -expOver Ω n g h := by
    simpa using expOver.smul (-1) g n h
  have hs := expOver.sub f (fun x => -g x) n h
  simpa [hneg] using hs

/-- Monotonicity needs only the histories actually reached at this horizon. -/
theorem expOver_mono_final (f g : List Ω → ℝ) (n : ℕ) (h : List Ω)
    (hfg : ∀ k, k.length = h.length + n → f k ≤ g k) :
    expOver Ω n f h ≤ expOver Ω n g h := by
  induction n generalizing h with
  | zero => exact hfg h (by simp)
  | succ n ih =>
    rw [expOver.succ, expOver.succ]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro ω _
    apply ih (ω :: h)
    intro k hk
    apply hfg k
    simpa [List.length_cons, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hk

/-- A finite, genuinely sampled run coin space, one independent coordinate per
round. It avoids an implicit probability distribution over arbitrary lists. -/
def RunCoins (Ω : Type) : ℕ → Type
  | 0 => Unit
  | n + 1 => Ω × RunCoins Ω n

instance runCoinsFintype (n : ℕ) : Fintype (RunCoins Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype Unit)
  | succ n ih => exact inferInstanceAs (Fintype (Ω × RunCoins Ω n))

instance runCoinsNonempty (n : ℕ) : Nonempty (RunCoins Ω n) := by
  induction n with
  | zero => exact inferInstanceAs (Nonempty Unit)
  | succ n ih => exact inferInstanceAs (Nonempty (Ω × RunCoins Ω n))

def runHistory : (n : ℕ) → RunCoins Ω n → List Ω → List Ω
  | 0, _, h => h
  | n + 1, coins, h => runHistory n coins.2 (coins.1 :: h)

omit [Fintype Ω] [Nonempty Ω] in
theorem runHistory_length (n : ℕ) (coins : RunCoins Ω n) (h : List Ω) :
    (runHistory n coins h).length = h.length + n := by
  induction n generalizing h with
  | zero => simp [runHistory]
  | succ n ih => simpa [runHistory, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      (ih coins.2 (coins.1 :: h))

/-- Exact transport from the finite resource game to the existing recursive
expectation operator, including its most-recent-first history convention. -/
theorem mean_runHistory (n : ℕ) (f : List Ω → ℝ) (h : List Ω) :
    BindingGame.mean (fun coins : RunCoins Ω n => f (runHistory n coins h)) =
      expOver Ω n f h := by
  classical
  induction n generalizing h with
  | zero =>
    change BindingGame.mean (fun _ : RunCoins Ω 0 => f h) = f h
    exact BindingGame.mean_const (f h)
  | succ n ih =>
    change (∑ coins : Ω × RunCoins Ω n, f (runHistory n coins.2 (coins.1 :: h))) /
        (Fintype.card (Ω × RunCoins Ω n) : ℝ) = _
    rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, expOver.succ]
    simp only [← ih]
    unfold BindingGame.mean
    rw [← Finset.sum_div, div_div]
    congr 1
    ring

theorem prob_runHistory (n : ℕ) (bad : List Ω → Prop)
    [DecidablePred bad] :
    BindingGame.prob (fun coins : RunCoins Ω n => bad (runHistory n coins [])) =
      expOver Ω n (fun h => if bad h then 1 else 0) [] := by
  classical
  rw [BindingGame.prob_eq_mean]
  exact mean_runHistory n (fun h => if bad h then 1 else 0) []

/-- Global finite-horizon error transfer in AuditSampling's actual expectation
operator. `bad` refers to the whole transcript; hbad is a global game bound.
The comparison X must be coupled pathwise, not obtained by conditioning on ¬bad.
For a run of n rounds with per-step damage b, M = n*b is a typical cap. -/
theorem expOver_bad_transfer (X Y : List Ω → ℝ)
    (bad : List Ω → Prop) [DecidablePred bad] (n : ℕ) (M B ε : ℝ)
    (hM : 0 ≤ M) (hX : ∀ h, h.length = n → 0 ≤ X h)
    (hgood : ∀ h, h.length = n → ¬ bad h → Y h ≤ X h)
    (hcap : ∀ h, h.length = n → bad h → Y h ≤ M)
    (hmean : expOver Ω n X [] ≤ B)
    (hbad : expOver Ω n (fun h => if bad h then 1 else 0) [] ≤ ε) :
    expOver Ω n Y [] ≤ B + M * ε := by
  have hp : ∀ h, h.length = n → Y h ≤ X h + M * (if bad h then 1 else 0) := by
    intro h hlen
    by_cases hb : bad h
    · simp only [ite_eq_left hb, mul_one]
      linarith [hcap h hlen hb, hX h hlen]
    · simpa [hb] using hgood h hlen hb
  have hs := expOver_mono_final Y
    (fun h => X h + M * (if bad h then 1 else 0)) n [] (by simpa using hp)
  rw [expOver_add, expOver.smul] at hs
  exact le_trans hs (add_le_add hmean (mul_le_mul_of_nonneg_left hbad hM))

/-- Concrete hookup of the global game route to the existing leakage theorem.
The comparison process has its own valid detection guarantee on the original
coin space. The real process is dominated off bad and capped everywhere on bad.
No per-history εbind hypothesis is claimed for the real process. -/
theorem leakage_with_global_binding
    (comparison : Round Ω) (Y : List Ω → ℝ) (bad : List Ω → Prop)
    [DecidablePred bad] (n : ℕ) (b q M ε : ℝ) (hq : 0 < q) (hb : 0 ≤ b)
    (hdet : ∀ h : List Ω, comparison.stopped h = false → comparison.corrupt h = true →
      q ≤ uniformProb Ω (fun ω => comparison.alarms h ω))
    (hM : 0 ≤ M)
    (hgood : ∀ h, h.length = n → ¬ bad h → Y h ≤ b * (comparison.count h : ℝ))
    (hcap : ∀ h, h.length = n → bad h → Y h ≤ M)
    (hbad : expOver Ω n (fun h => if bad h then 1 else 0) [] ≤ ε) :
    expOver Ω n Y [] ≤ b / q + M * ε :=
  expOver_bad_transfer (fun h => b * (comparison.count h : ℝ)) Y bad n M (b / q) ε
    hM (fun _ _ => mul_nonneg hb (Nat.cast_nonneg _)) hgood hcap
    (Round.leakage_bound hq hb hdet n) hbad

/-- A resource-indexed GLOBAL computational game instantiates the whole-run bad
probability. This is the ordinary computational-security route; unlike the
history adapter it does not require an adversary for every conditioned history. -/
theorem leakage_of_global_game {Result : Type}
    (comparison : Round Ω) (Y : List Ω → ℝ) (bad : List Ω → Prop)
    [DecidablePred bad] (n : ℕ) (b q M ε : ℝ) (hq : 0 < q) (hb : 0 ≤ b)
    (hdet : ∀ h : List Ω, comparison.stopped h = false → comparison.corrupt h = true →
      q ≤ uniformProb Ω (fun ω => comparison.alarms h ω))
    (hM : 0 ≤ M)
    (hgood : ∀ h, h.length = n → ¬ bad h → Y h ≤ b * (comparison.count h : ℝ))
    (hcap : ∀ h, h.length = n → bad h → Y h ≤ M)
    (G : BindingGame.Experiment (RunCoins Ω n) Code Result)
    (gameBad : RunCoins Ω n → Result → Prop) (a : Code) (queries steps : ℕ)
    (hsecure : G.SecureAt gameBad queries steps ε) (hbudget : G.Within a queries steps)
    (hcover : ∀ coins, bad (runHistory n coins []) → gameBad coins (G.run a coins)) :
    expOver Ω n Y [] ≤ b / q + M * ε := by
  apply leakage_with_global_binding comparison Y bad n b q M ε hq hb hdet hM hgood hcap
  rw [← prob_runHistory]
  exact le_trans (BindingGame.prob_mono hcover) (hsecure a hbudget)

end ComputationalBinding
end Minidregg.Selvage

/-! Axiom audit: exact declarations, no unpinned theorem exports. -/
/-- info: 'Minidregg.Selvage.ComputationalBinding.perfect_iff_no_attempt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.ComputationalBinding.perfect_iff_no_attempt
/-- info: 'Minidregg.Selvage.ComputationalBinding.flat_attempt_collision' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.ComputationalBinding.flat_attempt_collision
/-- info: 'Minidregg.Selvage.ComputationalBinding.flat_binding_advantage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.ComputationalBinding.flat_binding_advantage
/-- info: 'Minidregg.Selvage.ComputationalBinding.prob_eq_uniformProb' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.ComputationalBinding.prob_eq_uniformProb
/-- info: 'Minidregg.Selvage.ComputationalBinding.bindLeg_of_history_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.ComputationalBinding.bindLeg_of_history_game
/-- info: 'Minidregg.Selvage.ComputationalBinding.sequential_of_history_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.ComputationalBinding.sequential_of_history_game
/-- info: 'Minidregg.Selvage.ComputationalBinding.expOver_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.ComputationalBinding.expOver_add
/-- info: 'Minidregg.Selvage.ComputationalBinding.expOver_mono_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.ComputationalBinding.expOver_mono_final
/-- info: 'Minidregg.Selvage.ComputationalBinding.runHistory_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.ComputationalBinding.runHistory_length
/-- info: 'Minidregg.Selvage.ComputationalBinding.mean_runHistory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.ComputationalBinding.mean_runHistory
/-- info: 'Minidregg.Selvage.ComputationalBinding.prob_runHistory' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.ComputationalBinding.prob_runHistory
/-- info: 'Minidregg.Selvage.ComputationalBinding.expOver_bad_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.ComputationalBinding.expOver_bad_transfer
/-- info: 'Minidregg.Selvage.ComputationalBinding.leakage_with_global_binding' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.ComputationalBinding.leakage_with_global_binding
/-- info: 'Minidregg.Selvage.ComputationalBinding.leakage_of_global_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.ComputationalBinding.leakage_of_global_game
