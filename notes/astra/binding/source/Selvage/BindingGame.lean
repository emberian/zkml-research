/-
Finite computational-security games and common-experiment error composition.
The code type and its resource semantics are fixed BEFORE security is assumed;
resource counters are not numbers supplied by the adversary. A concrete machine/
oracle interpreter must justify that these semantics model the deployment.
No random-oracle or concrete hash bound is asserted by this module.
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FinCases

namespace Minidregg.Selvage.BindingGame

set_option autoImplicit false
open Finset

variable {Ω Code Result Subject Digest : Type} [Fintype Ω]

noncomputable def prob (p : Ω → Prop) : ℝ := by
  classical
  exact (∑ ω : Ω, if p ω then (1 : ℝ) else 0) / Fintype.card Ω

noncomputable def mean (f : Ω → ℝ) : ℝ :=
  (∑ ω : Ω, f ω) / Fintype.card Ω

theorem mean_const [Nonempty Ω] (a : ℝ) : mean (fun _ : Ω => a) = a := by
  unfold mean
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ a (by exact_mod_cast Fintype.card_ne_zero)

theorem prob_eq_mean (p : Ω → Prop) [DecidablePred p] :
    prob p = mean (fun ω => if p ω then 1 else 0) := by
  unfold prob mean
  congr 1
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : p ω <;> simp [h]

theorem prob_mono {p q : Ω → Prop} (h : ∀ ω, p ω → q ω) : prob p ≤ prob q := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : p ω <;> by_cases hq : q ω <;> simp_all

theorem prob_or (p q : Ω → Prop) : prob (fun ω => p ω ∨ q ω) ≤ prob p + prob q := by
  classical
  unfold prob
  rw [← add_div, ← Finset.sum_add_distrib]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply Finset.sum_le_sum
  intro ω _
  by_cases hp : p ω <;> by_cases hq : q ω <;> simp [hp, hq]

theorem prob_le_one (p : Ω → Prop) : prob p ≤ 1 := by
  classical
  have hs : (∑ ω : Ω, if p ω then (1 : ℝ) else 0) ≤ Fintype.card Ω := by
    calc _ ≤ ∑ _ω : Ω, (1 : ℝ) := Finset.sum_le_sum (fun ω _ => by split_ifs <;> norm_num)
         _ = _ := by simp
  by_cases h : Fintype.card Ω = 0
  · simp [prob, h]
  · unfold prob
    exact (div_le_one (by exact_mod_cast Nat.pos_of_ne_zero h)).2 hs

/-- Normalization is required at every security API; empty spaces are only
allowed for the algebraic zero-measure lemmas above. -/
theorem prob_true [Nonempty Ω] : prob (fun _ : Ω => True) = 1 := by
  classical
  simp [prob, ne_of_gt (Fintype.card_pos : 0 < Fintype.card Ω)]

/-- The resource model belongs to the experiment, not to its submitted code. -/
structure Experiment (Ω Code Result : Type) where
  run : Code → Ω → Result
  queries : Code → Ω → ℕ
  steps : Code → Ω → ℕ

/-- Worst-case resources, including extraction, verification and output queries
when those operations belong to the reduction. -/
def Experiment.Within (G : Experiment Ω Code Result) (a : Code) (q t : ℕ) : Prop :=
  ∀ ω, G.queries a ω ≤ q ∧ G.steps a ω ≤ t

noncomputable def Experiment.advantage (G : Experiment Ω Code Result)
    (bad : Ω → Result → Prop) (a : Code) : ℝ := prob (fun ω => bad ω (G.run a ω))

/-- Explicit security assumption at one resource budget, on THIS experiment.
A security parameter or public setup can index a family of these games.
A bound for a smaller adversary class is not a bound for a larger one. -/
def Experiment.SecureAt [Nonempty Ω] (G : Experiment Ω Code Result) (bad : Ω → Result → Prop)
    (q t : ℕ) (ε : ℝ) : Prop :=
  ∀ a, G.Within a q t → G.advantage bad a ≤ ε

/-- Output transformation with explicit worst-case reduction overhead. The
chosen time bound includes scanning/encoding the outputs; zero is not implicit. -/
def Experiment.map (G : Experiment Ω Code Result) {Result' : Type}
    (f : Result → Result') (extraQueries extraSteps : ℕ) : Experiment Ω Code Result' where
  run a ω := f (G.run a ω)
  queries a ω := G.queries a ω + extraQueries
  steps a ω := G.steps a ω + extraSteps

omit [Fintype Ω] in
theorem Experiment.within_map (G : Experiment Ω Code Result) {Result' : Type}
    (f : Result → Result') (extraQueries extraSteps : ℕ) (a : Code) (q t : ℕ)
    (h : G.Within a q t) :
    (G.map f extraQueries extraSteps).Within a (q + extraQueries) (t + extraSteps) := by
  intro ω
  exact ⟨Nat.add_le_add_right (h ω).1 _, Nat.add_le_add_right (h ω).2 _⟩

/-- A reduction produces a named output pair in the fixed code model.
Computability and interpreter adequacy require a concrete instantiation. Its resource bounds
must be proved for the transformed code, not inherited from the original code. -/
theorem advantage_reduction [Nonempty Ω] {Code' Result' : Type}
    (G : Experiment Ω Code Result) (H : Experiment Ω Code' Result')
    (bad : Ω → Result → Prop) (wins : Ω → Result' → Prop)
    (reduce : Code → Code') (a : Code) (q t : ℕ) (ε : ℝ)
    (hsecure : H.SecureAt wins q t ε)
    (hresource : H.Within (reduce a) q t)
    (hcover : ∀ ω, bad ω (G.run a ω) → wins ω (H.run (reduce a) ω)) :
    G.advantage bad a ≤ ε :=
  le_trans (prob_mono hcover) (hsecure (reduce a) hresource)

/-- Whole-subject binding includes length: instantiate Subject := List Byte,
not a fixed-length projection which loses the empty/prefix distinction. -/
def SameRootDifferentSubject (commit : Subject → Digest) (s : Subject × Subject) : Prop :=
  commit s.1 = commit s.2 ∧ s.1 ≠ s.2

/-- In the flat hash scheme the reduction is the actual two extracted inputs;
there is no existential assertion that some collision somewhere exists. -/
theorem flat_collision_reduction (H : Subject → Digest) (s : Subject × Subject) :
    SameRootDifferentSubject H s → s.1 ≠ s.2 ∧ H s.1 = H s.2 :=
  fun h => ⟨h.2, h.1⟩

/-- Common-experiment conjunction, relative to the FIRST extracted subject.
Each verifier binds its own subject to the advertised root; their disagreement
is the third bad event. No independence assumption. All extraction overhead
belongs in the budget used to establish hb. -/
theorem cert_and [Nonempty Ω] (commit : Ω → Subject → Digest) (root : Ω → Digest)
    (w₁ w₂ : Ω → Subject) (V₁ V₂ : Ω → Prop) (P₁ P₂ : Subject → Prop)
    (ε₁ ε₂ εb : ℝ)
    (h₁ : prob (fun ω => V₁ ω ∧ ¬ (commit ω (w₁ ω) = root ω ∧ P₁ (w₁ ω))) ≤ ε₁)
    (h₂ : prob (fun ω => V₂ ω ∧ ¬ (commit ω (w₂ ω) = root ω ∧ P₂ (w₂ ω))) ≤ ε₂)
    (hb : prob (fun ω => SameRootDifferentSubject (commit ω) (w₁ ω, w₂ ω)) ≤ εb) :
    prob (fun ω => V₁ ω ∧ V₂ ω ∧
      ¬ (commit ω (w₁ ω) = root ω ∧ P₁ (w₁ ω) ∧ P₂ (w₁ ω)))
      ≤ min 1 (ε₁ + ε₂ + εb) := by
  classical
  apply le_min (prob_le_one _)
  have hc : prob (fun ω => V₁ ω ∧ V₂ ω ∧
      ¬ (commit ω (w₁ ω) = root ω ∧ P₁ (w₁ ω) ∧ P₂ (w₁ ω))) ≤
      prob (fun ω => (V₁ ω ∧ ¬ (commit ω (w₁ ω) = root ω ∧ P₁ (w₁ ω))) ∨
        (V₂ ω ∧ ¬ (commit ω (w₂ ω) = root ω ∧ P₂ (w₂ ω))) ∨
        SameRootDifferentSubject (commit ω) (w₁ ω, w₂ ω)) := by
    apply prob_mono
    intro ω h
    by_cases hfirst : commit ω (w₁ ω) = root ω ∧ P₁ (w₁ ω)
    · by_cases hsecond : commit ω (w₂ ω) = root ω ∧ P₂ (w₂ ω)
      · right; right
        exact ⟨hfirst.1.trans hsecond.1.symm, fun heq => h.2.2
          ⟨hfirst.1, hfirst.2, (by simpa only [show w₁ ω = w₂ ω from heq] using hsecond.2)⟩⟩
      · exact Or.inr (Or.inl ⟨h.2.1, hsecond⟩)
    · exact Or.inl ⟨h.1, hfirst⟩
  have hu := prob_or
    (fun ω => V₁ ω ∧ ¬ (commit ω (w₁ ω) = root ω ∧ P₁ (w₁ ω)))
    (fun ω => (V₂ ω ∧ ¬ (commit ω (w₂ ω) = root ω ∧ P₂ (w₂ ω))) ∨
      SameRootDifferentSubject (commit ω) (w₁ ω, w₂ ω))
  have hv := prob_or
    (fun ω => V₂ ω ∧ ¬ (commit ω (w₂ ω) = root ω ∧ P₂ (w₂ ω)))
    (fun ω => SameRootDifferentSubject (commit ω) (w₁ ω, w₂ ω))
  linarith

/-- Computational conjunction with witnesses tied to the actual resource-
bounded extractor output. Bounds for merely existential witnesses do not suffice. -/
theorem cert_and_of_game [Nonempty Ω]
    (G : Experiment Ω Code (Subject × Subject)) (a : Code) (queries steps : ℕ)
    (commit : Ω → Subject → Digest) (root : Ω → Digest)
    (V₁ V₂ : Ω → Prop) (P₁ P₂ : Subject → Prop) (ε₁ ε₂ εb : ℝ)
    (h₁ : prob (fun ω => V₁ ω ∧ ¬ (commit ω (G.run a ω).1 = root ω ∧ P₁ (G.run a ω).1)) ≤ ε₁)
    (h₂ : prob (fun ω => V₂ ω ∧ ¬ (commit ω (G.run a ω).2 = root ω ∧ P₂ (G.run a ω).2)) ≤ ε₂)
    (hsecure : G.SecureAt (fun ω => SameRootDifferentSubject (commit ω)) queries steps εb)
    (hbudget : G.Within a queries steps) :
    prob (fun ω => V₁ ω ∧ V₂ ω ∧
      ¬ (commit ω (G.run a ω).1 = root ω ∧ P₁ (G.run a ω).1 ∧ P₂ (G.run a ω).1))
      ≤ min 1 (ε₁ + ε₂ + εb) :=
  cert_and commit root (fun ω => (G.run a ω).1) (fun ω => (G.run a ω).2)
    V₁ V₂ P₁ P₂ ε₁ ε₂ εb h₁ h₂ (hsecure a hbudget)

/-- Receipt composition permits a nontrivial subject projection. The binding
check establishes that projection agrees, outside its explicitly charged event.
This theorem does not equate occurrence with validity or sampling with safety. -/
theorem receipt_and [Nonempty Ω] (V₁ V₂ Bind P₁ P₂ BadBind : Ω → Prop) (ε₁ ε₂ εb : ℝ)
    (h₁ : prob (fun ω => V₁ ω ∧ ¬ P₁ ω) ≤ ε₁)
    (h₂ : prob (fun ω => V₂ ω ∧ ¬ P₂ ω) ≤ ε₂)
    (hb : prob BadBind ≤ εb)
    (Target : Ω → Prop)
    (hjoin : ∀ ω, Bind ω → ¬ BadBind ω → P₁ ω → P₂ ω → Target ω) :
    prob (fun ω => V₁ ω ∧ V₂ ω ∧ Bind ω ∧ ¬ Target ω)
      ≤ min 1 (ε₁ + ε₂ + εb) := by
  classical
  apply le_min (prob_le_one _)
  have hc : prob (fun ω => V₁ ω ∧ V₂ ω ∧ Bind ω ∧ ¬ Target ω) ≤
      prob (fun ω => (V₁ ω ∧ ¬ P₁ ω) ∨ (V₂ ω ∧ ¬ P₂ ω) ∨ BadBind ω) := by
    apply prob_mono
    intro ω h
    by_cases hp : P₁ ω
    · by_cases hq : P₂ ω
      · by_cases hb' : BadBind ω
        · exact Or.inr (Or.inr hb')
        · exact False.elim (h.2.2.2 (hjoin ω h.2.2.1 hb' hp hq))
      · exact Or.inr (Or.inl ⟨h.2.1, hq⟩)
    · exact Or.inl ⟨h.1, hp⟩
  have hu := prob_or (fun ω => V₁ ω ∧ ¬ P₁ ω)
    (fun ω => (V₂ ω ∧ ¬ P₂ ω) ∨ BadBind ω)
  have hv := prob_or (fun ω => V₂ ω ∧ ¬ P₂ ω) BadBind
  linarith

/-- Finite-horizon global-bad-event repair. X is a comparison process on the
SAME sample space, not the real process conditioned on a future good event.
Y ≤ X off bad, Y ≤ M on bad, and X ≥ 0 imply E[Y] ≤ E[X] + M Pr[bad]. -/
theorem mean_bad_transfer (X Y : Ω → ℝ) (bad : Ω → Prop) (M B ε : ℝ)
    (hM : 0 ≤ M) (hX : ∀ ω, 0 ≤ X ω)
    (hgood : ∀ ω, ¬ bad ω → Y ω ≤ X ω)
    (hcap : ∀ ω, bad ω → Y ω ≤ M)
    (hmean : mean X ≤ B) (hbad : prob bad ≤ ε) :
    mean Y ≤ B + M * ε := by
  classical
  have hp : ∀ ω, Y ω ≤ X ω + M * (if bad ω then 1 else 0) := by
    intro ω
    by_cases h : bad ω
    · simp only [ite_eq_left h, mul_one]
      linarith [hcap ω h, hX ω]
    · simpa [h] using hgood ω h
  have hs : mean Y ≤ mean X + M * prob bad := by
    unfold mean prob
    rw [← mul_div_assoc, ← add_div, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun ω _ => hp ω)) (Nat.cast_nonneg _)
  exact le_trans hs (add_le_add hmean (mul_le_mul_of_nonneg_left hbad hM))

/-! Keystones: accepted nontrivial instance, failure when binding is omitted,
and a rare-history countermodel to global-to-conditional security. -/

namespace Keystone

def constantHash (_ : Bool) : Unit := ()
def pairGame : Experiment Unit Unit (Bool × Bool) where
  run _ _ := (false, true)
  queries _ _ := 2
  steps _ _ := 1

theorem pairGame_inhabited : pairGame.Within () 2 1 := by
  intro ω; exact ⟨le_rfl, le_rfl⟩

theorem pairGame_advantage : pairGame.advantage
    (fun _ => SameRootDifferentSubject constantHash) () = 1 := by
  norm_num [Experiment.advantage, prob, pairGame, SameRootDifferentSubject, constantHash]

theorem zero_budget_refuted : ¬ pairGame.SecureAt
    (fun _ => SameRootDifferentSubject constantHash) 2 1 0 := by
  intro h
  have hh := h () pairGame_inhabited
  rw [pairGame_advantage] at hh
  norm_num at hh

theorem budget_inhabited : pairGame.SecureAt
    (fun _ => SameRootDifferentSubject constantHash) 2 1 1 := by
  intro a _; exact prob_le_one _

/-- Each certificate is true of its extracted subject, but there is no common
subject satisfying both predicates. Both leg errors are zero; binding costs one. -/
theorem conjunction_requires_binding :
    (false = false ∧ true = true) ∧ ¬ ∃ b : Bool, b = false ∧ b = true := by
  constructor
  · exact ⟨rfl, rfl⟩
  · rintro ⟨b, h₁, h₂⟩; cases h₁.symm.trans h₂

/-- The bad event is the rare prefix 0. Given that prefix, every current coin
is bad. The global probability is 1/2 here, while the conditional value is 1. -/
theorem global_not_history_conditional :
    prob (fun x : Bool × Bool => x.1 = false) = 1 / 2 ∧
    prob (fun _x : Bool => (false : Bool) = false) = 1 := by
  norm_num [prob, Fintype.sum_prod_type, Fintype.sum_bool]

/-- The same conditioning defect with a 1/128 global event. No zero-
probability history is involved. The frozen prefix 0 makes the event certain. -/
theorem rare_history_counterexample :
    prob (fun x : Fin 128 => x = 0) = 1 / 128 ∧
    prob (fun _x : Bool => (0 : Fin 128) = 0) = 1 := by
  classical
  have hsum : (∑ x : Fin 128, if x = 0 then (1 : ℝ) else 0) = 1 := by
    rw [Finset.sum_eq_single (0 : Fin 128)]
    · simp
    · intro x _ hx; simp [hx]
    · simp
  constructor
  · rw [prob_eq_mean]
    unfold mean
    rw [hsum]
    norm_num
  · norm_num [prob, Fintype.sum_bool]

theorem identity_secure_zero [Nonempty Ω] (G : Experiment Ω Code (Bool × Bool)) (q t : ℕ) :
    G.SecureAt (fun _ => SameRootDifferentSubject (fun b : Bool => b)) q t 0 := by
  classical
  intro a _
  have hfalse : ∀ ω, ¬ SameRootDifferentSubject (fun b : Bool => b) (G.run a ω) :=
    fun _ h => h.2 h.1
  simp [Experiment.advantage, prob, hfalse]

theorem global_transfer_tight :
    mean (fun b : Bool => if b = false then (1 : ℝ) else 0) = 1 / 2 := by
  norm_num [mean, Fintype.sum_bool]

/-- A sampled compressing family: three messages, two digests, two random bits.
This is only a pairwise-universal, nonadaptive two-query toy, NOT deployed CR. -/
def sampledHash (coins : Bool × Bool) (x : Fin 3) : Bool :=
  if x = 0 then coins.1 else if x = 1 then coins.2 else xor coins.1 coins.2

def sampledPairGame : Experiment (Bool × Bool) (Fin 3 × Fin 3) (Fin 3 × Fin 3) where
  run a _ := a
  queries _ _ := 2
  steps _ _ := 1

theorem sampled_budget_inhabited : sampledPairGame.Within (0, 1) 2 1 := by
  intro ω; exact ⟨le_rfl, le_rfl⟩

theorem sampled_compressing_secure : sampledPairGame.SecureAt
    (fun ω => SameRootDifferentSubject (sampledHash ω)) 2 1 (1 / 2) := by
  intro a _
  rcases a with ⟨x, y⟩
  unfold Experiment.advantage prob
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  fin_cases x <;> fin_cases y <;>
    norm_num [sampledPairGame, SameRootDifferentSubject, sampledHash, Fintype.sum_bool]

/-- Composition fires on the compressing toy: leg one proves message 0,
leg two proves message 1, and both accept one root exactly on a collision. -/
theorem certificate_game_fires :
    prob (fun ω : Bool × Bool => sampledHash ω 1 = sampledHash ω 0) ≤ 1 / 2 := by
  have h₁ : prob (fun ω : Bool × Bool => True ∧
      ¬ (sampledHash ω (sampledPairGame.run (0, 1) ω).1 = sampledHash ω 0 ∧
        (sampledPairGame.run (0, 1) ω).1 = 0)) ≤ 0 := by
    simp [sampledPairGame, prob]
  have h₂ : prob (fun ω : Bool × Bool => sampledHash ω 1 = sampledHash ω 0 ∧
      ¬ (sampledHash ω (sampledPairGame.run (0, 1) ω).2 = sampledHash ω 0 ∧
        (sampledPairGame.run (0, 1) ω).2 = 1)) ≤ 0 := by
    simp [sampledPairGame, prob]
  have h := cert_and_of_game sampledPairGame (0, 1) 2 1 sampledHash
    (fun ω => sampledHash ω 0) (fun _ => True)
    (fun ω => sampledHash ω 1 = sampledHash ω 0)
    (fun x => x = 0) (fun x => x = 1) 0 0 (1 / 2)
    h₁ h₂ sampled_compressing_secure sampled_budget_inhabited
  norm_num [sampledPairGame] at h
  exact h

end Keystone

end Minidregg.Selvage.BindingGame

/-! Axiom audit: exact declarations, no unpinned theorem exports. -/
/-- info: 'Minidregg.Selvage.BindingGame.mean_const' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.mean_const
/-- info: 'Minidregg.Selvage.BindingGame.prob_eq_mean' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.prob_eq_mean
/-- info: 'Minidregg.Selvage.BindingGame.prob_true' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.prob_true
/-- info: 'Minidregg.Selvage.BindingGame.prob_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.prob_mono
/-- info: 'Minidregg.Selvage.BindingGame.prob_or' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.prob_or
/-- info: 'Minidregg.Selvage.BindingGame.prob_le_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.prob_le_one
/-- info: 'Minidregg.Selvage.BindingGame.Experiment.within_map' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.Experiment.within_map
/-- info: 'Minidregg.Selvage.BindingGame.advantage_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.advantage_reduction
/-- info: 'Minidregg.Selvage.BindingGame.flat_collision_reduction' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.flat_collision_reduction
/-- info: 'Minidregg.Selvage.BindingGame.cert_and_of_game' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.cert_and_of_game
/-- info: 'Minidregg.Selvage.BindingGame.cert_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.cert_and
/-- info: 'Minidregg.Selvage.BindingGame.receipt_and' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.receipt_and
/-- info: 'Minidregg.Selvage.BindingGame.mean_bad_transfer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.mean_bad_transfer
/-- info: 'Minidregg.Selvage.BindingGame.Keystone.pairGame_inhabited' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.Keystone.pairGame_inhabited
/-- info: 'Minidregg.Selvage.BindingGame.Keystone.pairGame_advantage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.Keystone.pairGame_advantage
/-- info: 'Minidregg.Selvage.BindingGame.Keystone.zero_budget_refuted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.Keystone.zero_budget_refuted
/-- info: 'Minidregg.Selvage.BindingGame.Keystone.budget_inhabited' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.Keystone.budget_inhabited
/-- info: 'Minidregg.Selvage.BindingGame.Keystone.conjunction_requires_binding' does not depend on any axioms -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.Keystone.conjunction_requires_binding
/-- info: 'Minidregg.Selvage.BindingGame.Keystone.global_not_history_conditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.Keystone.global_not_history_conditional
/-- info: 'Minidregg.Selvage.BindingGame.Keystone.rare_history_counterexample' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.Keystone.rare_history_counterexample
/-- info: 'Minidregg.Selvage.BindingGame.Keystone.identity_secure_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.Keystone.identity_secure_zero
/-- info: 'Minidregg.Selvage.BindingGame.Keystone.global_transfer_tight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.Keystone.global_transfer_tight
/-- info: 'Minidregg.Selvage.BindingGame.Keystone.sampled_budget_inhabited' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.Keystone.sampled_budget_inhabited
/-- info: 'Minidregg.Selvage.BindingGame.Keystone.sampled_compressing_secure' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.Keystone.sampled_compressing_secure

/-- info: 'Minidregg.Selvage.BindingGame.Keystone.certificate_game_fires' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Selvage.BindingGame.Keystone.certificate_game_fires
