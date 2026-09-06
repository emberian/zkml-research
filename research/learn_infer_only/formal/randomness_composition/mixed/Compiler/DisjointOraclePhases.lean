/-
Statement-first: a two-phase adaptive query strategy runs against ONE shared
cache. Disjoint Sum-tagged query encodings make its trace pathwise equal to
concatenated local traces; this derives, rather than assumes, the product-coin
coupling. The second strategy may depend on the entire first response history.
The proof is a cache transport, not a soundness theorem for a dummy relation.
ATLAS witnesses/falsifiers are instantiated in ResidentMixedPhases.
-/
import Selvage.Depth

namespace Minidregg.Compiler.DisjointOraclePhases
open Minidregg.Selvage
open Classical
set_option autoImplicit false

variable {Q Q₀ Q₁ C : Type} [DecidableEq Q] [DecidableEq Q₀] [DecidableEq Q₁]

/-- First occurrence cache lookup with a supplied fresh fallback. -/
def answer (L : List (Q × C)) (q : Q) (fallback : C) : C :=
  match L with
  | [] => fallback
  | e :: rest => if e.1=q then e.2 else answer rest q fallback

/-- A positional coin is consumed even if an old answer is reused. -/
def step (ask : List C → Q) (L : List (Q × C)) (coin : C) : List (Q × C) :=
  let q := ask (L.map Prod.snd)
  L ++ [(q,answer L q coin)]

def run (ask : List C → Q) (L : List (Q × C)) (coins : List C) : List (Q × C) :=
  coins.foldl (step ask) L

def liftLeft (L : List (Q₀ × C)) : List ((Q₀ ⊕ Q₁) × C) :=
  L.map (fun e => (Sum.inl e.1,e.2))
def liftRight (L : List (Q₁ × C)) : List ((Q₀ ⊕ Q₁) × C) :=
  L.map (fun e => (Sum.inr e.1,e.2))
def leftLog (L : List ((Q₀ ⊕ Q₁) × C)) : List (Q₀ × C) :=
  L.filterMap (fun e => match e.1 with | .inl q => some (q,e.2) | .inr _ => none)
def rightLog (L : List ((Q₀ ⊕ Q₁) × C)) : List (Q₁ × C) :=
  L.filterMap (fun e => match e.1 with | .inl _ => none | .inr q => some (q,e.2))

/-- The tag determines which local response history is visible to the active
program strategy. Both strategies' answers still come from the same full log. -/
def leftStep (ask : List C → Q₀) (L : List ((Q₀ ⊕ Q₁) × C)) (coin : C) :=
  let q := Sum.inl (ask ((leftLog L).map Prod.snd))
  L ++ [(q,answer L q coin)]
def rightStep (ask : List C → Q₁) (L : List ((Q₀ ⊕ Q₁) × C)) (coin : C) :=
  let q := Sum.inr (ask ((rightLog L).map Prod.snd))
  L ++ [(q,answer L q coin)]

def mixedTrace (ask₀ : List C → Q₀) (ask₁ : List C → List C → Q₁)
    (coins₀ coins₁ : List C) : List ((Q₀ ⊕ Q₁) × C) :=
  let first := coins₀.foldl (leftStep ask₀) []
  coins₁.foldl (rightStep (ask₁ (first.map Prod.snd))) first

theorem answer_append (A B : List (Q × C)) (q : Q) (c : C) :
    answer (A++B) q c = answer A q (answer B q c) := by
  induction A with
  | nil => rfl
  | cons a A ih => simp only [List.cons_append,answer]; split <;> simp_all

theorem tagged_answers (A : List (Q₀ × C)) (B : List (Q₁ × C)) (c : C) :
    (∀ q,answer (liftLeft A++liftRight B) (.inl q) c=answer A q c) ∧
    (∀ q,answer (liftLeft A++liftRight B) (.inr q) c=answer B q c) := by
  have left_other : ∀ q, answer (liftRight B : List ((Q₀ ⊕ Q₁) × C)) (.inl q) c=c := by
    intro q;induction B with
    | nil => rfl
    | cons b B ih => simpa [liftRight,answer] using ih
  have left_same : ∀ q c, answer (liftLeft A : List ((Q₀ ⊕ Q₁) × C)) (.inl q) c=answer A q c := by
    intro q c;induction A with
    | nil => rfl
    | cons a A ih => simpa [liftLeft,answer] using congrArg (fun x=>if a.1=q then a.2 else x) ih
  have right_other : ∀ q c, answer (liftLeft A : List ((Q₀ ⊕ Q₁) × C)) (.inr q) c=c := by
    clear left_same
    intro q c;induction A with
    | nil => rfl
    | cons a A ih => simpa [liftLeft,answer] using ih
  have right_same : ∀ q, answer (liftRight B : List ((Q₀ ⊕ Q₁) × C)) (.inr q) c=answer B q c := by
    clear left_other
    intro q;induction B with
    | nil => rfl
    | cons b B ih => simpa [liftRight,answer] using congrArg (fun x=>if b.1=q then b.2 else x) ih
  constructor
  · intro q;rw [answer_append,left_other,left_same]
  · intro q;rw [answer_append,right_other,right_same]

omit [DecidableEq Q₀] [DecidableEq Q₁] in
theorem tagged_projections (A : List (Q₀ × C)) (B : List (Q₁ × C)) :
    leftLog (liftLeft A++liftRight B)=A ∧ rightLog (liftLeft A++liftRight B)=B := by
  constructor <;> simp [leftLog,rightLog,liftLeft,liftRight,List.filterMap_map]

theorem left_step_transport (ask : List C → Q₀) (A : List (Q₀ × C)) (c : C) :
    leftStep ask (liftLeft A : List ((Q₀ ⊕ Q₁) × C)) c=liftLeft (step ask A c) := by
  have hp := (tagged_projections A ([] : List (Q₁ × C))).1
  have ha := (tagged_answers A ([] : List (Q₁ × C)) c).1
  simp only [liftRight,List.map_nil,List.append_nil] at hp ha
  unfold leftStep
  rw [hp]
  dsimp only
  rw [ha]
  simp only [step,liftLeft,List.map_append,List.map_cons,List.map_nil]

theorem right_step_transport (ask : List C → Q₁) (A : List (Q₀ × C))
    (B : List (Q₁ × C)) (c : C) :
    rightStep ask (liftLeft A++liftRight B) c=liftLeft A++liftRight (step ask B c) := by
  have hp := (tagged_projections A B).2
  have ha := (tagged_answers A B c).2
  unfold rightStep
  rw [hp]
  dsimp only
  rw [ha]
  simp only [step,liftRight,List.map_append,List.map_cons,List.map_nil,List.append_assoc]

theorem left_run_transport (ask : List C → Q₀) (coins : List C) (A : List (Q₀ × C)) :
    coins.foldl (leftStep ask) (liftLeft A : List ((Q₀ ⊕ Q₁) × C))=liftLeft (run ask A coins) := by
  induction coins generalizing A with
  | nil => rfl
  | cons c cs ih => simpa only [List.foldl_cons,left_step_transport,run] using ih (step ask A c)

theorem right_run_transport (ask : List C → Q₁) (coins : List C)
    (A : List (Q₀ × C)) (B : List (Q₁ × C)) :
    coins.foldl (rightStep ask) (liftLeft A++liftRight B)=liftLeft A++liftRight (run ask B coins) := by
  induction coins generalizing B with
  | nil => rfl
  | cons c cs ih => simpa only [List.foldl_cons,right_step_transport,run] using ih (step ask B c)

theorem mixed_trace_coupling (ask₀ : List C → Q₀) (ask₁ : List C → List C → Q₁)
    (coins₀ coins₁ : List C) :
    mixedTrace ask₀ ask₁ coins₀ coins₁ =
      let A := run ask₀ [] coins₀
      liftLeft A++liftRight (run (ask₁ (A.map Prod.snd)) [] coins₁) := by
  unfold mixedTrace
  have h₀ := left_run_transport (Q₁:=Q₁) ask₀ coins₀ []
  change coins₀.foldl (leftStep ask₀) []=liftLeft (run ask₀ [] coins₀) at h₀
  rw [h₀]
  dsimp only
  have hmap : (liftLeft (run ask₀ [] coins₀) : List ((Q₀ ⊕ Q₁) × C)).map Prod.snd=
      (run ask₀ [] coins₀).map Prod.snd := by simp [liftLeft,List.map_map]
  rw [hmap]
  simpa only [liftRight,List.map_nil,List.append_nil] using
    right_run_transport (ask₁ ((run ask₀ [] coins₀).map Prod.snd)) coins₁ (run ask₀ [] coins₀) []

theorem run_length (ask : List C → Q) (L : List (Q × C)) (coins : List C) :
    (run ask L coins).length=L.length+coins.length := by
  induction coins generalizing L with
  | nil => simp [run]
  | cons c cs ih => simpa [run,step,List.foldl_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih (step ask L c)

theorem mixed_query_budget (ask₀ : List C → Q₀) (ask₁ : List C → List C → Q₁)
    (coins₀ coins₁ : List C) :
    (mixedTrace ask₀ ask₁ coins₀ coins₁).length=coins₀.length+coins₁.length := by
  rw [mixed_trace_coupling]
  simp [liftLeft,liftRight,run_length]

theorem answer_eq_find (L : List (Q × C)) (q : Q) (c : C) :
    answer L q c = match L.find? (fun e => decide (e.1=q)) with | some e=>e.2 | none=>c := by
  induction L with
  | nil => rfl
  | cons e L ih => simp only [answer,List.find?_cons];split <;> simp_all

/-- Exact transport into the pre-existing Fiat–Shamir game's cache engine. -/
theorem run_is_srTrace {r : Reduction} {s t : Nat} (P : SrProver r s)
    (coins : Fin t → r.Chal) : run P.move [] (List.ofFn coins)=srTrace P coins := by
  classical
  rw [srTrace_eq_runFrom]
  unfold run runFrom
  have h : step P.move=stepOnce P := by
    funext L c;simp only [step,stepOnce,answer_eq_find];congr 6
    cases L.find? (fun e=>decide (e.1=P.move (L.map Prod.snd))) <;> rfl
  rw [h]

/-- Product slicing requires no event independence: the right event is bounded
for EVERY left history, including histories selected adaptively by the first
program. The uniform product here is justified by the pathwise cache coupling. -/
theorem two_phase_union_bound {A B : Type} [Fintype A] [Fintype B]
    (p : A → Prop) (q : A → B → Prop) {ε₀ ε₁ : ℝ}
    (h₀ : uniformProb A p ≤ ε₀) (h₁ : ∀ a,uniformProb B (q a) ≤ ε₁)
    (nonneg₁ : 0≤ε₁) :
    uniformProb (A×B) (fun c=>p c.1 ∨ q c.1 c.2) ≤ ε₀+ε₁ := by
  have left : uniformProb (A×B) (fun c=>p c.1) ≤ ε₀ := by
    rw [←uniformProb_equiv (Equiv.prodComm B A) (fun c : A×B=>p c.1)]
    exact uniformProb_prod_le (le_trans (uniformProb_nonneg p) h₀) (fun _=>h₀)
  have right : uniformProb (A×B) (fun c=>q c.1 c.2) ≤ ε₁ :=
    uniformProb_prod_le nonneg₁ h₁
  exact le_trans (uniformProb_or_le _ _) (add_le_add left right)

/-- Injective transport preserves every cached answer, including repeats.
The resident adapter supplies the actual Stage0/EMA byte encoder. -/
theorem encoded_answer_transport {Bytes : Type} [DecidableEq Bytes]
    (encode : Q → Bytes) (injective : Function.Injective encode)
    (L : List (Q × C)) (q : Q) (c : C) :
    answer (L.map (fun e=>(encode e.1,e.2))) (encode q) c=answer L q c := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [List.map_cons,answer]
    have same : encode e.1=encode q ↔ e.1=q := injective.eq_iff
    simp only [same,ih]

theorem answer_eq_getD (L : List (Q × C)) (q : Q) (c : C) :
    answer L q c=((L.find? (fun e=>decide (e.1=q))).map Prod.snd).getD c := by
  rw [answer_eq_find]
  cases L.find? (fun e=>decide (e.1=q)) <;> rfl

end Minidregg.Compiler.DisjointOraclePhases

/-- info: 'Minidregg.Compiler.DisjointOraclePhases.answer_append' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DisjointOraclePhases.answer_append
/-- info: 'Minidregg.Compiler.DisjointOraclePhases.tagged_answers' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DisjointOraclePhases.tagged_answers
/-- info: 'Minidregg.Compiler.DisjointOraclePhases.tagged_projections' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DisjointOraclePhases.tagged_projections
/-- info: 'Minidregg.Compiler.DisjointOraclePhases.left_step_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DisjointOraclePhases.left_step_transport
/-- info: 'Minidregg.Compiler.DisjointOraclePhases.right_step_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DisjointOraclePhases.right_step_transport
/-- info: 'Minidregg.Compiler.DisjointOraclePhases.left_run_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DisjointOraclePhases.left_run_transport
/-- info: 'Minidregg.Compiler.DisjointOraclePhases.right_run_transport' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DisjointOraclePhases.right_run_transport
/-- info: 'Minidregg.Compiler.DisjointOraclePhases.mixed_trace_coupling' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DisjointOraclePhases.mixed_trace_coupling
/-- info: 'Minidregg.Compiler.DisjointOraclePhases.run_length' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DisjointOraclePhases.run_length
/-- info: 'Minidregg.Compiler.DisjointOraclePhases.mixed_query_budget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DisjointOraclePhases.mixed_query_budget
/-- info: 'Minidregg.Compiler.DisjointOraclePhases.answer_eq_find' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DisjointOraclePhases.answer_eq_find
/-- info: 'Minidregg.Compiler.DisjointOraclePhases.run_is_srTrace' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DisjointOraclePhases.run_is_srTrace
/-- info: 'Minidregg.Compiler.DisjointOraclePhases.two_phase_union_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DisjointOraclePhases.two_phase_union_bound
/-- info: 'Minidregg.Compiler.DisjointOraclePhases.encoded_answer_transport' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DisjointOraclePhases.encoded_answer_transport
/-- info: 'Minidregg.Compiler.DisjointOraclePhases.answer_eq_getD' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms Minidregg.Compiler.DisjointOraclePhases.answer_eq_getD
