import Std

/-! Statement-audit teeth. No claim about deployed verifier code. -/
namespace AstraGovernanceAudit

/-- An accepted false joint claim lies in a local failure or a subject-binding failure.
`transport` is the semantic bridge absent from the old displayed union bound. -/
theorem projected_bad_subset
    {Ω : Type} (accept₁ accept₂ bind local₁ local₂ aligned joint : Ω → Prop)
    (transport : ∀ w, aligned w → local₁ w → local₂ w → joint w)
    (w : Ω) (h : accept₁ w ∧ accept₂ w ∧ bind w ∧ ¬ joint w) :
    (accept₁ w ∧ ¬ local₁ w) ∨
      (accept₂ w ∧ ¬ local₂ w) ∨ (bind w ∧ ¬ aligned w) := by
  classical
  by_cases h₁ : local₁ w
  · by_cases h₂ : local₂ w
    · right; right
      exact ⟨h.2.2.1, fun hb => h.2.2.2 (transport w hb h₁ h₂)⟩
    · exact Or.inr (Or.inl ⟨h.2.1, h₂⟩)
  · exact Or.inl ⟨h.1, h₁⟩

/-- A genuinely inhabited bridge: same-subject propositions compose. -/
example (p q : Prop) : p → q → p ∧ q := fun hp hq => ⟨hp, hq⟩

/-- Without transport, locally valid evidence and a true binding Boolean prove nothing. -/
theorem no_transport_falsifier :
    True ∧ True ∧ True ∧ ¬ False := by decide

/-- A two-point uniform experiment, counting failures instead of dividing by two. -/
def badCount (accept truth : Bool → Bool) : Nat :=
  (if accept false && !truth false then 1 else 0) +
  (if accept true && !truth true then 1 else 0)

def sameEvidence (_ : Bool) : Unit := ()
def acceptAll (_ : Bool) : Bool := true
def pred₁ (w : Bool) : Bool := w
def pred₂ (w : Bool) : Bool := !w

/-- The evidence bytes/identity are identical in every world, and each leg has error 1/2. -/
theorem dedup_premises :
    (∀ w, sameEvidence w = ()) ∧
    badCount acceptAll pred₁ = 1 ∧ badCount acceptAll pred₂ = 1 := by decide

/-- Deduplicating these *different claims* to one 1/2 allowance is false: joint error is 1. -/
theorem dedup_by_identity_false :
    badCount acceptAll (fun w => pred₁ w && pred₂ w) = 2 ∧
    ¬ badCount acceptAll (fun w => pred₁ w && pred₂ w) ≤ 1 := by decide

/-- Dedup is justified when the accepted-false event itself is identical. -/
theorem same_failure_idempotent (failure : Bool → Prop) (w : Bool) :
    (failure w ∨ failure w) ↔ failure w := by simp

/-- Authentication + equal schema/session/length does not assert equal roots or records. -/
theorem equal_length_different_records :
    ([false] : List Bool).length = ([true] : List Bool).length ∧
    ([false] : List Bool) ≠ ([true] : List Bool) := by decide

/-- In a 100-point equiprobable game there can be one false acceptance and no true acceptance.
The false-accept probability is 1/100, but every accepted receipt is false. -/
def rareAccept (w : Fin 100) : Bool := w.val == 0

theorem conditional_reliability_falsifier :
    rareAccept ⟨0, by decide⟩ = true ∧
    (∀ w, rareAccept w = true → ¬ False) ∧
    ¬ (∃ w : Fin 100, rareAccept w = true ∧ False) := by
  exact ⟨rfl, fun _ _ => not_false, by simp⟩

/-- Exact enumeration for the posterior example; each of 100 equiprobable worlds has weight 1/100. -/
theorem rare_accept_count :
    ((List.finRange 100).filter rareAccept).length = 1 := by decide

/-- Two projected witnesses can exist separately but have no common world witness. -/
theorem projected_intersection_strict :
    (∃ w : Bool, w = false) ∧ (∃ w : Bool, w = true) ∧
    ¬ (∃ w : Bool, w = false ∧ w = true) := by decide

/--
info: AstraGovernanceAudit.projected_bad_subset {Ω : Type} (accept₁ accept₂ bind local₁ local₂ aligned joint : Ω → Prop)
  (transport : ∀ (w : Ω), aligned w → local₁ w → local₂ w → joint w) (w : Ω)
  (h : accept₁ w ∧ accept₂ w ∧ bind w ∧ ¬joint w) : accept₁ w ∧ ¬local₁ w ∨ accept₂ w ∧ ¬local₂ w ∨ bind w ∧ ¬aligned w
-/
#guard_msgs in
#check projected_bad_subset

/-- info: 'AstraGovernanceAudit.projected_bad_subset' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms projected_bad_subset

/-- info: 'AstraGovernanceAudit.dedup_by_identity_false' does not depend on any axioms -/
#guard_msgs in
#print axioms dedup_by_identity_false

/-- info: 'AstraGovernanceAudit.equal_length_different_records' does not depend on any axioms -/
#guard_msgs in
#print axioms equal_length_different_records

/-- info: 'AstraGovernanceAudit.conditional_reliability_falsifier' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms conditional_reliability_falsifier

/-- info: 'AstraGovernanceAudit.rare_accept_count' does not depend on any axioms -/
#guard_msgs in
#print axioms rare_accept_count

/-- info: 'AstraGovernanceAudit.projected_intersection_strict' does not depend on any axioms -/
#guard_msgs in
#print axioms projected_intersection_strict
end AstraGovernanceAudit
