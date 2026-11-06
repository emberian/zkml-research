import Lean

namespace Astra.CertificateAudit

/-- A faithful version of the proposal's fields, with Nat error units: the
problem is independent of which nonnegative numerical codomain is used. -/
structure ProposedScheme (Sym Digest Op : Type) where
  commit : List Sym → Digest
  openAt : List Sym → Nat → Op
  verifyOpen : Digest → Nat → Sym → Op → Bool
  verifyLen : Digest → Nat → Op → Bool
  complete : ∀ w i (h : i < w.length),
    verifyOpen (commit w) i w[i] (openAt w i) = true
  bindAdv : Nat → Nat

def zeroClaim : ProposedScheme Bool Unit Unit where
  commit := fun _ => ()
  openAt := fun _ _ => ()
  verifyOpen := fun _ _ _ _ => true
  verifyLen := fun _ _ _ => false
  complete := by intros; rfl
  bindAdv := fun _ => 0

theorem unbacked_advantage :
    zeroClaim.bindAdv 0 = 0 ∧
    zeroClaim.verifyOpen () 0 false () = true ∧
    zeroClaim.verifyOpen () 0 true () = true ∧ false ≠ true := by decide

def prefixScheme : ProposedScheme Unit Unit Unit where
  commit := fun _ => ()
  openAt := fun _ _ => ()
  verifyOpen := fun _ _ _ _ => true
  verifyLen := fun _ _ _ => false
  complete := by intros; rfl
  bindAdv := fun _ => 0

theorem prefix_perfect_position_binding (v v' : Unit) : v = v' := by
  cases v; cases v'; rfl

theorem prefix_word_collision :
    prefixScheme.commit [] = prefixScheme.commit [()] ∧
    ([] : List Unit) ≠ [()] := by decide

/-- This scheme commits injectively. Its extra digest `none` is nonetheless
accepted as a one-symbol root. Length and position uniqueness both hold. -/
def phantomCommit (w : List Unit) : Option (List Unit) := some w

def phantomVerify (c : Option (List Unit)) (i : Nat) : Bool :=
  match c with
  | none => i == 0
  | some w => i < w.length

def phantomLen (c : Option (List Unit)) (n : Nat) : Bool :=
  match c with
  | none => n == 1
  | some w => n == w.length

theorem phantom_accepted : phantomVerify none 0 = true ∧ phantomLen none 1 = true := by decide

theorem phantom_no_word : ¬ ∃ w, phantomCommit w = none := by
  rintro ⟨w, h⟩
  cases h

theorem phantom_length_unique (c : Option (List Unit)) (n m : Nat)
    (hn : phantomLen c n = true) (hm : phantomLen c m = true) : n = m := by
  cases c <;> simp [phantomLen] at hn hm <;> omega

abbrev At (w : List Nat) (i : Nat) (p : List Nat) : Prop :=
  i + p.length ≤ w.length ∧ (w.drop i).take p.length = p

theorem position_matters :
    At [0, 1, 2, 3, 4, 5] 2 [2, 3] ∧ ¬ At [0, 1, 2, 3, 4, 5] 1 [2, 3] := by decide

theorem unchecked_empty_pattern :
    (∀ _j : Fin ([] : List Nat).length, True) ∧ ¬ At [] 1 [] := by decide

theorem omitted_index :
    ([0, 1] : List Nat)[0]? = some 0 ∧ ¬ At [0, 1] 0 [0, 2] := by decide

theorem clamped_span :
    (([1] : List Nat).drop 99).take (100 - 99) = [] ∧
    ¬ (99 ≤ 100 ∧ 100 ≤ ([1] : List Nat).length) := by decide

variable {W D D' : Type}

def WordCollision (commit : W → D) (u v : W) : Prop :=
  u ≠ v ∧ commit u = commit v

theorem conjunction_or_collision (commit : W → D) (c : D)
    (φ ψ : W → Prop) (u v : W)
    (hu : commit u = c ∧ φ u) (hv : commit v = c ∧ ψ v) :
    (commit u = c ∧ φ u ∧ ψ u) ∨ WordCollision commit u v := by
  classical
  by_cases h : u = v
  · subst v
    exact Or.inl ⟨hu.1, hu.2, hv.2⟩
  · exact Or.inr ⟨h, hu.1.trans hv.1.symm⟩

theorem two_true_legs_false_join :
    prefixScheme.commit [] = () ∧ prefixScheme.commit [()] = () ∧
    ([] : List Unit).length = 0 ∧ ([()] : List Unit).length = 1 ∧
    ¬ ∃ w : List Unit, w.length = 0 ∧ w.length = 1 := by
  refine ⟨rfl, rfl, rfl, rfl, ?_⟩
  rintro ⟨w, h0, h1⟩
  omega

theorem transport_same_witness (s : W → D) (t : W → D') (f : D → D')
    (commutes : ∀ w, f (s w) = t w) (φ : W → Prop)
    (w : W) (c : D) (h : s w = c ∧ φ w) : t w = f c ∧ φ w := by
  exact ⟨(commutes w).symm.trans (congrArg f h.1), h.2⟩

/-- A fixed one-symbol language accepts [1], while [0,1,0] lies in its
whole-word complement and contains an accepted substring. -/
theorem complement_not_absence :
    ([0, 1, 0] : List Nat) ≠ [1] ∧ At [0, 1, 0] 1 [1] := by decide

/-- Two valid roots are legitimate when their committed contents differ.
A repair may not ban them merely because the descriptor is the same. -/
theorem distinct_honest_roots_allowed :
    phantomCommit [] ≠ phantomCommit [()] := by decide

/-- info: 'Astra.CertificateAudit.unbacked_advantage' does not depend on any axioms -/
#guard_msgs in
#print axioms unbacked_advantage
/-- info: 'Astra.CertificateAudit.prefix_perfect_position_binding' does not depend on any axioms -/
#guard_msgs in
#print axioms prefix_perfect_position_binding
/-- info: 'Astra.CertificateAudit.prefix_word_collision' does not depend on any axioms -/
#guard_msgs in
#print axioms prefix_word_collision
/-- info: 'Astra.CertificateAudit.phantom_accepted' does not depend on any axioms -/
#guard_msgs in
#print axioms phantom_accepted
/-- info: 'Astra.CertificateAudit.phantom_no_word' does not depend on any axioms -/
#guard_msgs in
#print axioms phantom_no_word
/-- info: 'Astra.CertificateAudit.phantom_length_unique' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms phantom_length_unique
/-- info: 'Astra.CertificateAudit.position_matters' does not depend on any axioms -/
#guard_msgs in
#print axioms position_matters
/-- info: 'Astra.CertificateAudit.unchecked_empty_pattern' does not depend on any axioms -/
#guard_msgs in
#print axioms unchecked_empty_pattern
/-- info: 'Astra.CertificateAudit.omitted_index' depends on axioms: [propext] -/
#guard_msgs in
#print axioms omitted_index
/-- info: 'Astra.CertificateAudit.clamped_span' does not depend on any axioms -/
#guard_msgs in
#print axioms clamped_span
/-- info: 'Astra.CertificateAudit.conjunction_or_collision' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms conjunction_or_collision
/-- info: 'Astra.CertificateAudit.two_true_legs_false_join' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms two_true_legs_false_join
/-- info: 'Astra.CertificateAudit.transport_same_witness' does not depend on any axioms -/
#guard_msgs in
#print axioms transport_same_witness
/-- info: 'Astra.CertificateAudit.complement_not_absence' does not depend on any axioms -/
#guard_msgs in
#print axioms complement_not_absence
/-- info: 'Astra.CertificateAudit.distinct_honest_roots_allowed' does not depend on any axioms -/
#guard_msgs in
#print axioms distinct_honest_roots_allowed

end Astra.CertificateAudit
