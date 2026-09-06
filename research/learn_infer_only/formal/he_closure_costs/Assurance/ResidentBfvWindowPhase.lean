/-
Closed premise inhabitant for the modular queue/noise composition at Q83.
The ciphertext is one logical ZMod Q coefficient, not a BFV ciphertext.
The codec and phase interpretation are transparent; no secrecy is claimed.
It demonstrates a nonzero query, message and error in a reachable public
queue, and checks that a different same-plaintext phase cannot expire it.
-/
import Theory.CiphertextWindowNoise
import Assurance.ResidentBfvWindowNoise
import Assurance.CiphertextWindowCell

namespace Minidregg.Assurance.ResidentBfvWindowPhase
set_option autoImplicit false
open Minidregg.Theory.IntegerWindowNoise
open Minidregg.Theory.CiphertextWindow
open Minidregg.Theory.CiphertextWindowNoise
open Minidregg.Assurance.ResidentBfvWindowNoise
open Minidregg.Assurance.CiphertextWindowCell

abbrev qNat : Nat := 9671406214650060397780993
abbrev Ct := ZMod qNat
def codec := (coeffStream qNat).toLawful
def admit (_ : Nat) (_ : List UInt8) : Bool := true
def phase : Ct →+ ZMod qNat := AddMonoidHom.id _
def interpret (_ : Entry Ct) : Row width := witnessRow
def integerPhase : Int := rowPhase witnessQuery witnessRow
def ciphertext : Ct := (integerPhase : ZMod qNat)
def command : Command Ct := ⟨⟨0, ciphertext⟩, none⟩
def state : State Ct := advance window initial command

def Subject : Prop :=
  Reachable codec admit window state ∧
  PhasePremises qNat width phase interpret witnessQuery state integerPhase ∧
  ActualPremises (state.queue.map interpret) witnessQuery ∧
  centered t32 (rounded q83 t32 integerPhase) = -1

theorem checked : check codec admit window initial command = true := by
  simp [check, initial, command, window, admit]

theorem reached : Reachable codec admit window state := .next .start command checked

theorem phase_premises : PhasePremises qNat width phase interpret witnessQuery state integerPhase := by
  constructor
  · intro e he
    have heq : e = command.fresh := by simpa [state, advance, initial, window] using he
    subst e
    rfl
  · simp [state, advance, initial, window, phase, command, ciphertext]

theorem queue_rows : state.queue.map interpret = [witnessRow] := by rfl

theorem fresh_rows : ∀ e ∈ state.queue, Fresh (qNat : Int) t32 freshBound (interpret e) := by
  intro e _
  exact witness_fresh

theorem actual_premises : ActualPremises (state.queue.map interpret) witnessQuery := by
  rw [queue_rows]
  refine ⟨?_, by decide, witness_premises.2.2.1, ?_⟩
  · intro x hx
    simp only [List.mem_singleton] at hx
    subst x
    exact witness_fresh
  · intro x hx j
    simp only [List.mem_singleton] at hx
    subst x
    exact witness_premises.2.2.2 witnessRow (by simp [witnessWindow, window]) j

theorem queue_score : readoutScore witnessQuery (state.queue.map interpret) = -1 := by
  rw [queue_rows]
  simpa [readoutScore] using witness_row_score

theorem decoded : centered t32 (rounded q83 t32 integerPhase) = -1 := by
  have h := reachable_signed_decode qNat width window t32 freshBound queryBudget
    (by decide) (by decide) (by decide) actual_margin codec admit phase interpret
    witnessQuery state integerPhase reached phase_premises fresh_rows
    (queryL1_le witnessQuery coordinateBound witness_premises.2.2.1)
    (by rw [queue_score]; decide)
  simpa [queue_score] using h

theorem subject : Subject := ⟨reached, phase_premises, actual_premises, decoded⟩

theorem nonzero_message_error_query :
    witnessRow.message firstCoordinate = 1 ∧ witnessRow.error firstCoordinate = 1 ∧
    witnessQuery firstCoordinate = -1 := by decide

/-- The negative query turns fresh error 1 into phase -(floor(Q/t)+1).
A replacement error 0 yields a distinct phase but the same signed output. -/
def replacement : Ct := ((integerPhase + 1 : Int) : ZMod qNat)

theorem row_phase_exact : integerPhase = -(q83 / t32 + 1) := by
  simp [integerPhase, rowPhase, witnessQuery, witnessRow]

theorem same_plaintext_distinct_phase :
    centered t32 (rounded q83 t32 (integerPhase + 1)) = -1 ∧ replacement ≠ ciphertext := by
  rw [row_phase_exact]
  constructor
  · decide
  · change (((integerPhase + 1 : Int) : ZMod qNat) ≠ (integerPhase : ZMod qNat))
    intro he
    have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub (integerPhase + 1) integerPhase qNat).mp he
    norm_num at hd

theorem different_expiry_bytes_refused :
    sameSerialized codec command.fresh ⟨0, replacement⟩ = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  have he := sameSerialized_eq codec command.fresh ⟨0, replacement⟩ h
  have hc := congrArg Entry.ciphertext he
  exact same_plaintext_distinct_phase.2 hc

theorem nonzero_ciphertext : ciphertext ≠ 0 := by
  unfold ciphertext
  rw [row_phase_exact]
  decide

/- Axiom closure pins. -/
/-- info: 'Minidregg.Assurance.ResidentBfvWindowPhase.checked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowPhase.checked
/-- info: 'Minidregg.Assurance.ResidentBfvWindowPhase.reached' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowPhase.reached
/-- info: 'Minidregg.Assurance.ResidentBfvWindowPhase.phase_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowPhase.phase_premises
/-- info: 'Minidregg.Assurance.ResidentBfvWindowPhase.queue_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowPhase.queue_rows
/-- info: 'Minidregg.Assurance.ResidentBfvWindowPhase.fresh_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowPhase.fresh_rows
/-- info: 'Minidregg.Assurance.ResidentBfvWindowPhase.actual_premises' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowPhase.actual_premises
/-- info: 'Minidregg.Assurance.ResidentBfvWindowPhase.queue_score' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowPhase.queue_score
/-- info: 'Minidregg.Assurance.ResidentBfvWindowPhase.decoded' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowPhase.decoded
/-- info: 'Minidregg.Assurance.ResidentBfvWindowPhase.subject' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowPhase.subject
/-- info: 'Minidregg.Assurance.ResidentBfvWindowPhase.nonzero_message_error_query' does not depend on any axioms -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowPhase.nonzero_message_error_query
/-- info: 'Minidregg.Assurance.ResidentBfvWindowPhase.row_phase_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowPhase.row_phase_exact
/-- info: 'Minidregg.Assurance.ResidentBfvWindowPhase.same_plaintext_distinct_phase' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowPhase.same_plaintext_distinct_phase
/-- info: 'Minidregg.Assurance.ResidentBfvWindowPhase.different_expiry_bytes_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowPhase.different_expiry_bytes_refused
/-- info: 'Minidregg.Assurance.ResidentBfvWindowPhase.nonzero_ciphertext' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Assurance.ResidentBfvWindowPhase.nonzero_ciphertext

end Minidregg.Assurance.ResidentBfvWindowPhase
