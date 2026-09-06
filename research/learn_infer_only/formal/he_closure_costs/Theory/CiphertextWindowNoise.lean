/-
A modular phase bridge from the public exact-ciphertext queue to the integer
noise ledger. The additive phase has codomain ZMod q, never the integers.
Its existence and its relation to actual ciphertext/RNS/readout operations
are explicit source-equation premises, not established by this module.
-/
import Theory.CiphertextWindow
import Theory.IntegerWindowNoise
import Mathlib.Data.ZMod.Basic

namespace Minidregg.Theory.CiphertextWindowNoise
set_option autoImplicit false
open Minidregg.Theory.IntegerWindowNoise
open Minidregg.Theory.CiphertextWindow
open Minidregg.Theory.IndexedProgram

variable {Ct : Type} [AddCommGroup Ct]

/-- A fixed public query determines this modular phase interpretation. -/
def PhasePremises (q : Nat) (r : Nat) (phase : Ct →+ ZMod q)
    (interpret : Entry Ct → Row r) (query : Fin r → Int)
    (s : State Ct) (outputLift : Int) : Prop :=
  (∀ e ∈ s.queue, phase e.ciphertext = (rowPhase query (interpret e) : ZMod q)) ∧
  (outputLift : ZMod q) = phase s.accumulator

/-- Mapping the exact queue sum gives the sum of its current fresh phases.
It contains no term indexed by the elapsed history. -/
theorem queue_phase_sum (q r : Nat) (phase : Ct →+ ZMod q)
    (interpret : Entry Ct → Row r) (query : Fin r → Int)
    (queue : List (Entry Ct))
    (h : ∀ e ∈ queue, phase e.ciphertext = (rowPhase query (interpret e) : ZMod q)) :
    phase (queueSum queue) = (readoutPhase query (queue.map interpret) : ZMod q) := by
  induction queue with
  | nil => simp [queueSum, readoutPhase]
  | cons e rest ih =>
    have he := h e (by simp)
    have hr := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [queueSum, List.map_cons, List.sum_cons, map_add] at *
    simp only [readoutPhase, List.map_cons, List.sum_cons, Int.cast_add]
    rw [he, hr]
    rfl

/-- An implementation-provided integer lift differs from the sum by Qk. -/
theorem queue_integer_lift (q r : Nat) (phase : Ct →+ ZMod q)
    (interpret : Entry Ct → Row r) (query : Fin r → Int)
    (s : State Ct) (outputLift : Int)
    (hsum : s.accumulator = queueSum s.queue)
    (hp : PhasePremises q r phase interpret query s outputLift) :
    ∃ wrap : Int, outputLift = readoutPhase query (s.queue.map interpret) + (q : Int) * wrap := by
  have he : (outputLift : ZMod q) = (readoutPhase query (s.queue.map interpret) : ZMod q) := by
    rw [hp.2, hsum]
    exact queue_phase_sum q r phase interpret query s.queue hp.1
  have hd := (ZMod.intCast_eq_intCast_iff_dvd_sub
    (readoutPhase query (s.queue.map interpret)) outputLift q).mp he.symm
  obtain ⟨wrap, hw⟩ := hd
  exact ⟨wrap, by linarith⟩

/-- All-history correctness is conditional only on current admitted rows,
the finite window bound and the modular implementation equations. -/
theorem reachable_decode (q r W : Nat) (t E L : Int)
    (hq : 0 < (q : Int)) (ht : 0 < t) (hE : 0 ≤ E)
    (margin : 2 * t * (W : Int) * L * (E + 1) < (q : Int))
    (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool)
    (phase : Ct →+ ZMod q) (interpret : Entry Ct → Row r)
    (query : Fin r → Int) (s : State Ct) (outputLift : Int)
    (reached : Reachable codec admit W s)
    (hp : PhasePremises q r phase interpret query s outputLift)
    (hf : ∀ e ∈ s.queue, Fresh (q : Int) t E (interpret e))
    (hL : queryL1 query ≤ L) :
    rounded (q : Int) t outputLift % t = readoutScore query (s.queue.map interpret) % t := by
  obtain ⟨hsum, hlen⟩ := reachable_queue_sum codec admit W s reached
  obtain ⟨wrap, hw⟩ := queue_integer_lift q r phase interpret query s outputLift hsum hp
  rw [hw]
  apply window_correctness (q : Int) t E L W hq ht hE margin
    r (s.queue.map interpret) query wrap
  · intro x hx
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
    exact hf e he
  · simpa only [List.length_map] using hlen
  · exact hL

/-- Signed decoding adds the actual output's strict nonwrap bound. -/
theorem reachable_signed_decode (q r W : Nat) (t E L : Int)
    (hq : 0 < (q : Int)) (ht : 0 < t) (hE : 0 ≤ E)
    (margin : 2 * t * (W : Int) * L * (E + 1) < (q : Int))
    (codec : LawfulCodec Ct) (admit : Nat → List UInt8 → Bool)
    (phase : Ct →+ ZMod q) (interpret : Entry Ct → Row r)
    (query : Fin r → Int) (s : State Ct) (outputLift : Int)
    (reached : Reachable codec admit W s)
    (hp : PhasePremises q r phase interpret query s outputLift)
    (hf : ∀ e ∈ s.queue, Fresh (q : Int) t E (interpret e))
    (hL : queryL1 query ≤ L)
    (hm : 2 * |readoutScore query (s.queue.map interpret)| < t) :
    centered t (rounded (q : Int) t outputLift) = readoutScore query (s.queue.map interpret) := by
  have h := reachable_decode q r W t E L hq ht hE margin codec admit phase
    interpret query s outputLift reached hp hf hL
  unfold centered
  rw [h]
  exact centered_exact t (readoutScore query (s.queue.map interpret)) hm

/- Axiom closure pins: mathematical Lean foundations only; no added axioms. -/
/-- info: 'Minidregg.Theory.CiphertextWindowNoise.queue_phase_sum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.CiphertextWindowNoise.queue_phase_sum
/-- info: 'Minidregg.Theory.CiphertextWindowNoise.queue_integer_lift' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.CiphertextWindowNoise.queue_integer_lift
/-- info: 'Minidregg.Theory.CiphertextWindowNoise.reachable_decode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.CiphertextWindowNoise.reachable_decode
/-- info: 'Minidregg.Theory.CiphertextWindowNoise.reachable_signed_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms Minidregg.Theory.CiphertextWindowNoise.reachable_signed_decode

end Minidregg.Theory.CiphertextWindowNoise
