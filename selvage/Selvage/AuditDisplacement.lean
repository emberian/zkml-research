/-
# Selvage.AuditDisplacement — expected injected displacement before the first alarm.

`Selvage.AuditSampling` bounds the expected number of corrupt rounds before the
first alarm (`Round.sequential_bound`, `≤ 1/q`) and the leakage under a payload
cap (`Round.leakage_bound`, `≤ b/q`). This file prices the quantity a training
loop actually absorbs: the accumulated **displacement** `‖delta h − honest h‖`
between the update the round applied and the honest update, summed over the
rounds that ran before an alarm stopped the process.

* `Round.injected` — the pathwise accumulated displacement. It indexes rounds
  exactly as `Round.count` does: `injected (ω :: h)` reads the history `h`
  BEFORE the round's coin, and adds the round's displacement iff `h` is not yet
  stopped. A round that alarms still contributes (it was applied before it was
  caught), matching `count`.
* `Round.displacement_bound_of_gap` — the general form: if the displacement is
  at most `D` on every live corrupt round and zero on every honest round, the
  expected injected displacement is at most `D/q` at every horizon.
* `Round.displacement_bound` — the envelope form: `‖delta‖ ≤ B` and
  `‖honest‖ ≤ B` give `D = 2B`, so the bound is `2B/q`.
* `Round.displacement_bound_of_legs` — the same, from `DetectionLegs`.

**Teeth.** `DisplacementRefutation` runs the theorem on `AuditWitness.round`
(always corrupt, alarms with probability exactly `1/2`) at `B = 1`, `q = 1/2`,
claimed bound `4`. Dropping `hhonest` (honest update `5`, applied `0`) or
dropping `hactual` (applied `5`, honest `0`) gives expected injected displacement
`5 > 4` after a single round, with every remaining hypothesis satisfied. The
satisfiable instance (`applied 1`, honest `0`) meets every hypothesis and has
expected injected displacement `3/2` at horizon two: the bound constrains a
real, stopping-sensitive event.
-/
import Mathlib.Analysis.Normed.Group.Real
import Selvage.AuditSampling

namespace Minidregg.Selvage

namespace Round

variable {Ω V : Type}

/-- The accumulated injected displacement up to and including the first alarm.
`injected (ω :: h)` does not read `ω`, exactly like `count`: the round's update
is fixed before its beacon emits. -/
noncomputable def injected [NormedAddCommGroup V] (R : Round Ω)
    (delta honest : List Ω → V) : List Ω → ℝ
  | [] => 0
  | _ :: h =>
      R.injected delta honest h +
        if R.stopped h then 0 else ‖delta h - honest h‖

/-- **Pathwise domination.** If every live corrupt round displaces by at most
`D` and every honest round displaces by nothing, the injected displacement is
at most `D` times the corrupt-round count, on every history. -/
theorem injected_le_count [NormedAddCommGroup V] (R : Round Ω)
    (delta honest : List Ω → V) {D : ℝ}
    (hgap : ∀ h, R.stopped h = false → R.corrupt h = true →
      ‖delta h - honest h‖ ≤ D)
    (hcoverage : ∀ h, R.corrupt h = false → delta h = honest h) :
    ∀ h : List Ω, R.injected delta honest h ≤ D * (R.count h : ℝ)
  | [] => by simp [injected, count]
  | ω :: h => by
    have ih := injected_le_count R delta honest hgap hcoverage h
    show R.injected delta honest h +
        (if R.stopped h then 0 else ‖delta h - honest h‖)
      ≤ D * ((if R.stopped h then R.count h
          else if R.corrupt h then R.count h + 1 else R.count h : ℕ) : ℝ)
    cases hs : R.stopped h
    · cases hc : R.corrupt h
      · simp only [Bool.false_eq_true, ite_false, hcoverage h hc, sub_self, norm_zero]
        linarith
      · simp only [Bool.false_eq_true, ite_false, ite_true]
        have := hgap h hs hc
        push_cast
        linarith
    · simp only [ite_true]
      linarith

/-- **The general displacement bound.** Displacement at most `D` on live corrupt
rounds, zero on honest rounds, detection at least `q` on live corrupt rounds:
the expected injected displacement is at most `D/q` at every horizon. -/
theorem displacement_bound_of_gap [Fintype Ω] [Nonempty Ω] [NormedAddCommGroup V]
    (R : Round Ω) (delta honest : List Ω → V) {D q : ℝ} (hD : 0 ≤ D) (hq : 0 < q)
    (hgap : ∀ h, R.stopped h = false → R.corrupt h = true →
      ‖delta h - honest h‖ ≤ D)
    (hcoverage : ∀ h, R.corrupt h = false → delta h = honest h)
    (hdetect : ∀ h, R.stopped h = false → R.corrupt h = true →
      q ≤ uniformProb Ω (fun ω => R.alarms h ω))
    (n : ℕ) :
    expOver Ω n (R.injected delta honest) [] ≤ D / q :=
  le_trans (expOver.mono (injected_le_count R delta honest hgap hcoverage) n [])
    (leakage_bound hq hD hdetect n)

/-- **THE DISPLACEMENT BOUND.** If the applied update and the honest update are
each bounded by `B`, honest rounds apply the honest update, and every live
corrupt round alarms with probability at least `q`, then the expected injected
displacement before the first alarm is at most `2B/q`, at every horizon, against
a fully adaptive adversary.

`0 ≤ B` is not a hypothesis: it follows from `hactual` at the empty history. -/
theorem displacement_bound [Fintype Ω] [Nonempty Ω] [NormedAddCommGroup V]
    (R : Round Ω) (delta honest : List Ω → V) {B q : ℝ} (hq : 0 < q)
    (hactual : ∀ h, ‖delta h‖ ≤ B)
    (hhonest : ∀ h, ‖honest h‖ ≤ B)
    (hcoverage : ∀ h, R.corrupt h = false → delta h = honest h)
    (hdetect : ∀ h, R.stopped h = false → R.corrupt h = true →
      q ≤ uniformProb Ω (fun ω => R.alarms h ω))
    (n : ℕ) :
    expOver Ω n (R.injected delta honest) [] ≤ (2 * B) / q := by
  have hB : 0 ≤ B := le_trans (norm_nonneg _) (hactual [])
  refine displacement_bound_of_gap R delta honest (by linarith) hq
    (fun h _ _ => ?_) hcoverage hdetect n
  calc ‖delta h - honest h‖ ≤ ‖delta h‖ + ‖honest h‖ := norm_sub_le _ _
    _ ≤ 2 * B := by linarith [hactual h, hhonest h]

/-- The composed statement: the three legs give the displacement bound at the
composed budget `q = p(1 − ε_chk) − ε_bind − ε_beacon`. -/
theorem displacement_bound_of_legs [Fintype Ω] [Nonempty Ω] [NormedAddCommGroup V]
    {A : AuditParams} (R : Round Ω) (delta honest : List Ω → V) {B : ℝ}
    (hL : DetectionLegs A R) (hq : 0 < A.q)
    (hactual : ∀ h, ‖delta h‖ ≤ B)
    (hhonest : ∀ h, ‖honest h‖ ≤ B)
    (hcoverage : ∀ h, R.corrupt h = false → delta h = honest h)
    (n : ℕ) :
    expOver Ω n (R.injected delta honest) [] ≤ (2 * B) / A.q :=
  displacement_bound R delta honest hq hactual hhonest hcoverage
    (fun _ _ hc => detect hL hc) n

end Round

/-! ## Teeth -/

namespace DisplacementRefutation

/-- The detection hypothesis holds on `AuditWitness.round` at `q = 1/2`. -/
theorem detect_half (h : List (Fin 4)) (_ : AuditWitness.round.stopped h = false)
    (_ : AuditWitness.round.corrupt h = true) :
    (1 / 2 : ℝ) ≤ uniformProb (Fin 4) (fun ω => AuditWitness.round.alarms h ω) := by
  rw [AuditWitness.alarm_prob h]

/-- Coverage is vacuous on `AuditWitness.round`: every round is corrupt. -/
theorem coverage_any (delta honest : List (Fin 4) → ℝ) (h : List (Fin 4))
    (hc : AuditWitness.round.corrupt h = false) : delta h = honest h := by
  simp [AuditWitness.round] at hc

/-- One round of constant displacement `|a − b|`: the first round is live. -/
theorem injected_one (a b : ℝ) :
    expOver (Fin 4) 1 (AuditWitness.round.injected (fun _ => a) (fun _ => b)) [] = |a - b| := by
  have hval : ∀ ω : Fin 4, AuditWitness.round.injected (fun _ => a) (fun _ => b) [ω] = |a - b| := by
    intro ω
    simp [Round.injected, Round.stopped, Real.norm_eq_abs]
  rw [expOver.succ]
  simp only [expOver.zero, hval, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  norm_num

/-- **Dropping `hhonest` makes the bound FALSE.** On `AuditWitness.round` at
`B = 1`, `q = 1/2` (claimed bound `2B/q = 4`), the applied update `0` satisfies
`hactual`, coverage and detection hold, but the honest update `5` is outside
the envelope and one round injects `5 > 4`. -/
theorem bound_false_without_hhonest :
    ¬ ∀ (delta honest : List (Fin 4) → ℝ),
      (∀ h, ‖delta h‖ ≤ 1) →
      (∀ h, AuditWitness.round.corrupt h = false → delta h = honest h) →
      (∀ h, AuditWitness.round.stopped h = false → AuditWitness.round.corrupt h = true →
        (1 / 2 : ℝ) ≤ uniformProb (Fin 4) (fun ω => AuditWitness.round.alarms h ω)) →
      ∀ n, expOver (Fin 4) n (AuditWitness.round.injected delta honest) [] ≤ (2 * 1) / (1 / 2) := by
  intro hall
  have := hall (fun _ => 0) (fun _ => 5) (fun _ => by simp)
    (coverage_any _ _) detect_half 1
  rw [injected_one] at this
  norm_num at this

/-- **Dropping `hactual` makes the bound FALSE.** Same instance, roles swapped:
the honest update `0` satisfies `hhonest`, the applied update `5` does not, and
one round injects `5 > 4`. -/
theorem bound_false_without_hactual :
    ¬ ∀ (delta honest : List (Fin 4) → ℝ),
      (∀ h, ‖honest h‖ ≤ 1) →
      (∀ h, AuditWitness.round.corrupt h = false → delta h = honest h) →
      (∀ h, AuditWitness.round.stopped h = false → AuditWitness.round.corrupt h = true →
        (1 / 2 : ℝ) ≤ uniformProb (Fin 4) (fun ω => AuditWitness.round.alarms h ω)) →
      ∀ n, expOver (Fin 4) n (AuditWitness.round.injected delta honest) [] ≤ (2 * 1) / (1 / 2) := by
  intro hall
  have := hall (fun _ => 5) (fun _ => 0) (fun _ => by simp)
    (coverage_any _ _) detect_half 1
  rw [injected_one] at this
  norm_num at this

/-- **The premise is INHABITED.** Applied update `1`, honest `0`, `B = 1`,
`q = 1/2`: every hypothesis of `displacement_bound` holds, so the expected
injected displacement is at most `4` at every horizon. -/
theorem fired (n : ℕ) :
    expOver (Fin 4) n (AuditWitness.round.injected (fun _ => (1 : ℝ)) (fun _ => 0)) []
      ≤ (2 * 1) / (1 / 2) :=
  Round.displacement_bound AuditWitness.round _ _ (by norm_num) (fun _ => by simp) (fun _ => by simp)
    (coverage_any _ _) detect_half n

/-- …and the event is real and stopping-sensitive: at horizon two the expected
injected displacement is `3/2` — the first round always injects `1`, the second
only on the half of first coins that did not alarm. -/
theorem injected_two :
    expOver (Fin 4) 2 (AuditWitness.round.injected (fun _ => (1 : ℝ)) (fun _ => 0)) [] = 3 / 2 := by
  rw [expOver.succ]
  simp only [expOver.succ, expOver.zero, Fin.sum_univ_four]
  simp [Round.injected, Round.stopped, AuditWitness.round, AuditWitness.sel]
  norm_num

end DisplacementRefutation

/-- info: 'Minidregg.Selvage.Round.displacement_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round.displacement_bound
/-- info: 'Minidregg.Selvage.Round.displacement_bound_of_gap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round.displacement_bound_of_gap
/-- info: 'Minidregg.Selvage.Round.displacement_bound_of_legs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Round.displacement_bound_of_legs
/-- info: 'Minidregg.Selvage.DisplacementRefutation.bound_false_without_hhonest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DisplacementRefutation.bound_false_without_hhonest
/-- info: 'Minidregg.Selvage.DisplacementRefutation.bound_false_without_hactual' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DisplacementRefutation.bound_false_without_hactual
/-- info: 'Minidregg.Selvage.DisplacementRefutation.fired' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DisplacementRefutation.fired
/-- info: 'Minidregg.Selvage.DisplacementRefutation.injected_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms DisplacementRefutation.injected_two

end Minidregg.Selvage
