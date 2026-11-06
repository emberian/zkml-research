/-
# Selvage.AuditChecked — the commit-then-audit theorem over a checked world, for any checker

`Selvage/AuditSampling.lean` proves, for an abstract `Round`, that the expected number of corrupt
rounds before the first alarm is at most `1/q`. This file builds the `Round` an auditor runs when
its selection and alarm are the exported `fires` and `alarm` of `Selvage/AuditDecideCore.lean` and
its verdict is a checker's exported verdict, proves it fail-closed, and composes the sequential bound
with a run-level bad event: draw the world once (an oracle, or nothing), run `n` rounds with fresh
coins, and `E[C_{τ∧n}] ≤ 1/q + n·(δchk + δbind)` (`expected_count_le`). Two instances:
`Selvage/AuditFlashProve.lean` (FlashProve's `cp_verify`; `δchk` from FlashProve's soundness bound
under a transport hypothesis) and `Selvage/AuditExact.lean` (an exact recompute of gptoss-int v0;
`δchk = 0` under a transport hypothesis about the recompute).

**Prior art.** The commit-then-audit statement is Rinberg et al. (arXiv 2511.02620), eprint
2026/541 and covert security (Aumann–Lindell). What is here is the machine-checked composition.

The bad event is read on the SAMPLED RUN (`BadPath`: at some round of this run, live and corrupt,
the audit fired and the verdict was `accept`); off it the run is the run of the `ideal` comparison
round (`agree_ideal`), which alarms on every fired corrupt round and meets the sequential bound;
on it the count is at most the horizon. (Codex round 1, initiative 8, refuted an earlier form whose
bad event ranged over every history.) Binding enters through a named collision extractor (`hext`,
the `cert_and_of_collisionExtractor` form of `Selvage/BindingFixedHash.lean`), not an adversary
class. The coin of each round is fresh in this model; the deployment owes the freshness.
-/
import Selvage.AuditSampling
import Selvage.BindingBudget
import Selvage.AuditDecideCore

namespace Minidregg.Selvage.AuditChecked

open Finset Minidregg.Selvage Minidregg.Selvage.AuditCore

set_option autoImplicit false

/-! ## 1. The world one oracle draw determines -/

/-- What one draw of the oracle fixes: the prover's whole strategy and the checker's answers.
`served h` is the claim the round served, fixed at commitment, before the round's coin. Everything
handed over at audit time may depend on the coin `ω`: `opened h ω` is the record the files the
auditor obtained open to, and `verdict h ω` the checker's verdict on them, the exported
`auditVerdict` of the instance (which folds in the auditor's own opening check). -/
structure World (Claim Ω : Type) where
  served : List Ω → Claim
  opened : List Ω → Ω → Claim
  isFalse : Claim → Bool
  verdict : List Ω → Ω → Verdict

namespace World

variable {Claim Ω : Type} [DecidableEq Claim]

/-- **The round.** Selection is the exported `fires` on the round's coin; the alarm is `alarmFn`
(the exported `alarm`, or the falsifier `alarmOpen`) of that and the verdict. -/
def round (W : World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64)
    (alarmFn : Bool → Verdict → Bool) : Round Ω where
  corrupt h := W.isFalse (W.served h)
  fires _ ω := fires (coin ω) pNum
  alarms h ω := alarmFn (fires (coin ω) pNum) (W.verdict h ω)
  chkErr h ω := W.verdict h ω == .accept && decide (W.opened h ω = W.served h)
  chkAbort h ω := W.verdict h ω == .noVerdict
  bindBreak h ω := W.verdict h ω == .accept && decide (W.opened h ω ≠ W.served h)

/-- **Fail-closed, proved for the exported `alarm`.** -/
theorem round_failClosed (W : World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64) :
    Round.FailClosed (W.round coin pNum alarm) := by
  intro h ω hf hab
  simp only [round, alarm] at *
  simp only [beq_iff_eq] at hab
  simp [hf, hab]

/-- The miss decomposition, from fail-closedness via the landed `missDecomp_of_failClosed`: a
fired corrupt round that does not alarm was accepted, with the served record (a checker error) or
another one (a binding break). -/
theorem round_missDecomp (W : World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64) :
    Round.MissDecomp (W.round coin pNum alarm) := by
  refine Round.missDecomp_of_failClosed (round_failClosed W coin pNum) ?_
  intro h ω _ hf _ hno
  simp only [round, alarm] at hf hno ⊢
  rw [hf] at hno
  have hacc : W.verdict h ω = .accept := by
    cases hv : W.verdict h ω <;> simp_all
  by_cases heq : W.opened h ω = W.served h
  · left; simp [hacc, heq]
  · right; simp [hacc, heq]

/-- **The comparison round**: the same process, except that every fired audit of a corrupt round
alarms. It is what the real round is on runs where the checker and the binding never fail. -/
def ideal (W : World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64) : Round Ω :=
  { W.round coin pNum alarm with
    alarms := fun h ω => alarm (fires (coin ω) pNum) (W.verdict h ω)
      || (W.isFalse (W.served h) && fires (coin ω) pNum) }

/-- The run-level bad event at one round: live, corrupt, fired, accepted. -/
def BadAt (W : World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64) (h : List Ω) (ω : Ω) : Prop :=
  (W.round coin pNum alarm).stopped h = false ∧ W.isFalse (W.served h) = true ∧
    fires (coin ω) pNum = true ∧ W.verdict h ω = .accept

/-- **The bad event on the sampled run**: some round of THIS run was live, corrupt, fired and
accepted. Histories are most recent first, so this reads every round of `h` once. -/
def BadPath (W : World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64) : List Ω → Prop
  | [] => False
  | ω :: h => BadPath W coin pNum h ∨ BadAt W coin pNum h ω

/-- Off the bad event the real run IS the ideal run: same stops, same count. -/
theorem agree_ideal (W : World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64) :
    ∀ h, ¬ BadPath W coin pNum h →
      (W.round coin pNum alarm).stopped h = (W.ideal coin pNum).stopped h ∧
      (W.round coin pNum alarm).count h = (W.ideal coin pNum).count h
  | [] => fun _ => ⟨rfl, rfl⟩
  | ω :: h => by
    intro hb
    simp only [BadPath, not_or] at hb
    obtain ⟨hs, hc⟩ := agree_ideal W coin pNum h hb.1
    have hcorr : (W.ideal coin pNum).corrupt h = (W.round coin pNum alarm).corrupt h := rfl
    have halarm : (W.round coin pNum alarm).stopped h = false →
        (W.round coin pNum alarm).alarms h ω = (W.ideal coin pNum).alarms h ω := by
      intro hlive
      show alarm _ _ = (alarm _ _ || _)
      by_cases hf : fires (coin ω) pNum = true
      · by_cases hcr : W.isFalse (W.served h) = true
        · have hv : W.verdict h ω ≠ .accept := fun hv => hb.2 ⟨hlive, hcr, hf, hv⟩
          simp [alarm, hf, hcr, hv]
        · simp [hcr]
      · simp [hf, alarm]
    refine ⟨?_, ?_⟩
    · simp only [Round.stopped]
      rw [← hs]
      cases hst : (W.round coin pNum alarm).stopped h
      · rw [halarm hst]
      · rfl
    · simp only [Round.count]
      rw [← hs, hc, hcorr]

/-- On the ideal round a live corrupt round alarms at least at the fire rate. -/
theorem ideal_detect [Fintype Ω] (W : World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64) {q : ℝ}
    (hbeacon : q ≤ uniformProb Ω (fun ω => fires (coin ω) pNum = true)) :
    ∀ h, (W.ideal coin pNum).stopped h = false → (W.ideal coin pNum).corrupt h = true →
      q ≤ uniformProb Ω (fun ω => (W.ideal coin pNum).alarms h ω = true) := by
  intro h _ hc
  refine le_trans hbeacon (uniformProb_mono fun ω hf => ?_)
  have hc' : W.isFalse (W.served h) = true := hc
  show (alarm _ _ || _) = true
  simp [hc', hf]

end World

/-! ## 2. The count never exceeds the horizon -/

theorem count_le_length {Ω : Type} (R : Round Ω) : ∀ h : List Ω, R.count h ≤ h.length
  | [] => by simp [Round.count]
  | _ :: h => by
    have ih := count_le_length R h
    simp only [Round.count, List.length_cons]
    split_ifs <;> omega

theorem expOver_add {Ω : Type} [Fintype Ω] (f g : List Ω → ℝ) :
    ∀ (n : ℕ) (h : List Ω),
      expOver Ω n (fun x => f x + g x) h = expOver Ω n f h + expOver Ω n g h := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    rw [expOver.succ, expOver.succ, expOver.succ]
    simp only [ih]
    rw [Finset.sum_add_distrib, add_div]

/-! ## 3. The composed theorem -/

section Composed

variable {Orc Claim Ω Witness : Type} [Fintype Orc] [Nonempty Orc] [Fintype Ω] [Nonempty Ω]
  [DecidableEq Claim]

/-- The checker-bad event on the run: a live corrupt fired round accepted WITH its served record.
-/
def ChkBadPath (W : World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64) : List Ω → Prop
  | [] => False
  | ω :: h => ChkBadPath W coin pNum h ∨ (World.BadAt W coin pNum h ω ∧ W.opened h ω = W.served h)

/-- The binding-bad event on the run: a live corrupt fired round accepted with ANOTHER record. -/
def BindBadPath (W : World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64) : List Ω → Prop
  | [] => False
  | ω :: h => BindBadPath W coin pNum h ∨ (World.BadAt W coin pNum h ω ∧ W.opened h ω ≠ W.served h)

omit [Fintype Ω] [Nonempty Ω] in
theorem badPath_split (W : World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64) :
    ∀ h, World.BadPath W coin pNum h → ChkBadPath W coin pNum h ∨ BindBadPath W coin pNum h
  | [] => fun h => h.elim
  | ω :: h => by
    intro hb
    rcases hb with hb | hb
    · rcases badPath_split W coin pNum h hb with hc | hc
      · exact Or.inl (Or.inl hc)
      · exact Or.inr (Or.inl hc)
    · by_cases heq : W.opened h ω = W.served h
      · exact Or.inl (Or.inr ⟨hb, heq⟩)
      · exact Or.inr (Or.inr ⟨hb, heq⟩)

/-- `Pr` over the run at horizon `n`, as `expOver` of an indicator. -/
noncomputable def runProb (n : ℕ) (P : List Ω → Prop) : ℝ :=
  by classical exact expOver Ω n (fun h => if P h then 1 else 0) []

/-- **THE COMPOSED BOUND.** Draw the oracle `o` once; run `n` rounds with fresh coins. The
expected number of corrupt rounds before the first alarm, averaged over the oracle, is at most
`1/(p − εb) + n·(δchk + δbind)`, where

* `hbeacon`: each fresh coin fires with probability at least `p − εb` (`beacon_ideal` discharges
  it with `εb = 0` for a uniform 64-bit coin);
* `hsnd`: averaged over the oracle, the run accepts a false claim with its served record with
  probability at most `δchk` (the instance names what discharges it);
* `hext`: a run that accepted another record makes the named reduction output a collision
  (`Coll`), and `δbind` is the averaged probability of that.

The proof runs the landed `leakage_with_global_binding` per oracle against the `ideal` round, then
averages. -/
theorem expected_count_le (W : Orc → World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64)
    {q δchk : ℝ} (hq : 0 < q)
    (hbeacon : q ≤ uniformProb Ω (fun ω => fires (coin ω) pNum = true))
    (n : ℕ)
    (hsnd : (∑ o : Orc, runProb n (ChkBadPath (W o) coin pNum)) / (Fintype.card Orc : ℝ) ≤ δchk)
    (Coll : Orc → List Ω → Prop)
    (hext : ∀ o h, BindBadPath (W o) coin pNum h → Coll o h) :
    (∑ o : Orc, expOver Ω n (fun h => ((W o).round coin pNum alarm |>.count h : ℝ)) [])
        / (Fintype.card Orc : ℝ)
      ≤ 1 / q + n * (δchk + (∑ o : Orc, runProb n (Coll o)) / (Fintype.card Orc : ℝ)) := by
  classical
  have hcard : (0 : ℝ) < (Fintype.card Orc : ℝ) := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- per oracle
  have hper : ∀ o, expOver Ω n (fun h => ((W o).round coin pNum alarm |>.count h : ℝ)) []
      ≤ 1 / q + n * (runProb n (ChkBadPath (W o) coin pNum) + runProb n (Coll o)) := by
    intro o
    have hbadle : expOver Ω n (fun h => if World.BadPath (W o) coin pNum h then (1 : ℝ) else 0) []
        ≤ runProb n (ChkBadPath (W o) coin pNum) + runProb n (Coll o) := by
      unfold runProb
      rw [← expOver_add]
      refine expOver.mono (fun h => ?_) n []
      by_cases hb : World.BadPath (W o) coin pNum h
      · rcases badPath_split (W o) coin pNum h hb with hc | hc
        · have := hext o h
          by_cases hcl : Coll o h <;> simp [hb, hc, hcl]
        · simp [hb, hext o h hc]
          split_ifs <;> norm_num
      · simp only [hb, ite_false]
        split_ifs <;> norm_num
    have := ComputationalBinding.leakage_with_global_binding ((W o).ideal coin pNum)
      (fun h => ((W o).round coin pNum alarm |>.count h : ℝ)) (World.BadPath (W o) coin pNum) n
      1 q n _ hq zero_le_one ((W o).ideal_detect coin pNum hbeacon) hn
      (fun h _ hb => by
        rw [((W o).agree_ideal coin pNum h hb).2, one_mul])
      (fun h hl _ => by
        have := count_le_length ((W o).round coin pNum alarm) h
        rw [hl] at this; exact_mod_cast this)
      le_rfl
    calc _ ≤ 1 / q + n * expOver Ω n
            (fun h => if World.BadPath (W o) coin pNum h then (1 : ℝ) else 0) [] := this
      _ ≤ _ := by gcongr
  have hsum := Finset.sum_le_sum fun o (_ : o ∈ Finset.univ) => hper o
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  rw [div_le_iff₀ hcard]
  have h1 : (∑ o : Orc, runProb n (ChkBadPath (W o) coin pNum)) ≤ δchk * (Fintype.card Orc : ℝ) :=
    (div_le_iff₀ hcard).mp hsnd
  have h2 : (∑ o : Orc, runProb n (Coll o))
      = ((∑ o : Orc, runProb n (Coll o)) / (Fintype.card Orc : ℝ)) * (Fintype.card Orc : ℝ) := by
    field_simp
  nlinarith

end Composed

/-! ## 4. The ideal beacon: the fire rate is exactly `pNum / 2^64` -/

/-- A uniform 64-bit coin, as `Fin (2^64)`. -/
def coin64 (ω : Fin (2 ^ 64)) : UInt64 := UInt64.ofNat ω.val

theorem fires_coin64_iff (ω : Fin (2 ^ 64)) (pNum : UInt64) :
    fires (coin64 ω) pNum = true ↔ ω.val < pNum.toNat := by
  have hlt : ω.val < 2 ^ 64 := ω.isLt
  simp [fires, coin64, UInt64.lt_iff_toNat_lt]

/-- **The ideal beacon's fire rate.** -/
theorem beacon_ideal (pNum : UInt64) :
    uniformProb (Fin (2 ^ 64)) (fun ω => fires (coin64 ω) pNum = true)
      = (pNum.toNat : ℝ) / 2 ^ 64 := by
  classical
  rw [uniformProb_congr (fires_coin64_iff · pNum)]
  unfold uniformProb
  have hle : pNum.toNat ≤ 2 ^ 64 := le_of_lt pNum.toNat_lt
  have hc : Nat.card {ω : Fin (2 ^ 64) // ω.val < pNum.toNat} = pNum.toNat := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [show (Finset.univ.filter fun ω : Fin (2 ^ 64) => ω.val < pNum.toNat)
        = (Finset.range pNum.toNat).attachFin (fun m hm => lt_of_lt_of_le (Finset.mem_range.mp hm) hle) from by
      ext ω; simp]
    simp
  rw [hc, Fintype.card_fin]
  push_cast
  ring

/-- The three nominal rates, as `⌊p · 2^64⌋`. -/
def pNum001 : UInt64 := 184467440737095516
def pNum005 : UInt64 := 922337203685477580
def pNum020 : UInt64 := 3689348814741910323

#guard pNum001.toNat = 18446744073709551616 / 100
#guard pNum005.toNat = 18446744073709551616 / 20
#guard pNum020.toNat = 18446744073709551616 / 5

/-! ## Axioms -/

/-- info: 'Minidregg.Selvage.AuditChecked.expected_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms expected_count_le
/-- info: 'Minidregg.Selvage.AuditChecked.World.round_failClosed' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms World.round_failClosed
/-- info: 'Minidregg.Selvage.AuditChecked.World.round_missDecomp' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms World.round_missDecomp
/-- info: 'Minidregg.Selvage.AuditChecked.World.agree_ideal' depends on axioms: [propext] -/
#guard_msgs (whitespace := lax) in #print axioms World.agree_ideal
/-- info: 'Minidregg.Selvage.AuditChecked.World.ideal_detect' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms World.ideal_detect
/-- info: 'Minidregg.Selvage.AuditChecked.beacon_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms beacon_ideal

end Minidregg.Selvage.AuditChecked
