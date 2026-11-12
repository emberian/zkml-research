/-
# Selvage.AuditExact — the commit-then-audit theorem over an exact recompute of gpt-oss-20b

The instance of `Selvage/AuditChecked.lean` whose checker recomputes a committed transcript with
gptoss-int v0 (the integer gpt-oss-20b of `zkml-research/research/exact_recompute_2026_11_06`) and
whose verdict is the exported `auditVerdict` of `Selvage/AuditExactDecide.lean`.

A claim is a request's prompt and its committed output tokens. It is false when the output is not
the integer model's greedy continuation: `M c ≠ c.output`, where `M c` is the spec's argmax list
teacher-forced over `c` (an abstract function here; the spec is the Python reference, digested in
the `pins` line). There is no random oracle and no soundness error: the recompute is
deterministic, so `δchk = 0` (`no_chkBad`, `exact_bound`), under one named hypothesis,

**[EX-transport]** (`Transport`): whenever the recompute reports an argmax list for the opened
claim, the list is `M` of that claim. The recompute may fail, time out or print garbage (that is
`noVerdict`, and fail-closed alarms on it); it may not report a wrong list. What stands behind it is
evidence, not proof: the same integers from two independent kernels (float64 BLAS on 20-bit limbs;
int8 x int8 -> int32 dots) on three machines (Apple CPU, XLA:CPU, a Tesla T4 through cublasLt),
digest-equal at every intermediate of layer 0. `Teeth.lyingRecompute` shows the hypothesis
carries the theorem: a recompute that reports the committed tokens accepts a false transcript.
-/
import Selvage.AuditChecked
import Selvage.AuditExactDecide

namespace Minidregg.Selvage.AuditExact

open Finset Minidregg.Selvage Minidregg.Selvage.AuditCore
open Minidregg.Selvage.AuditChecked (runProb coin64 beacon_ideal pNum001 expected_count_le)

set_option autoImplicit false

/-- A request as committed: the prompt tokens and the output tokens. -/
structure Claim where
  prompt : List Nat
  output : List Nat
  deriving DecidableEq

/-- What one run fixes. `served h` is fixed at commitment; the opened record, the auditor's own
opening check and the recompute's output may depend on the round's coin. `M` is the spec. -/
structure World (Ω : Type) where
  M : Claim → List Nat
  pins : String × String × String
  served : List Ω → Claim
  opened : List Ω → Ω → Claim
  openOk : List Ω → Ω → Bool
  call : List Ω → Ω → String × Option UInt32

namespace World

variable {Ω : Type}

/-- What the auditor compares against: its pins, and the prompt length and output of the record
it opened. -/
def expect (W : World Ω) (h : List Ω) (ω : Ω) : Expect :=
  { spec := W.pins.1, params := W.pins.2.1, weights := W.pins.2.2,
    promptLen := (W.opened h ω).prompt.length, output := (W.opened h ω).output }

/-- The verdict: the exported `auditVerdict`. -/
def verdict (W : World Ω) (h : List Ω) (ω : Ω) : Verdict :=
  auditVerdict (W.openOk h ω) (W.call h ω).1 (W.call h ω).2 (W.expect h ω)

/-- A claim is false when its output is not the spec's argmax list. -/
def isFalse (W : World Ω) (c : Claim) : Bool := decide (W.M c ≠ c.output)

def toC (W : World Ω) : AuditChecked.World Claim Ω :=
  { served := W.served, opened := W.opened, isFalse := W.isFalse, verdict := W.verdict }

/-- **[EX-transport].** On a call whose files opened and which exited 0, a report, when there is
one, is the spec's argmax list of the opened claim. Nothing is asked of calls that failed or of
openings that did not check out (codex round 3: the first form quantified over every call). An
always-failing recompute satisfies it, and buys no availability: fail-closed alarms on it. -/
def Transport (W : World Ω) : Prop :=
  ∀ h ω ts, W.openOk h ω = true → (W.call h ω).2 = some 0 →
    reported (W.call h ω).1 (W.expect h ω) = some ts → ts = W.M (W.opened h ω)

/-- **An accept means the files opened, the recompute exited 0, and it reported exactly the
committed output.** -/
theorem accept_reported (W : World Ω) (h : List Ω) (ω : Ω) (hv : W.verdict h ω = .accept) :
    W.openOk h ω = true ∧ (W.call h ω).2 = some 0 ∧
      reported (W.call h ω).1 (W.expect h ω) = some (W.opened h ω).output := by
  unfold verdict auditVerdict at hv
  by_cases hok : W.openOk h ω = true
  · simp only [hok, if_true] at hv
    unfold verdictOf at hv
    split at hv
    · rename_i hx
      split at hv
      · rename_i ts hr
        split_ifs at hv with heq
        have : ts = (W.expect h ω).output := by simpa using heq
        exact ⟨hok, hx, by rw [hr, this]; rfl⟩
      · cases hv
    · cases hv
  · simp [hok] at hv

/-- **No false transcript is accepted with its committed record.** Under [EX-transport] an
accepted opening's output is the spec's argmax list, so the opened claim is true; if it is the
served one, the served claim is true. -/
theorem no_chkBad (W : World Ω) (hT : W.Transport) (coin : Ω → UInt64) (pNum : UInt64) :
    ∀ h, ¬ AuditChecked.ChkBadPath W.toC coin pNum h
  | [] => id
  | ω :: h => by
    rintro (hb | ⟨⟨_, hcr, _, hv⟩, heq⟩)
    · exact no_chkBad W hT coin pNum h hb
    · obtain ⟨hok, hx, hrep⟩ := accept_reported W h ω hv
      have hM := hT h ω _ hok hx hrep
      have heq' : W.opened h ω = W.served h := heq
      have : W.isFalse (W.served h) = false := by
        simp [isFalse, ← heq', ← hM]
      exact absurd hcr (by simp [toC, this])

end World

/-- `Pr` of an event that never happens is `0`. -/
theorem runProb_never {Ω : Type} [Fintype Ω] [Nonempty Ω] (n : ℕ) (P : List Ω → Prop)
    (hP : ∀ h, ¬ P h) : runProb n P = 0 := by
  classical
  unfold runProb
  have : (fun h => if P h then (1 : ℝ) else 0) = fun _ => 0 := by
    funext h; simp [hP h]
  simp only [this]
  exact expOver.const 0 n []

/-- **THE EXACT INSTANCE.** Expected corrupt rounds before the first alarm at horizon `n`, averaged
over whatever the world draw is, at most `1/q + n·δbind`: the checker term is zero. -/
theorem exact_bound {Orc Ω : Type} [Fintype Orc] [Nonempty Orc] [Fintype Ω] [Nonempty Ω]
    (W : Orc → World Ω) (hT : ∀ o, (W o).Transport) (coin : Ω → UInt64) (pNum : UInt64)
    {q : ℝ} (hq : 0 < q) (hbeacon : q ≤ uniformProb Ω (fun ω => fires (coin ω) pNum = true))
    (n : ℕ) (Coll : Orc → List Ω → Prop)
    (hext : ∀ o h, AuditChecked.BindBadPath (W o).toC coin pNum h → Coll o h) :
    (∑ o : Orc, expOver Ω n (fun h => ((W o).toC.round coin pNum alarm |>.count h : ℝ)) [])
        / (Fintype.card Orc : ℝ)
      ≤ 1 / q + n * (0 + (∑ o : Orc, runProb n (Coll o)) / (Fintype.card Orc : ℝ)) := by
  refine expected_count_le (fun o => (W o).toC) coin pNum hq hbeacon n ?_ Coll hext
  have : ∀ o, runProb n (AuditChecked.ChkBadPath (W o).toC coin pNum) = 0 :=
    fun o => runProb_never n _ ((W o).no_chkBad (hT o) coin pNum)
  simp [this]

/-- At `p = 0.01` with the ideal 64-bit beacon. -/
theorem exact_p001 {Orc : Type} [Fintype Orc] [Nonempty Orc]
    (W : Orc → World (Fin (2 ^ 64))) (hT : ∀ o, (W o).Transport) (n : ℕ)
    (Coll : Orc → List (Fin (2 ^ 64)) → Prop)
    (hext : ∀ o h, AuditChecked.BindBadPath (W o).toC coin64 pNum001 h → Coll o h) :
    (∑ o : Orc, expOver (Fin (2 ^ 64)) n
        (fun h => ((W o).toC.round coin64 pNum001 alarm |>.count h : ℝ)) []) / (Fintype.card Orc : ℝ)
      ≤ 1 / ((pNum001.toNat : ℝ) / 2 ^ 64)
        + n * (0 + (∑ o : Orc, runProb n (Coll o)) / (Fintype.card Orc : ℝ)) := by
  have hp : (0 : ℝ) < (pNum001.toNat : ℝ) / 2 ^ 64 := by
    apply div_pos _ (by norm_num); exact_mod_cast (by decide : 0 < pNum001.toNat)
  exact exact_bound W hT coin64 pNum001 hp (by rw [beacon_ideal]) n Coll hext

/-! ## Teeth -/

namespace Teeth

private def dA : String := "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa"
private def report (toks : String) : String × Option UInt32 :=
  (s!"pins spec={dA} params={dA} weights={dA}\nshape prompt=2 output=1\nargmax tokens={toks}\nDONE\n", some 0)

/-- The spec says the next token is 7; the server committed 8: a false claim, every round. -/
def false8 : Claim := ⟨[1, 2], [8]⟩

/-- An honest recompute: it reports the spec's 7. -/
def honest : World (Fin (2 ^ 64)) where
  M _ := [7]
  pins := (dA, dA, dA)
  served _ := false8
  opened _ _ := false8
  openOk _ _ := true
  call _ _ := report "7"

theorem honest_report : reported (report "7").1 (honest.expect [] 0) = some [7] := by native_decide

theorem honest_transport : honest.Transport := by
  intro h ω ts _ _ hr
  have hr' : reported (report "7").1 (honest.expect [] 0) = some ts := hr
  rw [honest_report] at hr'
  cases hr'; rfl

theorem honest_rejects (h : List (Fin (2 ^ 64))) (ω : Fin (2 ^ 64)) :
    honest.toC.verdict h ω = .reject := by
  have : auditVerdict true (report "7").1 (report "7").2 (honest.expect [] 0) = .reject := by
    native_decide
  exact this

/-- **[EX-transport] carries the theorem.** A recompute that reports the committed tokens accepts
the false transcript: the bad event is met on the first fired round. -/
def lyingRecompute : World (Fin (2 ^ 64)) := { honest with call := fun _ _ => report "8" }

theorem lying_accepts : lyingRecompute.toC.verdict [] 0 = .accept := by native_decide

theorem lying_badAt : AuditChecked.World.BadAt lyingRecompute.toC coin64 AuditChecked.pNum020 [] 0 :=
  ⟨rfl, by native_decide, by native_decide, lying_accepts⟩

theorem lying_not_transport : ¬ lyingRecompute.Transport := by
  intro hT
  have hr : reported (report "8").1 (lyingRecompute.expect [] 0) = some [8] := by native_decide
  have := hT [] 0 [8] rfl rfl hr
  simp [lyingRecompute, honest] at this

end Teeth

/-! ## Axioms -/

/-- info: 'Minidregg.Selvage.AuditExact.exact_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exact_bound
/-- info: 'Minidregg.Selvage.AuditExact.exact_p001' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms exact_p001
/-- info: 'Minidregg.Selvage.AuditExact.World.no_chkBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms World.no_chkBad
/-- info: 'Minidregg.Selvage.AuditExact.Teeth.honest_transport' depends on axioms: [propext, Classical.choice, Quot.sound, Teeth.honest_report._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.honest_transport
/-- info: 'Minidregg.Selvage.AuditExact.Teeth.lying_badAt' depends on axioms: [propext, Classical.choice, Quot.sound, Teeth.lying_accepts._native.native_decide.ax_1_1, Teeth.lying_badAt._native.native_decide.ax_1_1, Teeth.lying_badAt._native.native_decide.ax_1_2] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.lying_badAt
/-- info: 'Minidregg.Selvage.AuditExact.Teeth.lying_not_transport' depends on axioms: [propext, Classical.choice, Quot.sound, Teeth.lying_not_transport._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.lying_not_transport

end Minidregg.Selvage.AuditExact
