/-
# Selvage.AuditFlashProve — the commit-then-audit theorem instantiated over FlashProve's verifier

`Selvage/AuditChecked.lean` proves the composed commit-then-audit bound for any checker whose
verdict is a function of the history and the round's coin. This file is its instance over
FlashProve: the verdict is the compiled, exported `auditVerdict` of
`Selvage/AuditFlashProveDecide.lean` on one `cp_verify` call, selection and alarm the exported
`fires` and `alarm` of `Selvage/AuditDecideCore.lean`, the functions the Rust auditor
`breadstuffs/audit-flashprove` calls; the bound is composed with
FlashProve's own soundness bound (`lean/Ladder/Bits.lean`, `soundnessErrorInQueries`, behind
`sound_of_verify_at` in FlashProve's `lean/THEOREM.md`).

**Prior art.** The commit-then-audit statement is not new: Rinberg et al. (arXiv 2511.02620),
eprint 2026/541 and covert security (Aumann–Lindell) state it. What is here is an instance of the
machine-checked composition over a real proof system's shipped verifier.

## The bar (initiative 8, the five corrections accepted 2026-11-06)

1. **ε_chk is an execution-level bad event, not a per-round `εchk`.** FlashProve's bound is over
   ONE random oracle shared by every round, and a total budget `Q` of hash queries. `ChkLeg` wants
   checker coins fresh each round and independent of the beacon (`chkLeg_of_product`; residual
   "fresh coins" of `AuditSampling` §8). A fixed hash is neither. So the oracle `o : Orc` is drawn
   once, and the bad event is read on the SAMPLED RUN: `BadPath` says that at some round of this
   run, live and corrupt, the audit fired and the verdict was `accept`. Off that event the run is
   the run of the `ideal` comparison round (`count_eq_ideal`), which alarms on every fired corrupt
   round and so meets the sequential bound at `1/q₀`; on it the count is at most the horizon `n`.
   Averaged: `E[C_{τ∧n}] ≤ 1/q₀ + n·(δchk + δbind)` (`expected_count_le`, through the landed
   `ComputationalBinding.leakage_with_global_binding`). The horizon appears; that is the honest
   price of a shared oracle. (Codex round 1 refuted an earlier form whose bad event ranged over
   every history, counterfactual branches included.) It is the shape of `ComputationalBinding.leakage_of_global_game`
   (`Selvage/BindingBudget.lean`, `b/q + M·ε`), with two differences: the bad event lives on a
   separately drawn oracle, not on the run's own coins, and binding enters through a named
   extractor rather than that theorem's `SecureAt`, which `BindingFixedHash` shows vacuous at a
   fixed hash.
2. **Their bound is about the Lean `verify`, not `cp_verify`.** `δchk` enters as the hypothesis
   `hsnd`, named **[FP-chk-transport]**: averaged over the oracle and the run's coins, the
   probability that some live corrupt fired round of the run is accepted with its committed
   record is at most `δchk`. What discharging it needs, none of which is proved here: the public
   files fixed before the oracle is drawn; `isFalse` equal to FlashProve's falsity (not the
   model's output at the extracted weights); `cp_verify` accepting only where `verify` accepts
   (no theorem: their `lean/LIMITS.md`, L9, L53); and a reduction from the n-round run to ONE
   `Sound` game: run the whole audit, output the first accepted false claim. That reduction makes
   the auditor's own verifications part of the adversary, so the value is
   `fpSoundErr (Q + n·(2^23 + 1))`, not `fpSoundErr Q`, and the damage term stays `n·δ`, not the
   `n²·δ` a per-round union bound would give. `fpSoundErr` is a transcription of their
   definition; nothing imports it. The `lean-verify` cross-check is evidence, not a discharge.
   Like every random-oracle bound, the average over `Orc` says nothing about one deployed hash.
3. **Exact match only.** Their theorem asks for exact match; `verdictOf` accepts only `YES` with
   `policy=exact-match` and `sh=8`. At a clipped-gap policy no bound of this strength exists, the
   honest `δchk` is 1, and `expected_count_le` says nothing, which is the right verdict.
4. **Fail-closed on every non-accept.** The opening, the files and the verdict may depend on the
   current round's coin (`World.opened`, `World.call` read `ω`): only the served claim is fixed
   before the beacon. `alarm` raises on `reject` and `noVerdict` alike: exit 1,
   any other exit code, a timeout, a kill, a missing proof, a hostile file. `round_failClosed` is
   proved, and `FailOpen.collapse` shows the fail-open `alarmOpen` lets an adversary that withholds
   proofs run every round uncaught, at every horizon, against the same beacon.
5. **The beacon round is anchored by the requester.** The coin of position `t` is
   `BLAKE3(drand signature of round (seen_t + 2) ‖ position)`, where `seen_t` is the latest drand
   round named in the requester's countersigned commitment. In this file the coin space is
   abstract and each round's coin is FRESH (the `expOver` model); `beacon_ideal` proves the fire
   rate exactly `pNum/2^64` for a uniform 64-bit coin, and the general theorem carries `εbeacon`
   as the hypothesis `hbeacon` on that fresh coin. The deployment owes the freshness: a coin
   reused across rounds meets the marginal rate and breaks the theorem (codex round 1: one coin
   forever gives `p + (1−p)n` against an always-corrupt prover); the position inside the hash and
   the `seen + 2` round are what make each round's coin unseen at commitment. What `εbeacon` must absorb —
   drand's threshold honesty, the requester's honesty about the round it saw, BLAKE3 as a random
   function — is an assumption, not a number this file computes.

## What the binding term is

`δbind` is the probability that ONE named deterministic reduction outputs a collision (BLAKE3 in
the MMR, or SHA-256 between the files and the record): `hext` says that whenever a fired audit of a
live corrupt round ACCEPTED an opening (so the auditor's `openOk` check passed: the files hash to a
record that opens at the position under the root) that is not the served record, `reduce` of the
run is a collision. A garbage opening is not charged here; it fails `openOk`, and
`auditVerdict` rejects it. That is the `cert_and_of_collisionExtractor` form of
`Selvage/BindingFixedHash.lean`; no adversary class is quantified, so the term is not vacuous at a
fixed hash. Its value is a human-ignorance bound, not a theorem.
-/
import Selvage.AuditChecked
import Selvage.AuditFlashProveDecide

namespace Minidregg.Selvage.AuditFlashProve

open Finset Minidregg.Selvage Minidregg.Selvage.AuditCore
open Minidregg.Selvage.AuditChecked (runProb coin64 beacon_ideal pNum001 pNum005 pNum020
  expected_count_le)

set_option autoImplicit false

/-! ## 1. The world one oracle draw determines -/

/-- What one draw of the oracle fixes: the prover's whole strategy and the checker's answers.
`served h` is the claim the round served, fixed at commitment, before the round's coin. Everything
handed over at audit time may depend on the coin `ω`: `opened h ω` is the record the files the
auditor obtained open to, `openOk h ω` the auditor's own check that they open under the root at
the position and hash to that record, `call h ω` the `cp_verify` call on them. `expect h` is what
the auditor holds (ID, build, `r`, `e`). -/
structure World (Claim Ω : Type) where
  served : List Ω → Claim
  opened : List Ω → Ω → Claim
  openOk : List Ω → Ω → Bool
  isFalse : Claim → Bool
  call : List Ω → Ω → String × Option UInt32
  expect : List Ω → Expect

namespace World

variable {Claim Ω : Type}

/-- The verdict: the exported `auditVerdict`. -/
def verdict (W : World Claim Ω) (h : List Ω) (ω : Ω) : Verdict :=
  auditVerdict (W.openOk h ω) (W.call h ω).1 (W.call h ω).2 (W.expect h)

/-- The checked world `Selvage/AuditChecked.lean` runs: every theorem there (`round_failClosed`,
`agree_ideal`, `expected_count_le`) applies to `W.toC`. -/
def toC (W : World Claim Ω) : AuditChecked.World Claim Ω :=
  { served := W.served, opened := W.opened, isFalse := W.isFalse, verdict := W.verdict }

end World

/-! ## 5. The numbers -/

/-- FlashProve's soundness error at `Q` adversary queries and one parser query, transcribed from
`lean/Ladder/Bits.lean:96` of FlashProve 9e2bdd8f (`soundnessErrorInQueries Q 1`, with
`errorFactorPerQuery = 16` and `verifierQueryAllowance = 2^23`), as a rational. -/
def fpSoundErr (Q : ℕ) : ℚ :=
  (16 * (Q + 1 + 2 ^ 23) : ℕ) / 2 ^ 128 + ((Q + 1 + 2 ^ 23 + 2) ^ 2 : ℕ) / 2 ^ 256

/-- At `Q = 2^64` the bound is below `2^-59`. -/
theorem fpSoundErr_2_64 : fpSoundErr (2 ^ 64) < 1 / 2 ^ 59 := by
  unfold fpSoundErr; norm_num

/-- With nothing queried it is above `2^-102`: the floor is real. -/
theorem fpSoundErr_zero_floor : 1 / 2 ^ 102 < fpSoundErr 0 := by
  unfold fpSoundErr; norm_num

/-- The query budget the run-to-one-game reduction spends: the adversary's `Q`, plus, for each of
the `n` rounds, the verifier's own allowance and the parser's query. -/
def reductionQueries (Q n : ℕ) : ℕ := Q + n * (2 ^ 23 + 1)

/-- At `Q = 2^64` and a horizon of `2^20` rounds the reduction's bound is still below `2^-59`. -/
theorem fpSoundErr_reduction : fpSoundErr (reductionQueries (2 ^ 64) (2 ^ 20)) < 1 / 2 ^ 59 := by
  unfold fpSoundErr reductionQueries; norm_num

/-- **The instance at `p = 0.01`, the ideal beacon.** Expected corrupt rounds before the first
alarm, at horizon `n`, at most `2^64/⌊0.01·2^64⌋ + n·(fpSoundErr (Q + n·(2^23+1)) + δbind)`, under
**[FP-chk-transport]** (`hsnd`, at the reduction's query count) and the collision extractor. -/
theorem flashprove_p001 {Orc Claim : Type} [Fintype Orc] [Nonempty Orc] [DecidableEq Claim]
    (W : Orc → World Claim (Fin (2 ^ 64))) (Q n : ℕ)
    (hsnd : (∑ o : Orc, runProb n (AuditChecked.ChkBadPath (W o).toC coin64 pNum001))
      / (Fintype.card Orc : ℝ)
      ≤ (fpSoundErr (reductionQueries Q n) : ℝ))
    (Coll : Orc → List (Fin (2 ^ 64)) → Prop)
    (hext : ∀ o h, AuditChecked.BindBadPath (W o).toC coin64 pNum001 h → Coll o h) :
    (∑ o : Orc, expOver (Fin (2 ^ 64)) n
        (fun h => ((W o).toC.round coin64 pNum001 alarm |>.count h : ℝ)) []) / (Fintype.card Orc : ℝ)
      ≤ 1 / ((pNum001.toNat : ℝ) / 2 ^ 64)
        + n * ((fpSoundErr (reductionQueries Q n) : ℝ)
          + (∑ o : Orc, runProb n (Coll o)) / (Fintype.card Orc : ℝ)) := by
  have hp : (0 : ℝ) < (pNum001.toNat : ℝ) / 2 ^ 64 := by
    apply div_pos _ (by norm_num); exact_mod_cast (by decide : 0 < pNum001.toNat)
  exact expected_count_le (fun o => (W o).toC) coin64 pNum001 hp (by rw [beacon_ideal]) n hsnd Coll hext

/-! ## 6. Teeth -/

namespace Teeth

/-- A claim is a Boolean: `true` is false (the served reply is not the model's). -/
abbrev Claim := Bool

private def yes : String × Option UInt32 :=
  ("covered: r=60 e=64 tokens=61..63 y=yes policy=exact-match sh=8\n" ++
   "result-v1 status=0 claim=exact-match id=A r=60 e=64 y=yes policy=exact-match build=B\nYES\n", some 0)

private def ex : Expect := { id := "A", build := "B", r := 60, e := 64, acceptWork := true }

#guard auditVerdict true yes.1 yes.2 ex == .accept

/-- An always-corrupt prover against a checker that rejects (exit 1). -/
def honestChecker : World Claim (Fin (2 ^ 64)) where
  served _ := true
  opened _ _ := true
  openOk _ _ := true
  isFalse c := c
  call _ _ := ("NO: reply-differs\n", some 1)
  expect _ := ex

theorem honestChecker_verdict (h : List (Fin (2 ^ 64))) (ω : Fin (2 ^ 64)) :
    honestChecker.toC.verdict h ω = .reject := rfl

/-- Its run never meets the bad event: `hsnd` and `hext` hold at `δchk = δbind = 0`, so the
hypotheses of `expected_count_le` are inhabited. -/
theorem honestChecker_noBad (coin : Fin (2 ^ 64) → UInt64) (pNum : UInt64) :
    ∀ h, ¬ AuditChecked.World.BadPath honestChecker.toC coin pNum h
  | [] => id
  | ω :: h => by
    rintro (hb | ⟨_, _, _, hv⟩)
    · exact honestChecker_noBad coin pNum h hb
    · rw [honestChecker_verdict] at hv; cases hv

/-- A prover whose files fail the auditor's opening check is rejected whatever `cp_verify` says:
a garbage opening is an alarm, never a binding charge. -/
def badOpening : World Claim (Fin (2 ^ 64)) :=
  { honestChecker with openOk := fun _ _ => false, call := fun _ _ => yes }

theorem badOpening_rejects (h : List (Fin (2 ^ 64))) (ω : Fin (2 ^ 64)) :
    badOpening.toC.verdict h ω = .reject := rfl

/-- A checker that ACCEPTS the false claim (its opening checks out and `cp_verify` prints the
accepting transcript): the bad event has content. A fact about concrete strings, so it is checked
by compiled evaluation (`native_decide`; in this toolchain each use is its own `…native_decide.ax` axiom, pinned below in place of `Lean.ofReduceBool`), per the house policy
for concrete data; the general theorems above stay kernel-proved. -/
def acceptingChecker : World Claim (Fin (2 ^ 64)) := { honestChecker with call := fun _ _ => yes }

theorem acceptingChecker_verdict : acceptingChecker.toC.verdict [] 0 = .accept := by native_decide

/-- Its first round, fired at any positive rate, is live, corrupt and accepted: `BadAt`. -/
theorem acceptingChecker_badAt :
    AuditChecked.World.BadAt acceptingChecker.toC coin64 pNum020 [] (0 : Fin (2 ^ 64)) :=
  ⟨rfl, rfl, by native_decide, acceptingChecker_verdict⟩

/-- **The withholding prover**: always corrupt, its opening checks out, it hands no proof, and
`cp_verify` ends with no exit status of its own. -/
def withholder : World Claim (Fin (2 ^ 64)) :=
  { honestChecker with call := fun _ _ => ("", none) }

theorem withholder_verdict (h : List (Fin (2 ^ 64))) (ω : Fin (2 ^ 64)) :
    withholder.toC.verdict h ω = .noVerdict := rfl

/-- **FAIL-OPEN COLLAPSES.** Under `alarmOpen` the withholder is never caught: the expected
corrupt count at horizon `n` is exactly `n`, for every `n` and every rate `pNum`. -/
theorem FailOpen.collapse (pNum : UInt64) (n : ℕ) :
    expOver (Fin (2 ^ 64)) n (fun h => ((withholder.toC.round coin64 pNum alarmOpen).count h : ℝ)) []
      = n := by
  have halarm : ∀ h ω, (withholder.toC.round coin64 pNum alarmOpen).alarms h ω = false := by
    intro h ω
    show alarmOpen _ (withholder.toC.verdict h ω) = false
    rw [withholder_verdict]; simp [alarmOpen]
  have hstop : ∀ h : List (Fin (2 ^ 64)),
      (withholder.toC.round coin64 pNum alarmOpen).stopped h = false := by
    intro h; induction h with
    | nil => rfl
    | cons ω h ih => simp [Round.stopped, ih, halarm]
  have hcount : ∀ h : List (Fin (2 ^ 64)),
      (withholder.toC.round coin64 pNum alarmOpen).count h = h.length := by
    intro h; induction h with
    | nil => rfl
    | cons ω h ih =>
      have hc : (withholder.toC.round coin64 pNum alarmOpen).corrupt h = true := rfl
      simp [Round.count, hstop h, ih, hc]
  simp only [hcount]
  rw [expOver.length]; simp

/-- The fail-open round is `FailOpen` in `AuditSampling`'s sense. -/
theorem withholder_failOpen (pNum : UInt64) :
    Round.FailOpen (withholder.toC.round coin64 pNum alarmOpen) := by
  intro h ω _
  show alarmOpen _ (withholder.toC.verdict h ω) = false
  rw [withholder_verdict]; simp [alarmOpen]

/-- **Fail-closed meets the same prover at no cost**: its run never meets the bad event, so
`expected_count_le` bounds it at `1/p` with `δchk = δbind = 0`. -/
theorem withholder_noBad (pNum : UInt64) :
    ∀ h, ¬ AuditChecked.World.BadPath withholder.toC coin64 pNum h
  | [] => id
  | ω :: h => by
    rintro (hb | ⟨_, _, _, hv⟩)
    · exact withholder_noBad pNum h hb
    · rw [withholder_verdict] at hv; cases hv

/-- At `p = 0.2` the fail-open count passes the fail-closed bound `1/p = 5` at horizon 6. -/
theorem failOpen_beats_bound :
    1 / ((pNum020.toNat : ℝ) / 2 ^ 64) <
      expOver (Fin (2 ^ 64)) 6 (fun h => ((withholder.toC.round coin64 pNum020 alarmOpen).count h : ℝ)) [] := by
  rw [FailOpen.collapse]
  have : (pNum020.toNat : ℝ) = 3689348814741910323 := by norm_cast
  rw [this]; norm_num

end Teeth

/-! ## Axioms -/

/-- info: 'Minidregg.Selvage.AuditFlashProve.flashprove_p001' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms flashprove_p001
/-- info: 'Minidregg.Selvage.AuditFlashProve.fpSoundErr_2_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fpSoundErr_2_64
/-- info: 'Minidregg.Selvage.AuditFlashProve.Teeth.acceptingChecker_badAt' depends on axioms: [propext, Classical.choice, Quot.sound, Teeth.acceptingChecker_badAt._native.native_decide.ax_1_1, Teeth.acceptingChecker_verdict._native.native_decide.ax_1_1] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.acceptingChecker_badAt
/-- info: 'Minidregg.Selvage.AuditFlashProve.fpSoundErr_zero_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fpSoundErr_zero_floor
/-- info: 'Minidregg.Selvage.AuditFlashProve.fpSoundErr_reduction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fpSoundErr_reduction
/-- info: 'Minidregg.Selvage.AuditFlashProve.Teeth.FailOpen.collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.FailOpen.collapse
/-- info: 'Minidregg.Selvage.AuditFlashProve.Teeth.failOpen_beats_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.failOpen_beats_bound
/-- info: 'Minidregg.Selvage.AuditFlashProve.Teeth.withholder_failOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.withholder_failOpen
/-- info: 'Minidregg.Selvage.AuditFlashProve.Teeth.withholder_noBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.withholder_noBad
/-- info: 'Minidregg.Selvage.AuditFlashProve.Teeth.honestChecker_noBad' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.honestChecker_noBad

end Minidregg.Selvage.AuditFlashProve
