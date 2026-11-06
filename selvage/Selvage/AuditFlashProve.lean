/-
# Selvage.AuditFlashProve — the commit-then-audit theorem instantiated over FlashProve's verifier

`Selvage/AuditSampling.lean` proves, for an abstract `Round`, that the expected number of corrupt
rounds before the first alarm is at most `1/q`. This file builds the `Round` whose selection,
verdict and alarm are the compiled, exported functions of `Selvage/AuditFlashProveDecide.lean`
(`fires`, `verdictOf`, `alarm`), the functions the Rust auditor `breadstuffs/audit-flashprove`
calls; it proves that `Round` fail-closed and its detection legs, and composes the result with
FlashProve's own soundness bound (`lean/Ladder/Bits.lean`, `soundnessErrorInQueries`, behind
`sound_of_verify_at` in FlashProve's `lean/THEOREM.md`).

**Prior art.** The commit-then-audit statement is not new: Rinberg et al. (arXiv 2511.02620),
eprint 2026/541 and covert security (Aumann–Lindell) state it. What is here is an instance of the
machine-checked composition over a real proof system's shipped verifier.

## The bar (initiative 8, the five corrections accepted 2026-11-06)

1. **ε_chk is a good-oracle event, not a per-round `εchk`.** FlashProve's bound is over ONE
   random oracle shared by every round, and a total budget `Q` of hash queries. `ChkLeg` wants
   checker coins fresh each round and independent of the beacon (`chkLeg_of_product`; residual
   "fresh coins" of `AuditSampling` §8). A fixed hash is neither. So the oracle `o : Orc` is drawn
   once; `Good o` says the checker accepts no false claim and no opened record differs from the
   served one; on `Good o` the round has `εchk = εbind = 0` and the sequential bound gives `1/q₀`;
   off it the count is at most the horizon `n`. Averaging over the oracle:
   `E[C_{τ∧n}] ≤ 1/q₀ + n·(δchk + δbind)` (`expected_count_le`). The horizon appears; that is the
   honest price of a shared oracle. It is the shape of `ComputationalBinding.leakage_of_global_game`
   (`Selvage/BindingBudget.lean`, `b/q + M·ε`), with two differences: the bad event lives on a
   separately drawn oracle, not on the run's own coins, and binding enters through a named
   extractor rather than that theorem's `SecureAt`, which `BindingFixedHash` shows vacuous at a
   fixed hash.
2. **Their bound is about the Lean `verify`, not `cp_verify`.** `δchk` enters as the hypothesis
   `hsnd`, named **[FP-chk-transport]**: the probability over the oracle that `cp_verify`, as the
   auditor runs it, accepts a false claim is at most `fpSoundErr Q`. FlashProve's `sound` proves
   that bound for `verify`; no theorem relates `cp_verify` to `verify` (their `lean/LIMITS.md`,
   L9 and L53). The `lean-verify` cross-check on bb2 is evidence for it, not a discharge.
3. **Exact match only.** Their theorem asks for exact match; `verdictOf` accepts only `YES` with
   `policy=exact-match` and `sh=8`. At a clipped-gap policy no bound of this strength exists, the
   honest `δchk` is 1, and `expected_count_le` says nothing, which is the right verdict.
4. **Fail-closed on every non-accept.** `alarm` raises on `reject` and `noVerdict` alike: exit 1,
   any other exit code, a timeout, a kill, a missing proof, a hostile file. `round_failClosed` is
   proved, and `FailOpen.collapse` shows the fail-open `alarmOpen` lets an adversary that withholds
   proofs run every round uncaught, at every horizon, against the same beacon.
5. **The beacon round is anchored by the requester.** The coin of position `t` is
   `BLAKE3(drand signature of round (seen_t + 2) ‖ position)`, where `seen_t` is the latest drand
   round named in the requester's countersigned commitment. In this file the coin space is
   abstract; `beacon_ideal` proves the fire rate exactly `pNum/2^64` for a uniform 64-bit coin, and
   the general theorem carries `εbeacon` as the hypothesis `hbeacon`. What `εbeacon` must absorb —
   drand's threshold honesty, the requester's honesty about the round it saw, BLAKE3 as a random
   function — is an assumption, not a number this file computes.

## What the binding term is

`δbind` is the probability that ONE named deterministic reduction outputs a BLAKE3 collision:
`hext` says that whenever some opened record differs from the served one under the same MMR root,
`reduce o` is a collision. That is the `cert_and_of_collisionExtractor` form of
`Selvage/BindingFixedHash.lean`; no adversary class is quantified, so the term is not vacuous at a
fixed hash. Its value is a human-ignorance bound, not a theorem.
-/
import Selvage.AuditSampling
import Selvage.AuditFlashProveDecide

namespace Minidregg.Selvage.AuditFlashProve

open Finset Minidregg.Selvage

set_option autoImplicit false

/-! ## 1. The world one oracle draw determines -/

/-- What one draw of the oracle `o` fixes: the adversary's whole strategy and the checker's
answers. `served h` is the claim the round served at history `h`; `opened h` the record the auditor
reads back through the MMR opening; `call c` the `cp_verify` call on the files of claim `c` (its
standard output and its exit status, `none` for no exit status of its own); `expect h` what the
auditor holds for the request (ID, build, `r`, `e`). Nothing here reads the current round's coin:
the claim is committed before the beacon emits. -/
structure World (Claim Ω : Type) where
  served : List Ω → Claim
  opened : List Ω → Claim
  isFalse : Claim → Bool
  call : Claim → String × Option UInt32
  expect : List Ω → Expect

namespace World

variable {Claim Ω : Type} [DecidableEq Claim]

/-- The verdict at history `h`: `verdictOf` on the call made for the OPENED record. -/
def verdict (W : World Claim Ω) (h : List Ω) : Verdict :=
  verdictOf (W.call (W.opened h)).1 (W.call (W.opened h)).2 (W.expect h)

/-- **The round.** Selection is `fires` on the round's coin; the alarm is `alarmFn` (the exported
`alarm`, or the falsifier `alarmOpen`) of that and the verdict. -/
def round (W : World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64)
    (alarmFn : Bool → Verdict → Bool) : Round Ω where
  corrupt h := W.isFalse (W.served h)
  fires _ ω := fires (coin ω) pNum
  alarms h ω := alarmFn (fires (coin ω) pNum) (W.verdict h)
  chkErr h _ := W.verdict h == .accept && decide (W.opened h = W.served h)
  chkAbort h _ := W.verdict h == .noVerdict
  bindBreak h _ := decide (W.opened h ≠ W.served h)

/-- The good-oracle event: the auditor's openings are the served records, and no false claim is
accepted. -/
def Good (W : World Claim Ω) : Prop :=
  (∀ h, W.opened h = W.served h) ∧ (∀ h, W.isFalse (W.served h) = true → W.verdict h ≠ .accept)

/-- **Fail-closed, proved for the exported `alarm`.** -/
theorem round_failClosed (W : World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64) :
    Round.FailClosed (W.round coin pNum alarm) := by
  intro h ω hf hab
  simp only [round, alarm] at *
  simp only [beq_iff_eq] at hab
  simp [hf, hab]

/-- The miss decomposition, from fail-closedness via the landed `missDecomp_of_failClosed`. -/
theorem round_missDecomp (W : World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64) :
    Round.MissDecomp (W.round coin pNum alarm) := by
  refine Round.missDecomp_of_failClosed (round_failClosed W coin pNum) ?_
  intro h ω _ hf _ hno
  simp only [round, alarm] at hf hno ⊢
  rw [hf] at hno
  have hacc : W.verdict h = .accept := by
    cases hv : W.verdict h <;> simp_all
  by_cases heq : W.opened h = W.served h
  · left; simp [hacc, heq]
  · right; simp [heq]

/-- The parameters on the good event: nominal rate `p`, beacon shortfall `εb`, and nothing else. -/
noncomputable def goodParams (p εb : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hεb : 0 ≤ εb) :
    AuditParams where
  p := p
  εchk := 0
  εbind := 0
  εbeacon := εb
  p_nonneg := hp0
  p_le_one := hp1
  εchk_nonneg := le_refl 0
  εchk_le_one := zero_le_one
  εbind_nonneg := le_refl 0
  εbeacon_nonneg := hεb

theorem goodParams_q (p εb : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hεb : 0 ≤ εb) :
    (goodParams p εb hp0 hp1 hεb).q = p - εb := by
  simp [goodParams, AuditParams.q]

/-- **On the good event, the four legs hold**, with `εchk = εbind = 0` and the beacon's shortfall
`εb` as given. -/
theorem legs_of_good [Fintype Ω] (W : World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64)
    {p εb : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hεb : 0 ≤ εb)
    (hbeacon : p - εb ≤ uniformProb Ω (fun ω => fires (coin ω) pNum = true))
    (hG : W.Good) :
    Round.DetectionLegs (goodParams p εb hp0 hp1 hεb) (W.round coin pNum alarm) where
  beacon := fun _ => by simpa [Round.BeaconLeg, goodParams, round] using hbeacon
  chk := by
    intro h hc
    have hna : W.verdict h ≠ .accept := hG.2 h (by simpa [round] using hc)
    have : uniformProb Ω (fun ω => (W.round coin pNum alarm).fires h ω = true ∧
        (W.round coin pNum alarm).chkErr h ω = true) = 0 :=
      uniformProb_false (fun ω hω => by simp [round, hna] at hω)
    rw [this]; simp [goodParams]
  bind := by
    intro h
    have : uniformProb Ω (fun ω => (W.round coin pNum alarm).bindBreak h ω = true) = 0 :=
      uniformProb_false (fun ω hω => by simp [round, hG.1 h] at hω)
    rw [this]; simp [goodParams]
  miss := round_missDecomp W coin pNum

end World

/-! ## 2. The count never exceeds the horizon -/

theorem count_le_length {Ω : Type} (R : Round Ω) : ∀ h : List Ω, R.count h ≤ h.length
  | [] => by simp [Round.count]
  | _ :: h => by
    have ih := count_le_length R h
    simp only [Round.count, List.length_cons]
    split_ifs <;> omega

theorem expOver_count_le {Ω : Type} [Fintype Ω] [Nonempty Ω] (R : Round Ω) (n : ℕ) :
    expOver Ω n (fun h => (R.count h : ℝ)) [] ≤ n := by
  have := expOver.mono (Ω := Ω) (f := fun h => (R.count h : ℝ)) (g := fun h => (h.length : ℝ))
    (fun h => by exact_mod_cast count_le_length R h) n []
  rw [expOver.length] at this
  simpa using this

/-! ## 3. The composed theorem: averaged over the oracle -/

section Composed

variable {Orc Claim Ω Witness : Type} [Fintype Orc] [Nonempty Orc] [Fintype Ω] [Nonempty Ω]
  [DecidableEq Claim]

/-- The checker-bad event: some false claim is accepted. -/
def ChkBad (W : World Claim Ω) : Prop :=
  ∃ h, W.isFalse (W.opened h) = true ∧ W.verdict h = .accept

/-- The binding-bad event: some opened record is not the served one. -/
def BindBad (W : World Claim Ω) : Prop := ∃ h, W.opened h ≠ W.served h

omit [Fintype Ω] [Nonempty Ω] in
theorem good_of_not_bad (W : World Claim Ω) (hc : ¬ ChkBad W) (hb : ¬ BindBad W) : W.Good := by
  refine ⟨fun h => ?_, fun h hf hacc => hc ⟨h, ?_, hacc⟩⟩
  · by_contra hne; exact hb ⟨h, hne⟩
  · have : W.opened h = W.served h := by by_contra hne; exact hb ⟨h, hne⟩
    rwa [this]

/-- **THE COMPOSED BOUND.** Draw the oracle `o` once. The expected number of corrupt rounds
before the first alarm, at horizon `n`, averaged over the oracle, is at most
`1/(p − εb) + n·(δchk + δbind)`, where

* `hbeacon`: the coin fires with probability at least `p − εb` (`beacon_ideal` discharges it with
  `εb = 0` for a uniform 64-bit coin);
* `hsnd` **[FP-chk-transport]**: the oracle makes `cp_verify` accept some false claim with
  probability at most `δchk` (FlashProve's `sound`, for `verify`, gives `fpSoundErr Q`);
* `hext`: whenever an opening differs from the served record, the named reduction `reduce o` is a
  collision (`Coll`); `δbind` is the probability of that.

Every hypothesis is about a named object; none quantifies over an adversary class. -/
theorem expected_count_le (W : Orc → World Claim Ω) (coin : Ω → UInt64) (pNum : UInt64)
    {p εb δchk : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hεb : 0 ≤ εb) (hq : 0 < p - εb)
    (hbeacon : p - εb ≤ uniformProb Ω (fun ω => fires (coin ω) pNum = true))
    (hsnd : uniformProb Orc (fun o => ChkBad (W o)) ≤ δchk)
    (Coll : Orc → Witness → Prop) (reduce : Orc → Witness)
    (hext : ∀ o, BindBad (W o) → Coll o (reduce o)) (n : ℕ) :
    (∑ o : Orc, expOver Ω n (fun h => ((W o).round coin pNum alarm |>.count h : ℝ)) [])
        / (Fintype.card Orc : ℝ)
      ≤ 1 / (p - εb) + n * (δchk + uniformProb Orc (fun o => Coll o (reduce o))) := by
  classical
  set E : Orc → ℝ := fun o => expOver Ω n (fun h => ((W o).round coin pNum alarm |>.count h : ℝ)) []
  have hcard : (0 : ℝ) < (Fintype.card Orc : ℝ) := by exact_mod_cast Fintype.card_pos
  -- per oracle: good gives 1/q₀, bad gives n
  have hper : ∀ o, E o ≤ 1 / (p - εb) + n * (if ChkBad (W o) ∨ Coll o (reduce o) then 1 else 0) := by
    intro o
    have hn0 : (0 : ℝ) ≤ 1 / (p - εb) := le_of_lt (one_div_pos.mpr hq)
    by_cases hb : ChkBad (W o) ∨ Coll o (reduce o)
    · simp only [hb, ite_true, mul_one]
      have := expOver_count_le ((W o).round coin pNum alarm) n
      linarith
    · simp only [hb, ite_false, mul_zero, add_zero]
      push Not at hb
      have hG := good_of_not_bad (W o) hb.1 (fun hbb => hb.2 (hext o hbb))
      have hL := World.legs_of_good (W o) coin pNum hp0 hp1 hεb hbeacon hG
      have hq' : 0 < (World.goodParams p εb hp0 hp1 hεb).q := by
        rw [World.goodParams_q]; exact hq
      have := Round.sequential_bound_of_legs hL hq' n
      rwa [World.goodParams_q] at this
  have hsum : ∑ o, E o ≤ ∑ o, (1 / (p - εb) + n * (if ChkBad (W o) ∨ Coll o (reduce o) then (1 : ℝ) else 0)) :=
    Finset.sum_le_sum fun o _ => hper o
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum] at hsum
  have hpr : (∑ o : Orc, if ChkBad (W o) ∨ Coll o (reduce o) then (1 : ℝ) else 0)
      / (Fintype.card Orc : ℝ) ≤ δchk + uniformProb Orc (fun o => Coll o (reduce o)) := by
    rw [← uniformProb_eq_avg_indicator]
    exact le_trans (uniformProb_or_le _ _) (by linarith [hsnd])
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [div_le_iff₀ hcard]
  have h2 := mul_le_mul_of_nonneg_left hpr hn
  rw [mul_div_assoc', div_le_iff₀ hcard] at h2
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

/-- The three nominal rates, as `⌊p · 2^64⌋`. -/
def pNum001 : UInt64 := 184467440737095516
def pNum005 : UInt64 := 922337203685477580
def pNum020 : UInt64 := 3689348814741910323

#guard pNum001.toNat = 18446744073709551616 / 100
#guard pNum005.toNat = 18446744073709551616 / 20
#guard pNum020.toNat = 18446744073709551616 / 5

/-- **The instance at `p = 0.01`, the ideal beacon, and `Q = 2^64`.** Expected corrupt rounds
before the first alarm, at any horizon `n`, at most `2^64/⌊0.01·2^64⌋ + n·(fpSoundErr 2^64 + δbind)`,
under **[FP-chk-transport]** (`hsnd`) and the collision extractor (`hext`). -/
theorem flashprove_p001 {Orc Claim Witness : Type} [Fintype Orc] [Nonempty Orc] [DecidableEq Claim]
    (W : Orc → World Claim (Fin (2 ^ 64)))
    (hsnd : uniformProb Orc (fun o => ChkBad (W o)) ≤ (fpSoundErr (2 ^ 64) : ℝ))
    (Coll : Orc → Witness → Prop) (reduce : Orc → Witness)
    (hext : ∀ o, BindBad (W o) → Coll o (reduce o)) (n : ℕ) :
    (∑ o : Orc, expOver (Fin (2 ^ 64)) n
        (fun h => ((W o).round coin64 pNum001 alarm |>.count h : ℝ)) []) / (Fintype.card Orc : ℝ)
      ≤ 1 / ((pNum001.toNat : ℝ) / 2 ^ 64)
        + n * ((fpSoundErr (2 ^ 64) : ℝ) + uniformProb Orc (fun o => Coll o (reduce o))) := by
  have hp : (0 : ℝ) < (pNum001.toNat : ℝ) / 2 ^ 64 := by
    apply div_pos _ (by norm_num); exact_mod_cast (by decide : 0 < pNum001.toNat)
  have hp1 : (pNum001.toNat : ℝ) / 2 ^ 64 ≤ 1 := by
    rw [div_le_one (by norm_num)]; exact_mod_cast le_of_lt pNum001.toNat_lt
  have := expected_count_le W coin64 pNum001 (le_of_lt hp) hp1 (le_refl 0)
    (by simpa using hp) (by rw [beacon_ideal]; simp) hsnd Coll reduce hext n
  simpa using this

/-! ## 6. Teeth -/

namespace Teeth

/-- A claim is a Boolean: `true` is false (the served reply is not the model's). -/
abbrev Claim := Bool

private def yes : String × Option UInt32 :=
  ("covered: r=60 e=64 tokens=61..63 y=yes policy=exact-match sh=8\n" ++
   "result-v1 status=0 claim=exact-match id=A r=60 e=64 y=yes policy=exact-match build=B\nYES\n", some 0)

private def ex : Expect := { id := "A", build := "B", r := 60, e := 64, acceptWork := true }

#guard verdictOf yes.1 yes.2 ex == .accept

/-- The honest world: always corrupt, the checker rejects false claims (exit 1). -/
def honestChecker : World Claim (Fin (2 ^ 64)) where
  served _ := true
  opened _ := true
  isFalse c := c
  call c := if c then ("NO: reply-differs\n", some 1) else yes
  expect _ := ex

/-- It is good: the hypotheses of `expected_count_le` are inhabited with `δchk = δbind = 0`. -/
theorem honestChecker_verdict (h : List (Fin (2 ^ 64))) :
    honestChecker.verdict h = .reject := rfl

theorem honestChecker_good : honestChecker.Good :=
  ⟨fun _ => rfl, fun h _ => by rw [honestChecker_verdict]; simp⟩

/-- A world whose opening is not the served record is NOT good: `Good` has content. (That an
accepting checker is not good is the `#guard` above read against `Good`'s second conjunct; the
kernel does not evaluate `String` parsing, so that case is checked by evaluation, not by proof.) -/
def bindBreaker : World Claim (Fin (2 ^ 64)) := { honestChecker with opened := fun _ => false }

theorem bindBreaker_not_good : ¬ bindBreaker.Good := fun hG => by
  have := hG.1 []; simp [bindBreaker, honestChecker] at this

/-- **The withholding adversary**: always corrupt, never hands a proof (no exit status). -/
def withholder : World Claim (Fin (2 ^ 64)) :=
  { honestChecker with call := fun _ => ("", none) }

/-- **FAIL-OPEN COLLAPSES.** Under `alarmOpen` the withholder is never caught: the expected
corrupt count at horizon `n` is exactly `n`, for every `n` and every rate `pNum`. -/
theorem withholder_verdict (h : List (Fin (2 ^ 64))) : withholder.verdict h = .noVerdict := rfl

theorem FailOpen.collapse (pNum : UInt64) (n : ℕ) :
    expOver (Fin (2 ^ 64)) n (fun h => ((withholder.round coin64 pNum alarmOpen).count h : ℝ)) []
      = n := by
  have halarm : ∀ h ω, (withholder.round coin64 pNum alarmOpen).alarms h ω = false := by
    intro h ω
    show alarmOpen _ (withholder.verdict h) = false
    rw [withholder_verdict]; simp [alarmOpen]
  have hstop : ∀ h : List (Fin (2 ^ 64)),
      (withholder.round coin64 pNum alarmOpen).stopped h = false := by
    intro h; induction h with
    | nil => rfl
    | cons ω h ih => simp [Round.stopped, ih, halarm]
  have hcount : ∀ h : List (Fin (2 ^ 64)),
      (withholder.round coin64 pNum alarmOpen).count h = h.length := by
    intro h; induction h with
    | nil => rfl
    | cons ω h ih =>
      have hc : (withholder.round coin64 pNum alarmOpen).corrupt h = true := rfl
      simp [Round.count, hstop h, ih, hc]
  simp only [hcount]
  rw [expOver.length]; simp

/-- The fail-open round is `FailOpen` in `AuditSampling`'s sense. -/
theorem withholder_failOpen (pNum : UInt64) :
    Round.FailOpen (withholder.round coin64 pNum alarmOpen) := by
  intro h ω _
  show alarmOpen _ (withholder.verdict h) = false
  rw [withholder_verdict]; simp [alarmOpen]

/-- **And fail-closed catches the same adversary at the nominal rate**: the withholder's world is
good-for-binding, and its verdict is `noVerdict`, never `accept`, so `legs_of_good` applies and the
bound is `1/p`. -/
theorem withholder_good : withholder.Good :=
  ⟨fun _ => rfl, fun h _ => by rw [withholder_verdict]; simp⟩

/-- At `p = 0.2` the fail-open count passes the fail-closed bound `1/p = 5` at horizon 6. -/
theorem failOpen_beats_bound :
    1 / ((pNum020.toNat : ℝ) / 2 ^ 64) <
      expOver (Fin (2 ^ 64)) 6 (fun h => ((withholder.round coin64 pNum020 alarmOpen).count h : ℝ)) [] := by
  rw [FailOpen.collapse]
  have : (pNum020.toNat : ℝ) = 3689348814741910323 := by norm_cast
  rw [this]; norm_num

end Teeth

/-! ## Axioms -/

/-- info: 'Minidregg.Selvage.AuditFlashProve.expected_count_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms expected_count_le
/-- info: 'Minidregg.Selvage.AuditFlashProve.flashprove_p001' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms flashprove_p001
/-- info: 'Minidregg.Selvage.AuditFlashProve.World.round_failClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms World.round_failClosed
/-- info: 'Minidregg.Selvage.AuditFlashProve.beacon_ideal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms beacon_ideal
/-- info: 'Minidregg.Selvage.AuditFlashProve.Teeth.FailOpen.collapse' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.FailOpen.collapse
/-- info: 'Minidregg.Selvage.AuditFlashProve.Teeth.failOpen_beats_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.failOpen_beats_bound
/-- info: 'Minidregg.Selvage.AuditFlashProve.fpSoundErr_2_64' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fpSoundErr_2_64

/-- info: 'Minidregg.Selvage.AuditFlashProve.World.round_missDecomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms World.round_missDecomp
/-- info: 'Minidregg.Selvage.AuditFlashProve.World.legs_of_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms World.legs_of_good
/-- info: 'Minidregg.Selvage.AuditFlashProve.Teeth.withholder_failOpen' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.withholder_failOpen
/-- info: 'Minidregg.Selvage.AuditFlashProve.Teeth.withholder_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.withholder_good
/-- info: 'Minidregg.Selvage.AuditFlashProve.Teeth.honestChecker_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.honestChecker_good
/-- info: 'Minidregg.Selvage.AuditFlashProve.Teeth.bindBreaker_not_good' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms Teeth.bindBreaker_not_good
/-- info: 'Minidregg.Selvage.AuditFlashProve.fpSoundErr_zero_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms fpSoundErr_zero_floor

end Minidregg.Selvage.AuditFlashProve
