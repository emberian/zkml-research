/-
# Selvage.OracleLogProgram — [ORACLE-LOG-program]: the audit finding (the stated
per-slot bound is REFUTABLE at every useful price) and the repair (link-root
opening re-attaches the fixed pair).

`Selvage/OracleLogExtraction.lean` sharpened the deployed-ZK adaptive-increment
residual to ONE per-slot lemma, `[ORACLE-LOG-program]` (`OracleLogProgram`):
at the game slot where round `i`'s prefix query is first answered, bound the
adversary's CONTINUATION — that after seeing the fresh `ρ` it completes an
ACCEPTING run whose log-read increment at `i` is false. The task here was to
prove it by rerunning `Selvage/Depth.lean`'s game-slot choreography.

**Audit finding first (house precedent: `OB2_depth_composition_false`): the
statement is REFUTABLE at every εslot below 1 — the continuation costs the
adversary NOTHING.** The diagnosis is structural, not probabilistic:
`accReductionBcsShifted.verify` checks openings, the genesis anchor, and the
LAST message's word against the aggregate — and NOTHING ELSE. In particular
no clause ever ties the round-`i` increment `ρ_i⁻¹·(h_{i+1} − h_i)` to the
CHAIN's own committed link word: the links' roots (`(ch.get i).claim.rt`)
are never opened, and the intermediate fold roots are tethered only through
the telescoped SUM `h_last − h_0` — every summand of which is committed
AFTER its own challenge. The one-query adversary `progPrv` (built below on
the landed F₅ chain) exploits exactly this:

* it queries the round-1 prefix `(𝕩, π₀‖π₁)` ONCE — that is the hit slot,
  and the answer IS the fold challenge `ρ₁` (`srFinalChal_eq_answerOf`);
* it then commits, as the LAST message, the codeword `(2 + ρ₁) • 1⃗` — which
  satisfies the aggregate `q2 = 2 + ρ₀·0 + ρ₁·1` EXACTLY, for every draw
  (link 0's target is 0, so the unqueried round-0 challenge is inert);
* the log-read round-1 increment is `ρ₁⁻¹·(1 + ρ₁) • 1⃗`, whose `q2`-value
  `ρ₁⁻¹·(1 + ρ₁) ≠ 1` for EVERY `ρ₁ ∈ F₅` (kernel-checked) — the link-1
  target is missed on every coin outcome.

So the hit-horn event holds with probability EXACTLY 1
(`progEvent_total`/`oracleLogProgram_forces_one`): `OracleLogProgram` at the
intended per-slot price `accRbrError = 1/|F|` is FALSE
(`oracleLogProgram_accRbrError_false`), and — the headline — the route
target itself, `adaptiveIncrement_sound_via_log` at `εlog = accRbrError`,
is FALSE on the landed F₅ instance (`adaptiveViaLog_accRbrError_false`):
`1 = Pr[event] ≰ (1 + 3)·(1/5) = 4/5`. The RO-programming continuation
argument the residual called for does not exist, because acceptance never
reads what the programmer programmed.

**The repair — what the deployment actually checks.** WARP's accumulation
verifier spot-checks the incoming link's word against the LINK's own
commitment: the fold step must open the link word's columns from the link's
root and verify `h_{i+1}(q_j) = h_i(q_j) + ρ_i · w_i(q_j)` columnwise. That
clause is `LinkOpened` below, and it CLOSES the hole deterministically:

* `linkOpened_honest` — the honest shifted run passes the check at every
  round (completeness: the repair does not exclude honest provers);
* `linkOpened_increment_pinned` — **the fixed-pair re-attachment**: under
  `LinkOpened` + binding, with the previous root's columns those of a
  codeword, the log-read increment at any NONZERO recorded challenge IS the
  link's committed word — a word fixed in the STATEMENT, before every
  challenge of the run. No continuation bound is needed at the hit slot:
  the adaptive-increment event collapses back to the fixed-pair alphabet
  the landed `accSound_rbr` machinery prices, and the only surviving
  per-slot mass is the zero-challenge draw (`1/|F|` — the `accRbrError`
  additive term's home) plus the statement-fixed misaligned-designation
  case (fixed-pair, `[ACC-rbr-bcs]`-shaped);
* `logIncrement_linked` — the pin, spoken in the extractor's vocabulary:
  the log-read increment map returns the link's committed word;
* teeth on the landed chain: the refuting adversary DIES against the
  repaired clause — `progLinkOpened_refuted` (its programmed increment
  cannot open against the honest link root: `2 + ρ = 1 + ρ` is refutable
  for every `ρ`, by binding) and `progLinked_zero` (the repaired per-slot
  event for `progPrv` is EMPTY — probability 0, not merely ≤ 1/|F|).

`OracleLogProgramLinked` states the repaired per-slot obligation
(statement-first, ATLAS fields on the def) — **[ORACLE-LOG-linked]**, the
new sharp residual. The horn split survives the refutation and is proved
generically (`logSlot_cover`: every run's round-`i` query is either absent
from the log — the fresh horn, where `logIncrement_none_of_unqueried` and
`unqueried_chal_fresh` (CITED) put both roots in output-fixed territory —
or first answered at some game slot `j < t`, the `(t + k)` union's budget).
-/
import Selvage.OracleLogExtraction
import Selvage.AccSoundRbr

namespace Minidregg.Selvage

/-! ## Counting helper: an everywhere-true event has probability 1 -/

lemma uniformProb_eq_one {C : Type} [Fintype C] [Nonempty C] {p : C → Prop}
    (h : ∀ c, p c) : uniformProb C p = 1 := by
  unfold uniformProb
  rw [Nat.card_congr (Equiv.subtypeUnivEquiv h), Nat.card_eq_fintype_card]
  exact div_self (by exact_mod_cast Fintype.card_ne_zero)

/-! ## The horn split — the cover skeleton, generic and intact

The fresh/hit dichotomy at the increment granularity: any run's designated
round-`a` query is either NOT in the log — the fresh horn, where the
extractor reads nothing (`logIncrement_none_of_unqueried`, CITED) and the
challenge is the output-independent fresh coin (`unqueried_chal_fresh`,
CITED): both fold roots are output-fixed — or FIRST answered at some game
slot `j < t` (`hitAt`, the attribution `gameSlotBound_proved` unions over).
This is the piece of the diagnosed composition that survives the refutation
below unchanged; the repaired route reruns the same split. -/

section HornSplit

open Classical

theorem logSlot_cover {r : Reduction} {s t : ℕ} (P : SrProver r s)
    (a : Fin r.k) (c : Fin t → r.Chal) :
    OracleLog.answerOf (srTrace P c) ((srOut P c).query a) = none ∨
      ∃ j : Fin t, hitAt P a j c := by
  cases hf : (srTrace P c).find?
      (fun e => decide (e.1 = (srOut P c).query a)) with
  | none =>
      refine Or.inl (OracleLog.answerOf_eq_none.mpr fun e he => ?_)
      have := List.find?_eq_none.mp hf e he
      simpa using this
  | some e =>
      obtain ⟨n, hn, hlt⟩ := exists_findIdx?_of_find? _ _ _ hf
      rw [srTrace_length] at hlt
      exact Or.inr ⟨⟨n, hlt⟩, hn⟩

end HornSplit

/-! ## The audit finding: the zero-tether adversary

One query, on the landed F₅ chain. The event of `[ORACLE-LOG-program]`
holds on EVERY coin outcome. -/

namespace OracleLogProgramExample

open RSExample LCExample AccExample ZkHidingExample ZkExtractionExample
  CommitExample AccRbrBcsExample AccRbrBcsShiftedExample AccSoundRbrExample

/-- The honest commitment message of a word: root, spot columns, honest
opening proofs — the same shape as `msgBcs`/`shiftedMsg`, at an arbitrary
word. -/
noncomputable def msgOf (w : Fin 4 → ZMod 5) :
    BcsMsg (Fin 4 → ZMod 5) (ZMod 5) Unit 2 :=
  ⟨S₅.commit w, fun j => w (qPair j), fun j => S₅.openAt w (qPair j)⟩

theorem msgOf_opens (w : Fin 4 → ZMod 5) : ColsOpen S₅ qPair (msgOf w) :=
  fun j => S₅.verifyOpen_commit w (qPair j)

theorem msgOf_word {w : Fin 4 → ZMod 5} (hw : w ∈ reedSolomonCode dom₅ 2) :
    bcsWord dom₅ 2 qPair (msgOf w) = w :=
  recoverFromColumns_sound dom₅ le_rfl qPair_inj hw fun _ => rfl

/-- The adversary's message family at hijacked round-1 challenge `ρ`:
`h₀ := xWord` (the genesis anchor, honest), `h₁ := 1⃗` (a codeword with
`q2 h₁ = 1`, committed BEFORE `ρ` — it sits inside the query), and the last
message `(2 + ρ) • 1⃗` — chosen AFTER `ρ`, solving the aggregate's equation
`q2 = 2 + ρ·1` exactly. The round-1 increment this family realizes is
`ρ⁻¹·(1 + ρ) • 1⃗`, which misses the link-1 target `1` at EVERY `ρ`. -/
noncomputable def progMsgs (ρ : ZMod 5) :
    ℕ → BcsMsg (Fin 4 → ZMod 5) (ZMod 5) Unit 2
  | 0 => msgOf xWord
  | 1 => msgOf oneWord
  | _ => msgOf ((2 + ρ) • oneWord)

/-- The adversary's output at hijacked challenge `ρ`: the landed genesis
statement, the three-message family, no salts, junk candidate witness. -/
noncomputable def progOut (ρ : ZMod 5) : SrOutput accReductionBcsShifted_F5 0 :=
  ⟨⟨(), genesis, xWord⟩, fun c => progMsgs ρ (c : ℕ), fun _ => Fin.elim0,
    fun _ => 0⟩

/-- The ONE query: the designated round-1 prefix `(𝕩, π₀‖π₁)`. Its prefix
does not reach the last message, so it is the same move for every `ρ`. -/
noncomputable def progQry : SrMove accReductionBcsShifted_F5 0 :=
  (progOut 0).query (Fin.castSucc (1 : Fin 2))

/-- **The zero-tether adversary**: query the round-1 prefix, read the
answer `ρ₁` off the response list, output `progOut ρ₁`. One query — the
minimal grinding budget. -/
noncomputable def progPrv : SrProver accReductionBcsShifted_F5 0 where
  move := fun _ => progQry
  out := fun resp => progOut (resp.getD 0 0)

/-- The round-1 designated query of the output is the queried move — for
every hijacked challenge (the last message is outside the prefix). -/
theorem progOut_query1 (ρ : ZMod 5) :
    (progOut ρ).query (Fin.castSucc (1 : Fin 2)) = progQry := rfl

/-- The game trace: exactly the one query, answered by the game's first
fresh coin. -/
theorem progTrace (c : Fin 1 → ZMod 5) :
    srTrace progPrv c = [(progQry, c 0)] := rfl

/-- The adversary's output on the run: `progOut` at the recorded answer. -/
theorem progSrOut (c : Fin 1 → ZMod 5) : srOut progPrv c = progOut (c 0) := rfl

/-- **The hit**: the round-1 designated query is first answered at game
slot 0 — on every coin outcome. -/
theorem progHit (c : Fin 1 → ZMod 5) :
    hitAt progPrv (Fin.castSucc (1 : Fin 2)) (0 : Fin 1) c := by
  classical
  unfold hitAt
  rw [progTrace, progSrOut, progOut_query1]
  simp [List.findIdx?_cons]

/-- The round-1 final challenge IS the recorded answer `c 0` — the
`srFinalChal_eq_answerOf` bridge, computed on the built run. -/
theorem progChal1 (c : Fin 1 → ZMod 5) (d : Fin 3 → ZMod 5) :
    srFinalChal progPrv c d (Fin.castSucc (1 : Fin 2)) = c 0 := by
  rw [srFinalChal_def, progTrace, progSrOut, progOut_query1,
    List.find?_cons_of_pos (by simp)]

/-- The log answers the round-1 designated query with `c 0`. -/
theorem progAnswer (c : Fin 1 → ZMod 5) :
    OracleLog.answerOf (srTrace progPrv c)
      ((srOut progPrv c).query (Fin.castSucc (1 : Fin 2))) = some (c 0) := by
  rw [progTrace, progSrOut, progOut_query1]
  exact OracleLog.answerOf_cons_self _ _ _

/-- **The programmed increment, read off the log**: `ρ₁⁻¹·(1 + ρ₁) • 1⃗` at
`ρ₁ = c 0` — the `γ⁻¹`-difference of the two committed roots, exactly what
`logIncrement` recovers. -/
theorem progLogIncrement (c : Fin 1 → ZMod 5) :
    logIncrement (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
        (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
        S₅ dom₅ 2 qPair (srOut progPrv c) (srTrace progPrv c) (1 : Fin 2)
      = some (((c 0)⁻¹ * (1 + c 0)) • oneWord) := by
  have h2 : (srOut progPrv c).πs (Fin.succ (1 : Fin 2))
      = msgOf ((2 + c 0) • oneWord) := rfl
  have h1 : (srOut progPrv c).πs (Fin.castSucc (1 : Fin 2))
      = msgOf oneWord := rfl
  have hsub : (2 + c 0) • oneWord - oneWord = (1 + c 0) • oneWord := by
    have e1 : (2 + c 0) • oneWord - oneWord
        = (2 + c 0) • oneWord - (1 : ZMod 5) • oneWord := by rw [one_smul]
    rw [e1, ← sub_smul]
    congr 1
    ring
  unfold logIncrement
  rw [progAnswer, Option.map_some]
  refine congrArg some ?_
  rw [h2, h1, msgOf_word (Submodule.smul_mem _ _ oneWord_mem),
    msgOf_word oneWord_mem, hsub, smul_smul]

/-- The shifted log extractor's round-1 output on the run. -/
theorem progExtract (c : Fin 1 → ZMod 5) :
    shiftedLogExtractor (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot
        goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
        (by norm_num) S₅ dom₅ 2 qPair 0
        (srOut progPrv c) (srTrace progPrv c) (1 : Fin 2)
      = ((c 0)⁻¹ * (1 + c 0)) • oneWord := by
  unfold shiftedLogExtractor
  rw [progLogIncrement]
  rfl

/-- **The programmed last word satisfies the aggregate EXACTLY, on every
draw**: link 0's target is `0` (its challenge — the unqueried round-0
prefix's fresh coin — is inert in the fold), and the round-1 term is solved
by construction: `q2 ((2 + ρ₁) • 1⃗) = 2 + ρ₁·1`. -/
theorem progAggSat (c : Fin 1 → ZMod 5) (d : Fin 3 → ZMod 5) :
    AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
      (aggregate linRoot
        (padSched fun i : Fin 2 => srFinalChal progPrv c d i.castSucc)
        genesis goodChain)
      ((2 + c 0) • oneWord) := by
  have hγ1 : padSched (fun i : Fin 2 => srFinalChal progPrv c d i.castSucc) 1
      = c 0 := by
    rw [padSched_lt _ (by norm_num : (1 : ℕ) < 2)]
    exact progChal1 c d
  have hagg : ∀ γs : ℕ → ZMod 5,
      aggregate linRoot γs genesis goodChain
        = foldClaims linRoot (foldClaims linRoot genesis claim₀ (γs 0))
            claim₁ (γs 1) := fun γs => rfl
  refine ⟨Submodule.mem_top, fun jj => ?_⟩
  rw [hagg]
  show q2 ((2 + c 0) • oneWord)
      = 2 + padSched (fun i : Fin 2 => srFinalChal progPrv c d i.castSucc) 0
          * 0
        + padSched (fun i : Fin 2 => srFinalChal progPrv c d i.castSucc) 1
          * 1
  rw [hγ1, map_smul, smul_eq_mul, show q2 oneWord = (1 : ZMod 5) from rfl]
  ring

/-- **The FS verifier accepts the run, on every draw** — openings verify,
the genesis anchor holds, and the output is the aggregate with the
programmed last word. -/
theorem progVerify (c : Fin 1 → ZMod 5) (d : Fin 3 → ZMod 5) :
    fiatShamir accReductionBcsShifted_F5 0
        (fsOracle (srOut progPrv c) (srFinalChal progPrv c d))
        (srOut progPrv c)
      = some (aggregate linRoot
            (padSched fun i : Fin 2 => srFinalChal progPrv c d i.castSucc)
            genesis goodChain,
          (2 + c 0) • oneWord) := by
  classical
  rw [fiatShamir_fsOracle]
  have hopen : ∀ i : Fin 3, ColsOpen S₅ qPair ((srOut progPrv c).πs i) := by
    intro i
    fin_cases i
    · exact msgOf_opens xWord
    · exact msgOf_opens oneWord
    · exact msgOf_opens ((2 + c 0) • oneWord)
  have hanchor : ∀ j, ((srOut progPrv c).πs 0).cols j = xWord (qPair j) :=
    fun j => rfl
  show (if (∀ i, ColsOpen S₅ qPair ((srOut progPrv c).πs i)) ∧
        (∀ j, ((srOut progPrv c).πs 0).cols j = xWord (qPair j)) then
      some (aggregate linRoot
          (padSched fun i : Fin 2 => srFinalChal progPrv c d i.castSucc)
          genesis goodChain,
        bcsWord dom₅ 2 qPair ((srOut progPrv c).πs (Fin.last 2)))
    else none) = _
  rw [if_pos ⟨hopen, hanchor⟩,
    show (srOut progPrv c).πs (Fin.last 2) = msgOf ((2 + c 0) • oneWord)
      from rfl,
    msgOf_word (Submodule.smul_mem _ _ oneWord_mem)]

/-- **The programmed increment misses link 1, at EVERY recorded challenge**:
`ρ⁻¹·(1 + ρ) ≠ 1` for all five values of `ρ` (at `ρ = 0` the increment is
`0`, missing the target `1`; at `ρ ≠ 0` it is `1 + ρ⁻¹ ≠ 1`) —
kernel-checked. -/
theorem progMisaligned (c : Fin 1 → ZMod 5) :
    ¬ LinkAligned (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) genesis goodChain
      (1 : Fin 2) (((c 0)⁻¹ * (1 + c 0)) • oneWord) := by
  have key : ∀ ρ : ZMod 5, ρ⁻¹ * (1 + ρ) ≠ 1 := by decide
  rintro ⟨-, hall⟩
  have hval : (goodChain.get (1 : Fin 2)).claim.targets 0 = 1 := by decide
  have hw : genesis.weights 0 = q2 := rfl
  have h := hall 0
  rw [hw, hval, map_smul, smul_eq_mul, show q2 oneWord = (1 : ZMod 5) from rfl,
    mul_one] at h
  exact key (c 0) h

/-- **The `[ORACLE-LOG-program]` event holds on EVERY coin outcome** — the
hit at slot 0, the acceptance with the candidate in `R'_{≤δ}`, and the false
log-read increment at round 1, all deterministic. -/
theorem progEvent_total (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 16))
    (coins : (Fin 1 → ZMod 5) × (Fin 3 → ZMod 5)) :
    hitAt progPrv (Fin.castSucc (1 : Fin 2)) (0 : Fin 1) coins.1 ∧
    (∃ (x' : AccClaim (ZMod 5) (ZMod 5) (Fin 4) 1) (y' : Fin 4 → ZMod 5),
      fiatShamir accReductionBcsShifted_F5 0
          (fsOracle (srOut progPrv coins.1) (srFinalChal progPrv coins.1
            coins.2))
          (srOut progPrv coins.1) = some (x', y') ∧
      RelaxedMem accReductionBcsShifted_F5.R' δ
        (srOut progPrv coins.1).stmt.idx x' y' (srOut progPrv coins.1).w') ∧
    ¬ LinkAligned (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
      (srOut progPrv coins.1).stmt.x goodChain (1 : Fin 2)
      (shiftedLogExtractor (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot
        goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
        (by norm_num) S₅ dom₅ 2 qPair 0
        (srOut progPrv coins.1) (srTrace progPrv coins.1) (1 : Fin 2)) := by
  refine ⟨progHit coins.1, ⟨_, _, progVerify coins.1 coins.2,
    ⟨(2 + coins.1 0) • oneWord, progAggSat coins.1 coins.2, ?_⟩⟩, ?_⟩
  · rw [fracHamming_self]
    exact hδ.1.le
  · rw [progExtract coins.1]
    exact progMisaligned coins.1

/-- **[ORACLE-LOG-program] is refutable at every useful price**: any
`εslot` it holds at is forced to `≥ 1` on the whole window — the per-slot
event is CERTAIN for the zero-tether adversary. -/
theorem oracleLogProgram_forces_one (εslot : ℝ → ℝ)
    (h : OracleLogProgram (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot
      goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
      (by norm_num) S₅ dom₅ 2 qPair εslot) :
    ∀ δ ∈ Set.Ioo (0 : ℝ) (1 / 16), 1 ≤ εslot δ := by
  intro δ hδ
  have hb := h 0 1 progPrv (1 : Fin 2) (0 : Fin 1) δ hδ
  refine le_trans (le_of_eq (uniformProb_eq_one ?_).symm) hb
  exact progEvent_total δ hδ

/-- **The intended per-slot price is dead**: `[ORACLE-LOG-program]` at
`εslot = accRbrError = 1/|F|` — the price the `(t + k)·accRbrError`
composition was to pay per slot — is FALSE on the landed F₅ chain. -/
theorem oracleLogProgram_accRbrError_false :
    ¬ OracleLogProgram (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot
      goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
      (by norm_num) S₅ dom₅ 2 qPair
      (accRbrError (ZMod 5) (fun _ => 0)) := by
  intro h
  have h1 := oracleLogProgram_forces_one _ h (1 / 32)
    (by rw [Set.mem_Ioo]; exact ⟨by norm_num, by norm_num⟩)
  rw [accRbrError_zero_five] at h1
  norm_num at h1

/-- **The route target is dead at the intended price** — the headline.
`adaptiveIncrement_sound_via_log` at `εlog = accRbrError` is FALSE on the
landed F₅ instance: the zero-tether adversary makes the `sound_log` event
CERTAIN (`t = 1` query), while the claimed bound is
`(1 + 3)·(1/5) = 4/5 < 1`. The pinning clause is what closes the trap: any
inhabitant's extractor must return the log-read increment
(`adaptive_pins_extractor_F5`'s clause), and that increment misses link 1 on
every draw. Route (i) of `[ACC-rbr-bcs-shifted-resid]`(a) CANNOT close as
stated — the verifier it prices never reads what the programmer programs. -/
theorem adaptiveViaLog_accRbrError_false :
    ¬ adaptiveIncrement_sound_via_log
      (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
      (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
      S₅ dom₅ 2 qPair (accRbrError (ZMod 5) (fun _ => 0)) := by
  rintro ⟨olr, hpin⟩
  have hδ : (1 / 32 : ℝ) ∈ Set.Ioo (0 : ℝ) (1 / 16) := by
    rw [Set.mem_Ioo]
    exact ⟨by norm_num, by norm_num⟩
  have hb := olr.sound_log 0 1 (1 / 32) hδ progPrv
  have h1 : (1 : ℝ) ≤ (((1 : ℕ) : ℝ) + ((accReductionBcsShifted_F5).k : ℝ))
      * accRbrError (ZMod 5) (fun _ => 0) (1 / 32) := by
    refine le_trans (le_of_eq (uniformProb_eq_one ?_).symm) hb
    intro coins
    refine ⟨Set.mem_univ _, ?_, _, _, progVerify coins.1 coins.2,
      ⟨(2 + coins.1 0) • oneWord, progAggSat coins.1 coins.2, ?_⟩⟩
    · rintro ⟨ystar, ⟨-, hlinks⟩, -⟩
      refine progMisaligned coins.1 ?_
      rw [← hpin 0 (srOut progPrv coins.1) (srTrace progPrv coins.1) (1 : Fin 2)
        _ (progLogIncrement coins.1)]
      exact hlinks (1 : Fin 2)
    · rw [fracHamming_self]
      norm_num
  rw [show (accReductionBcsShifted_F5).k = 3 from rfl,
    accRbrError_zero_five] at h1
  norm_num at h1

end OracleLogProgramExample

/-! ## The repair: link-root opening

The clause the deployed accumulation verifier runs and
`accReductionBcsShifted.verify` omits: the round's fold step must OPEN the
link's committed word from the LINK's root and spot-check the fold
columnwise. Under binding this pins the increment to a word committed in
the STATEMENT — before every challenge of the run — which is exactly the
fixed-pair territory the landed `accSound_rbr` machinery prices. -/

section LinkBinding

variable {Root' Op : Type} {F : Type} [Field F] {m t : ℕ}

/-- **The link-opening check** for one fold step: some claimed link-word
columns `lc` with proofs `lo` open from the link's root `rt`, and the two
consecutive fold roots' opened columns satisfy the fold equation
`h'(q_j) = h(q_j) + ρ · lc j` at every spot. The run supplies `(lc, lo)`;
binding (not honesty) is what pins `lc` to the committed word
(`binding_columns`, CITED). -/
def LinkOpened (S : BindingCommitment Root' F (Fin m) Op)
    (q : Fin t → Fin m) (rt : Root') (π π' : BcsMsg Root' F Op t) (ρ : F) :
    Prop :=
  ∃ (lc : Fin t → F) (lo : Fin t → Op),
    (∀ j, S.verifyOpen rt (q j) (lc j) (lo j)) ∧
    ∀ j, π'.cols j = π.cols j + ρ * lc j

/-- **Completeness — the honest shifted run passes the check at every
round**: open the link word honestly; the fold equation at the spots is
`partialFold_succ` (CITED) pointwise. The repair does not exclude honest
provers. -/
theorem linkOpened_honest {n : ℕ} (S : BindingCommitment Root' F (Fin m) Op)
    (q : Fin t → Fin m) (γs : ℕ → F) (f₀ : Fin m → F)
    (ms : Fin n → Fin m → F) (k : Fin n) :
    LinkOpened S q (S.commit (ms k)) (shiftedMsg S q γs f₀ ms (k : ℕ))
      (shiftedMsg S q γs f₀ ms ((k : ℕ) + 1)) (γs (k : ℕ)) := by
  refine ⟨fun j => ms k (q j), fun j => S.openAt (ms k) (q j),
    fun j => S.verifyOpen_commit _ _, fun j => ?_⟩
  show partialFold γs f₀ ms ((k : ℕ) + 1) (q j)
    = partialFold γs f₀ ms (k : ℕ) (q j) + γs (k : ℕ) * ms k (q j)
  rw [partialFold_succ]
  rfl

/-- **The fixed-pair re-attachment — increment pinning.** Under the
link-opening check, with the previous root's columns those of a codeword
`u` (what committed-column consistency + `bcsWord_committed` supply on the
analysis side) and the link root committing a codeword `w`, the `γ⁻¹`-read
increment at any NONZERO recorded challenge IS `w` — the word fixed in the
statement BEFORE any challenge existed. The adaptive-increment event
collapses to the fixed-pair alphabet: no continuation bound, no
RO-programming argument. What survives per slot is the zero-challenge draw
(`ρ = 0`, probability `1/|F|`) and the statement-fixed case that `w` itself
misses its link — both fixed-pair mass. -/
theorem linkOpened_increment_pinned (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) {d : ℕ} (hdt : d ≤ t) {q : Fin t → Fin m}
    (hq : Function.Injective (dom ∘ q)) {u w : Fin m → F}
    (hu : u ∈ reedSolomonCode dom d) (hw : w ∈ reedSolomonCode dom d)
    {π π' : BcsMsg Root' F Op t} (hπ : ∀ j, π.cols j = u (q j))
    {rt : Root'} (hrt : rt = S.commit w) {ρ : F} (hρ : ρ ≠ 0)
    (hlink : LinkOpened S q rt π π' ρ) :
    ρ⁻¹ • (bcsWord dom d q π' - bcsWord dom d q π) = w := by
  obtain ⟨lc, lo, hver, hcols⟩ := hlink
  have hlc : ∀ j, lc j = w (q j) := binding_columns S hrt hver
  have hπ' : ∀ j, π'.cols j = (u + ρ • w) (q j) := by
    intro j
    rw [hcols j, hπ j, hlc j]
    rfl
  have h1 : bcsWord dom d q π' = u + ρ • w :=
    recoverFromColumns_sound dom hdt hq
      (Submodule.add_mem _ hu (Submodule.smul_mem _ _ hw)) hπ'
  have h0 : bcsWord dom d q π = u :=
    recoverFromColumns_sound dom hdt hq hu hπ
  rw [h1, h0, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hρ, one_smul]

end LinkBinding

/-! ## The repaired per-slot obligation — [ORACLE-LOG-linked] -/

section LinkedProgram

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F)) (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F) (d : ℕ)
  (q : Fin t → Fin m)

/-- **The pin, in the extractor's vocabulary**: where the log answers the
round-`i` designated query with a nonzero `ρ` and the run passes the linked
check against a root committing `w`, `logIncrement` returns `w` — the
straightline log extractor reads the STATEMENT's committed link word, not
the adversary's programming. -/
theorem logIncrement_linked {s : ℕ} (hdt : d ≤ t)
    (hq : Function.Injective (dom ∘ q))
    (o : SrOutput (accReductionBcsShifted C foldRoot ch hm hch δs hδpos
      hδone S dom d q) s)
    (L : OracleLog (SrMove (accReductionBcsShifted C foldRoot ch hm hch δs
      hδpos hδone S dom d q) s) F)
    (i : Fin ch.length) {ρ : F} (hρ : ρ ≠ 0)
    (hans : OracleLog.answerOf L (o.query i.castSucc) = some ρ)
    {u w : Fin m → F} (hu : u ∈ reedSolomonCode dom d)
    (hw : w ∈ reedSolomonCode dom d)
    (hπ : ∀ j, (o.πs i.castSucc).cols j = u (q j))
    {rt : Root'} (hrt : rt = S.commit w)
    (hlink : LinkOpened S q rt (o.πs i.castSucc) (o.πs i.succ) ρ) :
    logIncrement C foldRoot ch hm hch δs hδpos hδone S dom d q o L i
      = some w := by
  unfold logIncrement
  rw [hans, Option.map_some]
  exact congrArg some
    (linkOpened_increment_pinned S dom hdt hq hu hw hπ hrt hρ hlink)

/-- **[ORACLE-LOG-linked] — the repaired per-slot obligation, STATED**
(house law: statement-first). The event of `OracleLogProgram` STRENGTHENED
by the deployment's link-opening clause at the recorded challenge (the
run must open the designated link root `wrt i` and pass the columnwise
fold check) — the clause whose absence `adaptiveViaLog_accRbrError_false`
exploits. Under it the hit-horn's increment is PINNED
(`linkOpened_increment_pinned`/`logIncrement_linked`): the per-slot mass
collapses to the zero-challenge draw plus the statement-fixed
misaligned-designation case, both fixed-pair.

ATLAS keystone fields (obligation):
* satisfiable: TODO realizer — rerun `gameSlotBound_proved`'s slot
  choreography (`splitAtGame` + the `hquery` pinning: on `hitAt` the
  recorded answer IS the tested coin) with the pinned increment: for
  aligned designations the event lands in `{ρ = 0}` (≤ `1/|F|`
  ≤ `accRbrError`); for misaligned designations the acceptance clause
  meets a statement-fixed falseness — the `accSound_rbr` family's event.
* teeth: the clause is load-bearing — the zero-tether adversary that makes
  the UNLINKED event certain (`progEvent_total`) has EMPTY linked event
  (`progLinked_zero`): its programmed increment cannot open against the
  honest link root (`progLinkOpened_refuted`, by `binding_columns`).
* premise-inhabitation: honest runs pass the added clause at every round
  (`linkOpened_honest`; F₅ instance `linkOpened_msgShifted_F5`), so the
  obligation does not demand the impossible. -/
def OracleLogProgramLinked (wrt : Fin ch.length → Root') (εslot : ℝ → ℝ) :
    Prop :=
  ∀ (s tq : ℕ)
    (P : SrProver (accReductionBcsShifted C foldRoot ch hm hch δs hδpos
      hδone S dom d q) s)
    (i : Fin ch.length) (j : Fin tq), ∀ δ ∈ Set.Ioo (0 : ℝ) δs,
    uniformProb ((Fin tq → F) × (Fin (ch.length + 1) → F)) (fun coins =>
      hitAt P i.castSucc j coins.1 ∧
      LinkOpened S q (wrt i) ((srOut P coins.1).πs i.castSucc)
        ((srOut P coins.1).πs i.succ)
        ((OracleLog.answerOf (srTrace P coins.1)
          ((srOut P coins.1).query i.castSucc)).getD 0) ∧
      (∃ (x' : AccClaim Root F (Fin m) r) (y' : Fin m → F),
        fiatShamir
            (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S
              dom d q) s
            (fsOracle (srOut P coins.1) (srFinalChal P coins.1 coins.2))
            (srOut P coins.1) = some (x', y') ∧
        RelaxedMem
          (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom
            d q).R'
          δ (srOut P coins.1).stmt.idx x' y' (srOut P coins.1).w') ∧
      ¬ LinkAligned C (srOut P coins.1).stmt.x ch i
        (shiftedLogExtractor C foldRoot ch hm hch δs hδpos hδone S dom d q s
          (srOut P coins.1) (srTrace P coins.1) i))
    ≤ εslot δ

end LinkedProgram

/-! ## Repair keystones on the landed F₅ chain -/

namespace OracleLogProgramExample

open RSExample LCExample AccExample ZkHidingExample ZkExtractionExample
  CommitExample AccRbrBcsExample AccRbrBcsShiftedExample AccSoundRbrExample

/-- **Premise-inhabitation, F₅**: the honest fold-root run passes the
link-opening check at every round, against the honest designation
`wrt k := S₅.commit (msEx k)` — `linkOpened_honest` on the landed chain. -/
theorem linkOpened_msgShifted_F5 (ρs : Fin 3 → ZMod 5) (k : Fin 2) :
    LinkOpened S₅ qPair (S₅.commit (msEx k)) (msgShifted ρs (k : ℕ))
      (msgShifted ρs ((k : ℕ) + 1))
      (padSched (fun i : Fin 2 => ρs i.castSucc) (k : ℕ)) :=
  linkOpened_honest S₅ qPair _ xWord msEx k

/-- The honest link-1 designation `1⃗` IS aligned — the repaired event's
designated word satisfies what the zero-tether adversary's programmed
increment misses. -/
theorem oneWord_aligned_F5 :
    LinkAligned (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) genesis goodChain
      (1 : Fin 2) oneWord :=
  ⟨Submodule.mem_top, fun _ => rfl⟩

/-- **Teeth — binding catches the programmer**: the zero-tether adversary's
consecutive roots CANNOT pass the link-opening check against the honest
link-1 root at its own recorded challenge: binding pins the opened columns
to `1⃗`'s, and the fold equation demands `2 + ρ = 1 + ρ` — refuted for
every `ρ`. The clause is load-bearing at exactly the run that killed the
unlinked statement. -/
theorem progLinkOpened_refuted (c : Fin 1 → ZMod 5) :
    ¬ LinkOpened S₅ qPair (S₅.commit oneWord)
        ((srOut progPrv c).πs (Fin.castSucc (1 : Fin 2)))
        ((srOut progPrv c).πs (Fin.succ (1 : Fin 2))) (c 0) := by
  rintro ⟨lc, lo, hver, hcols⟩
  have hlc : ∀ j, lc j = oneWord (qPair j) := binding_columns S₅ rfl hver
  have h : (2 + c 0) * oneWord (qPair 0)
      = oneWord (qPair 0) + c 0 * lc 0 := hcols 0
  rw [hlc 0, show oneWord (qPair 0) = 1 from rfl, mul_one, mul_one] at h
  exact absurd (add_right_cancel h) (by decide)

/-- **The repaired per-slot event for the zero-tether adversary is EMPTY**
— probability 0, not merely `≤ 1/|F|`: the linked clause at the recorded
answer contradicts the run outright (`progLinkOpened_refuted`). The
repaired obligation survives, with room, the exact adversary that made the
unrepaired event certain. -/
theorem progLinked_zero (δ : ℝ) :
    uniformProb ((Fin 1 → ZMod 5) × (Fin 3 → ZMod 5)) (fun coins =>
      hitAt progPrv (Fin.castSucc (1 : Fin 2)) (0 : Fin 1) coins.1 ∧
      LinkOpened S₅ qPair (S₅.commit oneWord)
        ((srOut progPrv coins.1).πs (Fin.castSucc (1 : Fin 2)))
        ((srOut progPrv coins.1).πs (Fin.succ (1 : Fin 2)))
        ((OracleLog.answerOf (srTrace progPrv coins.1)
          ((srOut progPrv coins.1).query
            (Fin.castSucc (1 : Fin 2)))).getD 0) ∧
      (∃ (x' : AccClaim (ZMod 5) (ZMod 5) (Fin 4) 1) (y' : Fin 4 → ZMod 5),
        fiatShamir accReductionBcsShifted_F5 0
            (fsOracle (srOut progPrv coins.1)
              (srFinalChal progPrv coins.1 coins.2))
            (srOut progPrv coins.1) = some (x', y') ∧
        RelaxedMem accReductionBcsShifted_F5.R' δ
          (srOut progPrv coins.1).stmt.idx x' y'
          (srOut progPrv coins.1).w') ∧
      ¬ LinkAligned (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
        (srOut progPrv coins.1).stmt.x goodChain (1 : Fin 2)
        (shiftedLogExtractor (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
          linRoot goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
          (by norm_num) S₅ dom₅ 2 qPair 0
          (srOut progPrv coins.1) (srTrace progPrv coins.1) (1 : Fin 2))) = 0 := by
  refine uniformProb_false ?_
  rintro ⟨c, dd⟩ ⟨-, hlink, -, -⟩
  have hgetD : (OracleLog.answerOf (srTrace progPrv c)
      ((srOut progPrv c).query (Fin.castSucc (1 : Fin 2)))).getD 0 = c 0 := by
    rw [progAnswer]
    rfl
  rw [hgetD] at hlink
  exact progLinkOpened_refuted c hlink

end OracleLogProgramExample

/-! ## Residual obligation — prose, not a stub

**What CLOSED here.** `[ORACLE-LOG-program]` is SETTLED — negatively, with
teeth, in the house's `OB2_depth_composition_false` tradition. The
zero-tether adversary `progPrv` (ONE query, on the landed F₅ chain) makes
the stated per-slot event hold on EVERY coin outcome (`progEvent_total`):
it reads the round-1 challenge off its own query, recommits `h₂` as the
codeword solving the aggregate equation exactly, and leaves the log-read
round-1 increment `ρ⁻¹·(1+ρ)•1⃗` missing the link target at all five
challenge values (kernel-checked). Consequences, machine-checked:
`oracleLogProgram_forces_one` (any admissible `εslot` is ≥ 1 on the whole
window), `oracleLogProgram_accRbrError_false` (the intended per-slot price
`1/|F|` is false), and — the headline — `adaptiveViaLog_accRbrError_false`:
the route target `adaptiveIncrement_sound_via_log` at `εlog = accRbrError`
is FALSE on the landed instance (`1 ≰ (1+3)·(1/5)`). The RO-programming
continuation bound the residual asked to prove does not exist: the shifted
verifier's acceptance never reads the intermediate roots (only openings,
the genesis anchor, and the LAST word against the aggregate), so the
programmed increment is free. `[ACC-rbr-bcs-shifted-resid]`(a) route (i)
CANNOT close over `accReductionBcsShifted` as landed — the reduction
under-specifies the deployed verifier, and the diagnosis that "the
acceptance clause at the END of the run must pay" was WRONG: it pays only
for the telescoped sum, every summand of which is committed after its own
challenge.

**The repair, and what it buys (proved).** The deployment's accumulation
verifier opens the incoming LINK's word from the link's own root and
spot-checks the fold columnwise — `LinkOpened`, the clause
`accReductionBcsShifted.verify` omits. Proved here: the honest shifted run
passes it at every round (`linkOpened_honest`, F₅ instance
`linkOpened_msgShifted_F5`); under it + binding the log-read increment at
any nonzero recorded challenge IS the link's committed word
(`linkOpened_increment_pinned`, extractor form `logIncrement_linked`) — a
word fixed in the statement BEFORE all challenges, so the adaptive event
collapses back to the fixed-pair alphabet; and the zero-tether adversary
DIES against it (`progLinkOpened_refuted` — binding forces `2+ρ = 1+ρ`;
`progLinked_zero` — its repaired event is EMPTY). The horn split needed by
any composition survives and is proved generically (`logSlot_cover`).

**[ORACLE-LOG-linked]** — what remains, stated precisely
(`OracleLogProgramLinked`, the formal Prop):

* the repaired per-slot bound: rerun `gameSlotBound_proved`'s slot
  choreography (`splitAtGame`; on `hitAt` the recorded answer IS the tested
  coin — `hitBad_fibre_le`'s `hquery` pinning) with the pinned increment.
  For an ALIGNED designation (`LinkAligned` at `wrt i`'s word, the deployed
  honest-chain regime) the event lands inside `{ρ = 0}` — per-slot mass
  `1/|F| ≤ accRbrError`. For a MISALIGNED designation the acceptance must
  survive a statement-fixed falseness — the `accSound_rbr` family's event,
  now genuinely fixed-pair. Both horns are Depth-scale bookkeeping over
  landed machinery, NOT a missing theory — the refutation removed the
  phantom "continuation bound" and the pin replaced it with fixed pairs.
* the fresh horn: unchanged by the repair — the extractor reads `0`
  (`logIncrement_none_of_unqueried`, CITED) and the challenge is the
  output-independent fresh coin (`unqueried_chal_fresh`, CITED); for a
  zero-target link the event is empty, else the aggregate's affine
  `ρ_i`-dependence plus unique decoding pins at most one bad draw —
  `1/|F|`. Composition: `logSlot_cover` + the `(t + k)` union.
* upstream surgery, named: `accReductionBcsShifted` itself should GROW the
  link-opening check (message alphabet carries the link openings; verify
  conjoins `LinkOpened` per round) — the derived-path law says the repaired
  verifier replaces the twin, and `accRbrKnowledgeSoundBcsShifted` /
  route (ii) must be re-read against it: the SAME hole (acceptance blind to
  intermediate roots) afflicts any statement whose event uses the landed
  verify. Not attempted here; named as the follow-on carve.
* inherited unchanged: the shifted state design
  (`[ACC-rbr-bcs-shifted-resid]`(b)), `[ZK-RBR-extract]` lemma A, and the
  floor `[FS-ROM]`/`[COMMIT-CR]`/`hPG` — consumed, never claimed.

**Honest assessment.** The deployed-ZK adaptive-increment bound is NOT
closed, and could never have been closed along the diagnosed route: the
per-slot lemma it reduced to is false, machine-checked. That is the real
finding — a wrong statement caught BEFORE proof effort sank into it, per
the audit discipline. The route forward is now well-posed: the link-opening
clause restores the fixed-pair structure (`linkOpened_increment_pinned` is
the load-bearing new theorem), the refuting adversary certifies the clause
is exactly the missing tether, and `[ORACLE-LOG-linked]` carries the
remaining mass — fixed-pair bookkeeping, not RO-programming.

## Ledger

* `uniformProb_eq_one` — PROVED: certain events have probability 1.
* `logSlot_cover` — PROVED (generic): every round's designated query is
  fresh or first-hit at some slot — the surviving cover skeleton.
* `progPrv` (+ `msgOf`, `progMsgs`, `progOut`, `progQry`) — BUILT: the
  one-query zero-tether adversary on the landed F₅ chain.
* `progHit` / `progChal1` / `progAnswer` / `progLogIncrement` /
  `progExtract` / `progAggSat` / `progVerify` / `progMisaligned` /
  `progEvent_total` — PROVED: the run hits at slot 0, the recorded answer
  is the fold challenge, acceptance holds on every draw, and the log-read
  increment misses link 1 at all five challenge values (kernel-checked).
* `oracleLogProgram_forces_one` / `oracleLogProgram_accRbrError_false` —
  PROVED: `[ORACLE-LOG-program]` is refutable at every `εslot < 1`; the
  intended `accRbrError` price is false.
* `adaptiveViaLog_accRbrError_false` — PROVED, the headline: the route
  target `adaptiveIncrement_sound_via_log` at `accRbrError` is FALSE on
  the landed instance.
* `LinkOpened` — DEFINED: the deployment's link-root opening + columnwise
  fold check, the missing clause.
* `linkOpened_honest` (+ `linkOpened_msgShifted_F5`) — PROVED: honest runs
  pass the check at every round.
* `linkOpened_increment_pinned` / `logIncrement_linked` — PROVED: under
  the check + binding, the log-read increment at a nonzero recorded
  challenge IS the statement-committed link word — the fixed pair
  re-attached.
* `progLinkOpened_refuted` / `progLinked_zero` (+ `oneWord_aligned_F5`) —
  PROVED (teeth): the zero-tether adversary's repaired event is EMPTY.
* `OracleLogProgramLinked` — STATED (`[ORACLE-LOG-linked]`,
  statement-first Prop with ATLAS fields): the repaired per-slot
  obligation, the new sharp residual.

`#print axioms` on `logSlot_cover`, `progEvent_total`,
`oracleLogProgram_accRbrError_false`, `adaptiveViaLog_accRbrError_false`,
`linkOpened_honest`, `linkOpened_increment_pinned`, `logIncrement_linked`,
`progLinkOpened_refuted`, `progLinked_zero`: `propext`,
`Classical.choice`, `Quot.sound` — no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage
