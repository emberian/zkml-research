/-
# Selvage.OracleLogLinked — [ORACLE-LOG-linked]: the audit finding (the repaired
per-slot statement is STILL refutable — the statement↔designation channel) and
the guarded repair, CLOSED at the sharp per-slot price `1/|F|`; the linked
reduction GROWN per the derived-path law.

`Selvage/OracleLogProgram.lean` refuted `[ORACLE-LOG-program]` (the increment was
never tied to the chain's committed link word), built the repair clause
`LinkOpened`, proved the fixed-pair re-attachment
(`linkOpened_increment_pinned`), and stated the repaired per-slot obligation
`OracleLogProgramLinked` — `[ORACLE-LOG-linked]`. The task here was to prove it
and close the deployed-ZK adaptive bound for the linked reduction.

**Audit finding first (house precedent: `OB2_depth_composition_false`,
`oracleLogProgram_accRbrError_false`): `OracleLogProgramLinked` is REFUTABLE
at the intended price — even at the HONEST designation family.** The repaired
event tests `¬ LinkAligned C (srOut P).stmt.x ch i (extracted)` — alignment at
the ADVERSARY'S OWN statement's channel functionals — against a CALLER-fixed
designation `wrt i`, and NO clause ties the two: the previous lane's repair
re-attached increment↔commitment but left statement↔designation open. The
landed `slotBad`/`HitBad` events (`Selvage/Depth.lean`) always carry a statement
guard (`o.stmt ∈ Z`); both oracle-log per-slot statements dropped it. The
two-query adversary `alnPrv` (built below on the landed F₅ chain) exploits
exactly this:

* its statement `alnClaim` carries the functional `alnW = proj 0` with
  `alnW (msEx 0) = 2 ≠ 0` — the honest designated link-0 word MISALIGNS
  against the adversary's own channel (while remaining perfectly aligned for
  the honest `genesis`: `msEx_linkAligned`, CITED);
* it queries the round-0 prefix (slot 0, answer `ρ₀`), commits
  `h₁ := xWord + ρ₀ • msEx 0` — which PASSES the link-opening check against
  the honest root `S₅.commit (msEx 0)` on the nose — queries the round-1
  prefix (slot 1, answer `ρ₁`), and solves the aggregate exactly with the
  last message `ρ₁ • 1⃗` (link-0's target is 0, so `ρ₀` is inert in the
  target; `alnW (ρ₁ • 1⃗) = ρ₁ = 0 + ρ₀·0 + ρ₁·1`);
* the log-read increment at round 0 is `ρ₀⁻¹·ρ₀ • msEx 0 = msEx 0` for every
  `ρ₀ ≠ 0` — misaligned FOR THE ADVERSARY'S STATEMENT by construction.

So the repaired event holds whenever `ρ₀ ≠ 0`: any admissible `εslot` is
forced `≥ 4/5` (`oracleLogProgramLinked_forces`), and `[ORACLE-LOG-linked]` at
`εslot = accRbrError = 1/5` is FALSE (`oracleLogProgramLinked_accRbrError_false`)
— at the honest designation `wrt k = S₅.commit (msEx k)`, on the landed chain.
Note the tether itself held: `alnPrv` PASSES `LinkOpened` honestly. The hole
is one level up, in what "misaligned" is measured against.

**The guarded repair — and it CLOSES, at the sharp price.** Two new generic
theorems make the guarded per-slot bound a short argument:

* `recoverFromColumns_line` + `linkOpened_increment_pinned_free` — erasure
  recovery (`Lagrange.interpolate` + `evalOnDomain`, both linear maps) is
  AFFINE in the opened columns, so the landed pin's codeword-columns premise
  on the PREVIOUS message is not needed: under `LinkOpened` + binding alone,
  at any nonzero recorded challenge, the `ρ⁻¹`-difference of the two
  synthesized words IS the designated codeword — junk previous columns
  included. (Supersedes `linkOpened_increment_pinned`'s `hu`/`hπ` premises;
  the landed lemma remains for the honest-analysis route.)
* `hitAt_answerOf` — on the hit horn the recorded answer IS the tested game
  coin: the `hquery` pinning inside `hitBad_fibre_le` (CITED), made a
  portable, fibre-free citation via the `runFrom` machinery.

`OracleLogLinkedAligned` is `OracleLogProgramLinked` with designations given
as WORDS `wv` and ONE added conjunct — the statement guard
`LinkAligned C (srOut P).stmt.x ch i (wv i)` (the `Z`-clause in its sharpest
per-round form; `Z := {st | ∀ i, LinkAligned C st.x ch i (wv i)}` is the
deployed statement set, inhabited by the honest chain: `msEx_linkAligned`).
Under the guard the event is CONTAINED in `{coins | c_j = 0}`: at `c_j ≠ 0`
the extracted increment is pinned to `wv i` (`hitAt_answerOf` +
`linkOpened_increment_pinned_free`), which the guard says IS aligned —
contradicting the event's misalignment conjunct. One coin coordinate pinned:
`uniformProb ≤ 1/|F|` (`splitProd1` + `uniformProb_prod_le`, CITED). That is
`oracleLogLinkedAligned_proved` — the hit-horn per-slot mass of the deployed-ZK
adaptive bound, CLOSED at `1/|F| ≤ accRbrError`
(`oracleLogLinkedAligned_accRbrError`), sharper than the budgeted price.

**The reduction grows the clause (derived-path law).**
`accReductionBcsShiftedLinked` = `accReductionBcsShifted` with `verify`
strengthened by the per-round link-opening conjunct against the designated
words — the deployment's actual check, superseding the twin (the unlinked
reduction remains upstream as the refutation's carrier; new work targets the
linked one). `linked_verify_strengthens` (acceptance ⟹ unlinked acceptance,
same output, + every round's `LinkOpened`) is the composition's discharge
lemma; `linked_verify_honest` (completeness, CITING `shifted_verify_honest` +
`linkOpened_honest` — nothing re-derived) shows the growth excludes no honest
prover; `progMsgs_linked_rejected` (teeth) shows the zero-tether refuter of
`[ORACLE-LOG-program]` now DIES inside the verifier itself
(`progLinkOpened_refuted`'s computation, CITED, re-run at the deployed
designation `msEx 1`: binding forces `2 + ρ = 1 + ρ`).
-/
import Selvage.OracleLogProgram
import Selvage.Depth
import Selvage.AccRbrBcsShifted
import Selvage.AccSoundRbr

namespace Minidregg.Selvage

/-! ## Counting: complement, and one pinned coin coordinate -/

section Counting

lemma uniformProb_not {C : Type} [Fintype C] [Nonempty C] (p : C → Prop) :
    uniformProb C (fun c => ¬ p c) = 1 - uniformProb C p := by
  classical
  unfold uniformProb
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl, Nat.cast_sub (Fintype.card_subtype_le p),
    sub_div, div_self (by exact_mod_cast Fintype.card_ne_zero)]

lemma uniformProb_eq_single {C : Type} [Fintype C] (a : C) :
    uniformProb C (fun b => b = a) = 1 / (Fintype.card C : ℝ) := by
  classical
  unfold uniformProb
  rw [show Nat.card {b : C // b = a} = 1 by
    rw [Nat.card_eq_fintype_card]; exact Fintype.card_subtype_eq a,
    Nat.cast_one]

/-- One designated COIN coordinate of a `(coins × side)` product takes a fixed
value with probability at most `1/|F|` — `splitProd1` (CITED,
`Selvage/Depth.lean`) slices the coordinate out, `uniformProb_prod_le` conditions
on everything else. -/
lemma uniformProb_prod_coord_le {F : Type} [Fintype F] {n : ℕ}
    {γ : Type} [Fintype γ] (j : Fin n) (a : F) :
    uniformProb ((Fin n → F) × γ) (fun x => x.1 j = a)
      ≤ 1 / (Fintype.card F : ℝ) := by
  classical
  have hkey := uniformProb_equiv (splitProd1 (β := F) (γ := γ) j)
    (fun y : (({i : Fin n // i ≠ j} → F) × γ) × F => y.2 = a)
  rw [show (fun x : (Fin n → F) × γ => x.1 j = a)
      = fun x => (splitProd1 (β := F) (γ := γ) j x).2 = a from rfl, hkey]
  refine uniformProb_prod_le (by positivity) fun w => ?_
  exact le_of_eq (uniformProb_eq_single a)

end Counting

/-! ## Erasure recovery is affine in the columns — the junk-tolerant pin -/

section ErasureLinear

variable {ι : Type*} {F : Type*} [Field F]

/-- **Erasure recovery is affine in the opened columns.** `recoverFromColumns`
interpolates through the first `d` column values (`Lagrange.interpolate`, a
linear map in the values) and evaluates on the domain (`evalOnDomain`, a
linear map) — so it carries `cols + ρ·cols'` to `word + ρ • word'`. This is
what frees the increment pin from any premise on the PREVIOUS message's
columns: the fold-check offset passes through the synthesis exactly, junk
columns included. -/
theorem recoverFromColumns_line (dom : ι ↪ F) (d : ℕ) {t : ℕ}
    (opened : Fin t → ι) (vals vals' : Fin t → F) (ρ : F) :
    recoverFromColumns dom d opened (fun j => vals j + ρ * vals' j)
      = recoverFromColumns dom d opened vals
        + ρ • recoverFromColumns dom d opened vals' := by
  unfold recoverFromColumns
  by_cases h : d ≤ t
  · rw [dif_pos h, dif_pos h, dif_pos h]
    have hv : ((fun j => vals j + ρ * vals' j) ∘ Fin.castLE h)
        = (vals ∘ Fin.castLE h) + ρ • (vals' ∘ Fin.castLE h) := by
      funext j
      simp [smul_eq_mul]
    rw [hv, map_add, map_smul, map_add, map_smul]
  · rw [dif_neg h, dif_neg h, dif_neg h]
    simp

end ErasureLinear

section LinkPinFree

variable {Root' Op : Type} {F : Type} [Field F] {m t : ℕ}

/-- **The increment pin, freed of the previous-message premise.** Under the
link-opening check + binding, with the designated root committing a codeword
`w`, the `ρ⁻¹`-read increment at any NONZERO challenge IS `w` — with NO
hypothesis on the previous message's columns (they may be junk): the fold
equation offsets the columns by `ρ · w∘q`, and the synthesis is affine
(`recoverFromColumns_line`), so the offset passes through as `ρ • w` exactly.
Supersedes `linkOpened_increment_pinned`'s `hu`/`hπ` premises on the analysis
side; `binding_columns` + `recoverFromColumns_sound` CITED. -/
theorem linkOpened_increment_pinned_free
    (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F) {d : ℕ}
    (hdt : d ≤ t) {q : Fin t → Fin m} (hq : Function.Injective (dom ∘ q))
    {w : Fin m → F} (hw : w ∈ reedSolomonCode dom d)
    {π π' : BcsMsg Root' F Op t} {rt : Root'} (hrt : rt = S.commit w)
    {ρ : F} (hρ : ρ ≠ 0) (hlink : LinkOpened S q rt π π' ρ) :
    ρ⁻¹ • (bcsWord dom d q π' - bcsWord dom d q π) = w := by
  obtain ⟨lc, lo, hver, hcols⟩ := hlink
  have hlc : ∀ j, lc j = w (q j) := binding_columns S hrt hver
  have hπ' : π'.cols = fun j => π.cols j + ρ * (w ∘ q) j := by
    funext j
    rw [hcols j, hlc j]
    rfl
  have hsw : recoverFromColumns dom d q (w ∘ q) = w :=
    recoverFromColumns_sound dom hdt hq hw fun _ => rfl
  have hword : bcsWord dom d q π' = bcsWord dom d q π + ρ • w := by
    show recoverFromColumns dom d q π'.cols = _
    rw [hπ', recoverFromColumns_line dom d q π.cols (w ∘ q) ρ, hsw]
    rfl
  rw [hword, add_sub_cancel_left, smul_smul, inv_mul_cancel₀ hρ, one_smul]

end LinkPinFree

/-! ## On the hit horn the recorded answer IS the tested coin -/

section HitPinned

open Classical

variable {r : Reduction} {s t : ℕ}

/-- **The hit-horn pinning, portable**: if the output's round-`a` designated
query was FIRST answered at game slot `j` (`hitAt`), the log's answer to it is
`some (c j)` — the fresh coin of that slot. This is the `hquery` content of
`hitBad_fibre_le` (CITED, `Selvage/Depth.lean`), extracted from its fibre
decomposition into a standalone citation via the `runFrom` machinery: split
the coin list at `j`, note the step-`j` move is fresh there (`hitAt`
minimality), so `stepOnce` records `c j`, and first-match resolution never
changes (`find?_eq_none_of_forall_ne` on the past + head match). -/
theorem hitAt_answerOf (P : SrProver r s) {a : Fin r.k} {j : Fin t}
    {c : Fin t → r.Chal} (h : hitAt P a j c) :
    OracleLog.answerOf (srTrace P c) ((srOut P c).query a) = some (c j) := by
  have h' : (srTrace P c).findIdx?
      (fun e => decide (e.1 = (srOut P c).query a)) = some (j : ℕ) := h
  rw [List.findIdx?_eq_some_iff_getElem] at h'
  obtain ⟨hjlt, hpj, hmin⟩ := h'
  -- split the coin list at position j
  have hlen : (j : ℕ) < (List.ofFn c).length := by
    rw [List.length_ofFn]
    exact j.2
  have hget : (List.ofFn c)[(j : ℕ)]'hlen = c j := by
    rw [List.getElem_ofFn]
  have hsplit : List.ofFn c = (List.ofFn c).take (j : ℕ)
      ++ c j :: (List.ofFn c).drop ((j : ℕ) + 1) := by
    conv_lhs => rw [← List.take_append_drop (j : ℕ) (List.ofFn c)]
    rw [List.drop_eq_getElem_cons hlen, hget]
  set Lp := runFrom P [] ((List.ofFn c).take (j : ℕ)) with hLp
  have hLplen : Lp.length = (j : ℕ) := by
    rw [hLp, runFrom_length, List.length_take, List.length_ofFn,
      Nat.min_eq_left (le_of_lt j.2)]
    simp
  set mv := P.move (Lp.map Prod.snd) with hmv
  obtain ⟨M, hM⟩ := runFrom_eq_append P ((List.ofFn c).drop ((j : ℕ) + 1))
    (stepOnce P Lp (c j))
  have htr : srTrace P c = Lp ++ ((mv,
      match Lp.find? (fun e => decide (e.1 = mv)) with
      | some e => e.2
      | none => c j) :: M) := by
    rw [srTrace_eq_runFrom]
    conv_lhs => rw [hsplit]
    rw [runFrom_append, runFrom_cons, ← hLp, hM, stepOnce_eq, ← hmv,
      List.append_assoc, List.singleton_append]
    rfl
  -- no past entry made the hit query (hitAt minimality)
  have hclean : ∀ e ∈ Lp, e.1 ≠ (srOut P c).query a := by
    intro e he heq
    obtain ⟨n, hn, hgetn⟩ := List.mem_iff_getElem.mp he
    have hnj : n < (j : ℕ) := by
      rw [hLplen] at hn
      exact hn
    have hmn := hmin n hnj
    have hTn : (srTrace P c)[n]'(by
        rw [srTrace_length]
        exact lt_trans hnj j.2) = Lp[n]'hn := by
      simp only [htr]
      exact List.getElem_append_left hn
    rw [hTn, hgetn] at hmn
    simp only [decide_eq_true_eq] at hmn
    exact hmn heq
  -- the step-j entry is the hit query, answered by the fresh coin
  have hgetj : (srTrace P c)[(j : ℕ)]'hjlt = (mv,
      match Lp.find? (fun e => decide (e.1 = mv)) with
      | some e => e.2
      | none => c j) := by
    simp only [htr]
    rw [List.getElem_append_right (by omega)]
    have hidx : (j : ℕ) - Lp.length = 0 := by omega
    simp only [hidx, List.getElem_cons_zero]
  have hmveq : mv = (srOut P c).query a := by
    have h1 := of_decide_eq_true hpj
    rw [hgetj] at h1
    exact h1
  have hfind : Lp.find? (fun e => decide (e.1 = mv)) = none := by
    refine find?_eq_none_of_forall_ne ?_
    intro e he
    rw [hmveq]
    exact hclean e he
  have htr2 : srTrace P c = Lp ++ ((mv, c j) :: M) := by
    rw [htr, hfind]
  show ((srTrace P c).find?
      (fun e => decide (e.1 = (srOut P c).query a))).map Prod.snd
    = some (c j)
  rw [htr2, List.find?_append, find?_eq_none_of_forall_ne hclean,
    Option.none_or, List.find?_cons_of_pos (by simp [hmveq])]
  rfl

end HitPinned

/-! ## The guarded per-slot obligation — [ORACLE-LOG-linked-aligned], PROVED -/

section LinkedAligned

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F)) (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F) (d : ℕ)
  (q : Fin t → Fin m)

/-- **[ORACLE-LOG-linked-aligned] — the GUARDED per-slot obligation.**
`OracleLogProgramLinked` with the designations given as words `wv` (roots
`S.commit (wv i)`) and ONE added conjunct: the statement guard
`LinkAligned C (srOut P).stmt.x ch i (wv i)` — the run's own statement must
align with the designation it is scored against. This is the `Z`-clause the
landed `slotBad` (`Selvage/Depth.lean`) always carries and both oracle-log
per-slot statements dropped; its absence is exactly what
`oracleLogProgramLinked_accRbrError_false` exploits (an adversary choosing a
channel that misaligns the honest designation wins for free). Restricting to
`Z := {st | ∀ i, LinkAligned C st.x ch i (wv i)}` — the deployed statement
set, inhabited by the honest chain (`msEx_linkAligned`, CITED) — discharges
the guard in composition.

PROVED below (`oracleLogLinkedAligned_proved`) at `εslot = 1/|F|`: sharper
than the budgeted `accRbrError` (`oracleLogLinkedAligned_accRbrError`).

ATLAS keystone fields:
* satisfiable: `oracleLogLinkedAligned_proved` — the bound HOLDS, with the
  F₅ instance fired (`oracleLogLinkedAligned_F5`, price `1/5`);
* teeth: the guard is load-bearing at exactly the refuting adversary —
  `alnPrv`'s guarded event is EMPTY (`alnGuarded_zero`) while its unguarded
  event forces `εslot ≥ 4/5` (`oracleLogProgramLinked_forces`);
* premise-inhabitation: honest runs pass every non-guard conjunct's premise
  (`linkOpened_msgShifted_F5`, CITED) and the honest statement passes the
  guard (`msEx_linkAligned`, CITED). -/
def OracleLogLinkedAligned (wv : Fin ch.length → Fin m → F)
    (εslot : ℝ → ℝ) : Prop :=
  ∀ (s tq : ℕ)
    (P : SrProver (accReductionBcsShifted C foldRoot ch hm hch δs hδpos
      hδone S dom d q) s)
    (i : Fin ch.length) (j : Fin tq), ∀ δ ∈ Set.Ioo (0 : ℝ) δs,
    uniformProb ((Fin tq → F) × (Fin (ch.length + 1) → F)) (fun coins =>
      hitAt P i.castSucc j coins.1 ∧
      LinkAligned C (srOut P coins.1).stmt.x ch i (wv i) ∧
      LinkOpened S q (S.commit (wv i)) ((srOut P coins.1).πs i.castSucc)
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

/-- **The guarded per-slot bound HOLDS, at the sharp price `1/|F|`.** On the
event: `hitAt` pins the recorded answer to the tested coin `c_j`
(`hitAt_answerOf`); at `c_j ≠ 0` the link-opening conjunct pins the log-read
increment to the designated word `wv i` (`linkOpened_increment_pinned_free` —
no premise on the previous message), which the guard says IS aligned —
contradicting the misalignment conjunct. So the event is contained in
`{c_j = 0}`, one pinned coin coordinate: `uniformProb_prod_coord_le`. No
continuation bound, no RO programming, no per-fibre choreography — the
fixed-pair collapse the repair promised, delivered. -/
theorem oracleLogLinkedAligned_proved (hdt : d ≤ t)
    (hq : Function.Injective (dom ∘ q)) (wv : Fin ch.length → Fin m → F)
    (hwv : ∀ i, wv i ∈ reedSolomonCode dom d) :
    OracleLogLinkedAligned C foldRoot ch hm hch δs hδpos hδone S dom d q wv
      (fun _ => 1 / (Fintype.card F : ℝ)) := by
  intro s tq P i j δ hδ
  refine le_trans (uniformProb_mono ?_) (uniformProb_prod_coord_le j 0)
  rintro ⟨c, dd⟩ ⟨hhit, halign, hlink, -, hbad⟩
  show c j = 0
  by_contra hne
  have hans := hitAt_answerOf P hhit
  rw [show (OracleLog.answerOf (srTrace P c)
      ((srOut P c).query i.castSucc)).getD 0 = c j by rw [hans]; rfl] at hlink
  have hpin : shiftedLogExtractor C foldRoot ch hm hch δs hδpos hδone S dom
      d q s (srOut P c) (srTrace P c) i = wv i := by
    unfold shiftedLogExtractor logIncrement
    rw [hans, Option.map_some, Option.getD_some]
    exact linkOpened_increment_pinned_free S dom hdt hq (hwv i) rfl hne hlink
  rw [hpin] at hbad
  exact hbad halign

/-- The guarded bound at the budgeted price: `1/|F| ≤ accRbrError` whenever
`errstar` is nonnegative on the window — the per-slot mass fits the
`(t + k)·accRbrError` composition with room. -/
theorem oracleLogLinkedAligned_accRbrError (hdt : d ≤ t)
    (hq : Function.Injective (dom ∘ q)) (wv : Fin ch.length → Fin m → F)
    (hwv : ∀ i, wv i ∈ reedSolomonCode dom d) (errstar : ℝ → ℝ)
    (hstar : ∀ δ ∈ Set.Ioo (0 : ℝ) δs, 0 ≤ errstar δ) :
    OracleLogLinkedAligned C foldRoot ch hm hch δs hδpos hδone S dom d q wv
      (accRbrError F errstar) := by
  intro s tq P i j δ hδ
  refine le_trans (oracleLogLinkedAligned_proved C foldRoot ch hm hch δs
    hδpos hδone S dom d q hdt hq wv hwv s tq P i j δ hδ) ?_
  unfold accRbrError
  have := hstar δ hδ
  linarith

end LinkedAligned

/-! ## The reduction grows the clause — the derived-path repair -/

section LinkedReduction

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F)) (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F) (d : ℕ)
  (q : Fin t → Fin m)

open Classical in
/-- **The LINKED shifted reduction** — `accReductionBcsShifted` with its
verifier GROWN by the deployment's per-round link-opening check against the
designated link-word family `wv` (derived-path law: the reduction grows the
missing vocabulary; this verifier supersedes the unlinked twin, which remains
upstream as the refutation's carrier). Everything else — types, relations,
rounds, the aggregate/last-word output — is the shifted reduction's,
unchanged. -/
@[reducible] noncomputable def accReductionBcsShiftedLinked
    (wv : Fin ch.length → Fin m → F) : Reduction :=
  { accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d q with
    verify := fun _ A₀ f₀ πs ρs =>
      if (∀ i, ColsOpen S q (πs i)) ∧ (∀ j, (πs 0).cols j = f₀ (q j)) ∧
          ∀ i : Fin ch.length,
            LinkOpened S q (S.commit (wv i)) (πs i.castSucc) (πs i.succ)
              (ρs i.castSucc) then
        some (aggregate foldRoot
            (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
          bcsWord dom d q (πs (Fin.last ch.length)))
      else none }

/-- **Linked acceptance strengthens unlinked acceptance**: a run the linked
verifier accepts is accepted by the unlinked shifted verifier with the SAME
output, AND passes the link-opening check at every round — the discharge
lemma the `(t + k)` composition reads the added clause off with. -/
theorem linked_verify_strengthens (wv : Fin ch.length → Fin m → F)
    (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (πs : Fin (ch.length + 1) → BcsMsg Root' F Op t)
    (ρs : Fin (ch.length + 1) → F)
    {out : AccClaim Root F (Fin m) r × (Fin m → F)}
    (h : (accReductionBcsShiftedLinked C foldRoot ch hm hch δs hδpos hδone S
        dom d q wv).verify () A₀ f₀ πs ρs = some out) :
    (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d
        q).verify () A₀ f₀ πs ρs = some out ∧
      ∀ i : Fin ch.length,
        LinkOpened S q (S.commit (wv i)) (πs i.castSucc) (πs i.succ)
          (ρs i.castSucc) := by
  classical
  by_cases hc : (∀ i, ColsOpen S q (πs i)) ∧
      (∀ j, (πs 0).cols j = f₀ (q j)) ∧
      ∀ i : Fin ch.length, LinkOpened S q (S.commit (wv i)) (πs i.castSucc)
        (πs i.succ) (ρs i.castSucc)
  · rw [show (accReductionBcsShiftedLinked C foldRoot ch hm hch δs hδpos
        hδone S dom d q wv).verify () A₀ f₀ πs ρs
        = some (aggregate foldRoot
            (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
          bcsWord dom d q (πs (Fin.last ch.length))) from if_pos hc] at h
    refine ⟨?_, hc.2.2⟩
    rw [show (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S
        dom d q).verify () A₀ f₀ πs ρs
        = some (aggregate foldRoot
            (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
          bcsWord dom d q (πs (Fin.last ch.length))) from
      if_pos ⟨hc.1, hc.2.1⟩]
    exact h
  · rw [show (accReductionBcsShiftedLinked C foldRoot ch hm hch δs hδpos
        hδone S dom d q wv).verify () A₀ f₀ πs ρs = none from if_neg hc] at h
    exact absurd h (by simp)

/-- Unlinked acceptance + the per-round link openings ⟹ linked acceptance,
same output — the converse direction, carrying completeness. -/
theorem linked_verify_of_shifted (wv : Fin ch.length → Fin m → F)
    (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (πs : Fin (ch.length + 1) → BcsMsg Root' F Op t)
    (ρs : Fin (ch.length + 1) → F)
    {out : AccClaim Root F (Fin m) r × (Fin m → F)}
    (h : (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d
        q).verify () A₀ f₀ πs ρs = some out)
    (hlk : ∀ i : Fin ch.length,
      LinkOpened S q (S.commit (wv i)) (πs i.castSucc) (πs i.succ)
        (ρs i.castSucc)) :
    (accReductionBcsShiftedLinked C foldRoot ch hm hch δs hδpos hδone S dom
        d q wv).verify () A₀ f₀ πs ρs = some out := by
  classical
  by_cases hc : (∀ i, ColsOpen S q (πs i)) ∧ ∀ j, (πs 0).cols j = f₀ (q j)
  · rw [show (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S
        dom d q).verify () A₀ f₀ πs ρs
        = some (aggregate foldRoot
            (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
          bcsWord dom d q (πs (Fin.last ch.length))) from if_pos hc] at h
    rw [show (accReductionBcsShiftedLinked C foldRoot ch hm hch δs hδpos
        hδone S dom d q wv).verify () A₀ f₀ πs ρs
        = some (aggregate foldRoot
            (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
          bcsWord dom d q (πs (Fin.last ch.length))) from
      if_pos ⟨hc.1, hc.2, hlk⟩]
    exact h
  · rw [show (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S
        dom d q).verify () A₀ f₀ πs ρs = none from
      if_neg (fun hcc => hc ⟨hcc.1, hcc.2⟩)] at h
    exact absurd h (by simp)

/-- **Completeness — the growth excludes no honest prover**: the honest
shifted fold-root run passes the LINKED verifier at the honest designation
`wv := ms`, with the same output as the unlinked one.
`shifted_verify_honest` + `linkOpened_honest` CITED — nothing re-derived. -/
theorem linked_verify_honest (hdt : d ≤ t)
    (hq : Function.Injective (dom ∘ q)) (A₀ : AccClaim Root F (Fin m) r)
    {f₀ : Fin m → F} {ms : Fin ch.length → Fin m → F}
    (hf₀ : f₀ ∈ reedSolomonCode dom d)
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    (ρs : Fin (ch.length + 1) → F) :
    (accReductionBcsShiftedLinked C foldRoot ch hm hch δs hδpos hδone S dom
        d q ms).verify () A₀ f₀
        (fun c => shiftedMsg S q
          (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms (c : ℕ)) ρs
      = some (aggregate foldRoot
            (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
          flatFold (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms)
    := by
  refine linked_verify_of_shifted C foldRoot ch hm hch δs hδpos hδone S dom
    d q ms A₀ f₀ _ ρs
    (shifted_verify_honest C foldRoot ch hm hch δs hδpos hδone S dom q hdt
      hq A₀ hf₀ hms ρs) ?_
  intro i
  have h := linkOpened_honest S q
    (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms i
  rw [padSched_lt _ i.isLt] at h
  exact h

end LinkedReduction

/-! ## Keystones on the landed F₅ chain: the refuter, the guard's teeth, the
linked reduction fired -/

namespace OracleLogLinkedExample

open RSExample LCExample AccExample ZkHidingExample ZkExtractionExample
  CommitExample AccRbrBcsExample AccRbrBcsShiftedExample AccSoundRbrExample
  AccRbrInstanceExample OracleLogProgramExample

/-! ### The statement-channel refuter `alnPrv` -/

/-- The misaligning functional: coordinate 0. `alnW (msEx 0) = 2 ≠ 0` (the
honest designated link-0 word misses ITS target through THIS channel) while
`alnW oneWord = 1` (the aggregate stays exactly solvable). -/
def alnW : (Fin 4 → ZMod 5) →ₗ[ZMod 5] ZMod 5 := LinearMap.proj 0

/-- **The misaligning statement**: genesis claim with channel `(alnW, 0)`. A
legitimate adversarial statement — nothing in `accReductionBcsShifted` (or its
linked strengthening) constrains the claim channel — whose functionals
misalign the HONEST designation `msEx 0` against link 0's target `0`. -/
def alnClaim : AccClaim (ZMod 5) (ZMod 5) (Fin 4) 1 :=
  ⟨0, fun _ => (alnW, 0)⟩

/-- The refuter's message family at recorded challenges `(ρ₀, ρ₁)`: honest
genesis anchor, the honestly LINK-OPENED first fold `h₁ = xWord + ρ₀ • msEx 0`
(this run PASSES the round-0 link-opening check against the honest root — the
tether is not what it beats), and the aggregate-solving last word `ρ₁ • 1⃗`. -/
noncomputable def alnMsgs (ρ₀ ρ₁ : ZMod 5) :
    ℕ → BcsMsg (Fin 4 → ZMod 5) (ZMod 5) Unit 2
  | 0 => msgOf xWord
  | 1 => msgOf (xWord + ρ₀ • msEx 0)
  | _ => msgOf (ρ₁ • oneWord)

/-- The refuter's output: the misaligning statement, the three-message
family, no salts, junk candidate witness. -/
noncomputable def alnOut (ρ₀ ρ₁ : ZMod 5) :
    SrOutput accReductionBcsShifted_F5 0 :=
  ⟨⟨(), alnClaim, xWord⟩, fun c => alnMsgs ρ₀ ρ₁ (c : ℕ), fun _ => Fin.elim0,
    fun _ => 0⟩

/-- The round-0 designated prefix query — independent of both challenges. -/
noncomputable def alnQ0 : SrMove accReductionBcsShifted_F5 0 :=
  (alnOut 0 0).query (Fin.castSucc (0 : Fin 2))

/-- The round-1 designated prefix query — depends on `ρ₀` only. -/
noncomputable def alnQ1 (ρ₀ : ZMod 5) : SrMove accReductionBcsShifted_F5 0 :=
  (alnOut ρ₀ 0).query (Fin.castSucc (1 : Fin 2))

theorem alnQ0_ne (ρ₀ : ZMod 5) : alnQ0 ≠ alnQ1 ρ₀ := by
  intro h
  have h1 : alnQ0.pfx.length = 1 := by
    simpa using SrOutput.query_pfx_length (alnOut 0 0)
      (Fin.castSucc (0 : Fin 2))
  have h2 : (alnQ1 ρ₀).pfx.length = 2 := by
    simpa using SrOutput.query_pfx_length (alnOut ρ₀ 0)
      (Fin.castSucc (1 : Fin 2))
  rw [h, h2] at h1
  exact absurd h1 (by norm_num)

/-- **The statement-channel refuter**: query the round-0 prefix, fold
`h₁` honestly from the answer, query the round-1 prefix, solve the aggregate
with the last word. Two queries — it sees every challenge the aggregate
reads. -/
noncomputable def alnPrv : SrProver accReductionBcsShifted_F5 0 where
  move := fun resp => match resp with
    | [] => alnQ0
    | ρ₀ :: _ => alnQ1 ρ₀
  out := fun resp => alnOut (resp.getD 0 0) (resp.getD 1 0)

/-- The game trace: the two distinct prefix queries, answered by the two
fresh coins in order. -/
theorem alnTrace (c : Fin 2 → ZMod 5) :
    srTrace alnPrv c = [(alnQ0, c 0), (alnQ1 (c 0), c 1)] := by
  rw [srTrace_eq_foldl, show List.finRange 2 = [(0 : Fin 2), 1] from rfl,
    List.foldl_cons, List.foldl_cons, List.foldl_nil,
    show stepFn alnPrv c [] 0 = [(alnQ0, c 0)] from rfl, stepFn_eq,
    show alnPrv.move (List.map Prod.snd [(alnQ0, c 0)]) = alnQ1 (c 0)
      from rfl,
    List.find?_cons_of_neg (by simpa using alnQ0_ne (c 0)), List.find?_nil]
  rfl

theorem alnSrOut (c : Fin 2 → ZMod 5) :
    srOut alnPrv c = alnOut (c 0) (c 1) := by
  show alnPrv.out ((srTrace alnPrv c).map Prod.snd) = alnOut (c 0) (c 1)
  rw [alnTrace]
  rfl

theorem alnOut_query0 (ρ₀ ρ₁ : ZMod 5) :
    (alnOut ρ₀ ρ₁).query (Fin.castSucc (0 : Fin 2)) = alnQ0 := rfl

theorem alnOut_query1 (ρ₀ ρ₁ : ZMod 5) :
    (alnOut ρ₀ ρ₁).query (Fin.castSucc (1 : Fin 2)) = alnQ1 ρ₀ := rfl

/-- **The hit**: the round-0 designated query is first answered at game slot
0 — on every coin outcome. -/
theorem alnHit (c : Fin 2 → ZMod 5) :
    hitAt alnPrv (Fin.castSucc (0 : Fin 2)) (0 : Fin 2) c := by
  unfold hitAt
  rw [alnTrace, alnSrOut, alnOut_query0]
  simp [List.findIdx?_cons]

theorem alnAnswer0 (c : Fin 2 → ZMod 5) :
    OracleLog.answerOf (srTrace alnPrv c)
      ((srOut alnPrv c).query (Fin.castSucc (0 : Fin 2))) = some (c 0) := by
  rw [alnTrace, alnSrOut, alnOut_query0]
  exact OracleLog.answerOf_cons_self _ _ _

/-- The round-1 final challenge is the slot-1 recorded answer `c 1`. -/
theorem alnChal1 (c : Fin 2 → ZMod 5) (d : Fin 3 → ZMod 5) :
    srFinalChal alnPrv c d (Fin.castSucc (1 : Fin 2)) = c 1 := by
  rw [srFinalChal_def, alnTrace, alnSrOut, alnOut_query1,
    List.find?_cons_of_neg (by simpa using alnQ0_ne (c 0)),
    List.find?_cons_of_pos (by simp)]

/-- **The refuter's last word satisfies the aggregate EXACTLY, on every
draw**: link 0's target is 0 (so the round-0 challenge is inert in the
target), and `alnW (ρ₁ • 1⃗) = ρ₁ = 0 + ρ₀·0 + ρ₁·1` by construction. -/
theorem alnAggSat (c : Fin 2 → ZMod 5) (d : Fin 3 → ZMod 5) :
    AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
      (aggregate linRoot
        (padSched fun i : Fin 2 => srFinalChal alnPrv c d i.castSucc)
        alnClaim goodChain)
      ((c 1) • oneWord) := by
  have hγ1 : padSched (fun i : Fin 2 => srFinalChal alnPrv c d i.castSucc) 1
      = c 1 := by
    rw [padSched_lt _ (by norm_num : (1 : ℕ) < 2)]
    exact alnChal1 c d
  have hagg : ∀ γs : ℕ → ZMod 5,
      aggregate linRoot γs alnClaim goodChain
        = foldClaims linRoot (foldClaims linRoot alnClaim claim₀ (γs 0))
            claim₁ (γs 1) := fun γs => rfl
  refine ⟨Submodule.mem_top, fun jj => ?_⟩
  rw [hagg]
  show alnW ((c 1) • oneWord)
      = 0 + padSched (fun i : Fin 2 => srFinalChal alnPrv c d i.castSucc) 0
          * 0
        + padSched (fun i : Fin 2 => srFinalChal alnPrv c d i.castSucc) 1
          * 1
  rw [hγ1, map_smul, smul_eq_mul, show alnW oneWord = (1 : ZMod 5) from rfl]
  ring

/-- **The FS verifier accepts the refuter's run, on every draw.** -/
theorem alnVerify (c : Fin 2 → ZMod 5) (d : Fin 3 → ZMod 5) :
    fiatShamir accReductionBcsShifted_F5 0
        (fsOracle (srOut alnPrv c) (srFinalChal alnPrv c d))
        (srOut alnPrv c)
      = some (aggregate linRoot
            (padSched fun i : Fin 2 => srFinalChal alnPrv c d i.castSucc)
            alnClaim goodChain,
          (c 1) • oneWord) := by
  classical
  rw [fiatShamir_fsOracle]
  have hopen : ∀ i : Fin 3, ColsOpen S₅ qPair ((srOut alnPrv c).πs i) := by
    intro i
    rw [alnSrOut]
    fin_cases i
    · exact msgOf_opens xWord
    · exact msgOf_opens _
    · exact msgOf_opens _
  have hanchor : ∀ j, ((srOut alnPrv c).πs 0).cols j = xWord (qPair j) := by
    intro j
    rw [alnSrOut]
    rfl
  show (if (∀ i, ColsOpen S₅ qPair ((srOut alnPrv c).πs i)) ∧
        (∀ j, ((srOut alnPrv c).πs 0).cols j = xWord (qPair j)) then
      some (aggregate linRoot
          (padSched fun i : Fin 2 => srFinalChal alnPrv c d i.castSucc)
          alnClaim goodChain,
        bcsWord dom₅ 2 qPair ((srOut alnPrv c).πs (Fin.last 2)))
    else none) = _
  rw [if_pos ⟨hopen, hanchor⟩,
    show (srOut alnPrv c).πs (Fin.last 2) = msgOf ((c 1) • oneWord) from by
      rw [alnSrOut]; rfl,
    msgOf_word (Submodule.smul_mem _ _ oneWord_mem)]

/-- **The refuter passes the round-0 link-opening check against the HONEST
root, at its recorded challenge, on every draw** — the tether of
`[ORACLE-LOG-linked]` is satisfied honestly; it is not what the refuter
beats. -/
theorem alnLinkOpened (c : Fin 2 → ZMod 5) :
    LinkOpened S₅ qPair (S₅.commit (msEx 0))
      ((srOut alnPrv c).πs (Fin.castSucc (0 : Fin 2)))
      ((srOut alnPrv c).πs (Fin.succ (0 : Fin 2)))
      ((OracleLog.answerOf (srTrace alnPrv c)
        ((srOut alnPrv c).query (Fin.castSucc (0 : Fin 2)))).getD 0) := by
  have hgetD : (OracleLog.answerOf (srTrace alnPrv c)
      ((srOut alnPrv c).query (Fin.castSucc (0 : Fin 2)))).getD 0 = c 0 := by
    rw [alnAnswer0]
    rfl
  rw [hgetD,
    show (srOut alnPrv c).πs (Fin.castSucc (0 : Fin 2)) = msgOf xWord from by
      rw [alnSrOut]; rfl,
    show (srOut alnPrv c).πs (Fin.succ (0 : Fin 2))
        = msgOf (xWord + (c 0) • msEx 0) from by rw [alnSrOut]; rfl]
  refine ⟨fun j => msEx 0 (qPair j), fun j => S₅.openAt (msEx 0) (qPair j),
    fun j => S₅.verifyOpen_commit _ _, fun j => ?_⟩
  show (xWord + (c 0) • msEx 0) (qPair j)
      = xWord (qPair j) + (c 0) * msEx 0 (qPair j)
  rfl

/-- The log-read increment at round 0: `ρ₀⁻¹·ρ₀ • msEx 0` at `ρ₀ = c 0`. -/
theorem alnExtract (c : Fin 2 → ZMod 5) :
    shiftedLogExtractor (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot
        goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
        (by norm_num) S₅ dom₅ 2 qPair 0
        (srOut alnPrv c) (srTrace alnPrv c) (0 : Fin 2)
      = ((c 0)⁻¹ * (c 0)) • msEx 0 := by
  unfold shiftedLogExtractor logIncrement
  rw [alnAnswer0, Option.map_some, Option.getD_some,
    show (srOut alnPrv c).πs (Fin.succ (0 : Fin 2))
        = msgOf (xWord + (c 0) • msEx 0) from by rw [alnSrOut]; rfl,
    show (srOut alnPrv c).πs (Fin.castSucc (0 : Fin 2)) = msgOf xWord from by
      rw [alnSrOut]; rfl,
    msgOf_word (Submodule.add_mem _ xWord_mem
      (Submodule.smul_mem _ _ (msEx_mem 0))),
    msgOf_word xWord_mem, add_sub_cancel_left, smul_smul]

/-- **The extracted increment misaligns AGAINST THE REFUTER'S OWN
STATEMENT** at every nonzero draw: `alnW (msEx 0) = 2 ≠ 0`, kernel-checked.
(Against the honest `genesis` it is perfectly aligned — `msEx_linkAligned`,
CITED. The channel is the statement, not the word.) -/
theorem alnMisaligned (c : Fin 2 → ZMod 5) (hc : ¬ c 0 = 0) :
    ¬ LinkAligned (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) alnClaim
      goodChain (0 : Fin 2) (((c 0)⁻¹ * (c 0)) • msEx 0) := by
  rintro ⟨-, hall⟩
  have h := hall 0
  rw [inv_mul_cancel₀ hc, one_smul] at h
  have hval : (goodChain.get (0 : Fin 2)).claim.targets 0 = 0 := by decide
  rw [hval] at h
  exact (by decide : ¬ alnClaim.weights 0 (msEx 0) = 0) h

/-- **[ORACLE-LOG-linked] is refutable at every useful price**: any `εslot`
it holds at — at the HONEST designation family, on the landed chain — is
forced `≥ 4/5` on the whole window. The refuter's event contains
`{ρ₀ ≠ 0}`. -/
theorem oracleLogProgramLinked_forces (εslot : ℝ → ℝ)
    (h : OracleLogProgramLinked (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
      linRoot goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
      (by norm_num) S₅ dom₅ 2 qPair (fun k => S₅.commit (msEx k)) εslot) :
    ∀ δ ∈ Set.Ioo (0 : ℝ) (1 / 16), (4 : ℝ) / 5 ≤ εslot δ := by
  intro δ hδ
  have hb := h 0 2 alnPrv (0 : Fin 2) (0 : Fin 2) δ hδ
  refine le_trans ?_ hb
  have h15 : uniformProb ((Fin 2 → ZMod 5) × (Fin 3 → ZMod 5))
      (fun coins => coins.1 0 = 0) ≤ 1 / 5 := by
    have h5 := uniformProb_prod_coord_le (γ := Fin 3 → ZMod 5)
      (0 : Fin 2) (0 : ZMod 5)
    rwa [show (Fintype.card (ZMod 5) : ℝ) = 5 from by
      rw [ZMod.card]; norm_num] at h5
  have hnot : (4 : ℝ) / 5 ≤ uniformProb ((Fin 2 → ZMod 5) × (Fin 3 → ZMod 5))
      (fun coins => ¬ coins.1 0 = 0) := by
    rw [uniformProb_not]
    linarith
  refine le_trans hnot (uniformProb_mono ?_)
  rintro ⟨c, dd⟩ hne
  exact ⟨alnHit c, alnLinkOpened c,
    ⟨_, _, alnVerify c dd,
      ⟨(c 1) • oneWord, alnAggSat c dd, by
        rw [fracHamming_self]; exact hδ.1.le⟩⟩,
    by rw [alnExtract]; exact alnMisaligned c hne⟩

/-- **The intended price is dead again**: `[ORACLE-LOG-linked]` at
`εslot = accRbrError = 1/|F|` is FALSE on the landed F₅ chain, at the honest
designation. The statement↔designation channel, not the increment tether, is
what it fails on. -/
theorem oracleLogProgramLinked_accRbrError_false :
    ¬ OracleLogProgramLinked (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
      linRoot goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
      (by norm_num) S₅ dom₅ 2 qPair (fun k => S₅.commit (msEx k))
      (accRbrError (ZMod 5) (fun _ => 0)) := by
  intro h
  have h1 := oracleLogProgramLinked_forces _ h (1 / 32)
    (by rw [Set.mem_Ioo]; exact ⟨by norm_num, by norm_num⟩)
  rw [accRbrError_zero_five] at h1
  norm_num at h1

/-! ### The guard's teeth and the guarded bound, fired -/

/-- The refuter's statement fails the alignment guard at round 0 —
kernel-checked. -/
theorem alnAligned_guard_false :
    ¬ LinkAligned (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) alnClaim
      goodChain (0 : Fin 2) (msEx 0) := by
  rintro ⟨-, hall⟩
  have h := hall 0
  have hval : (goodChain.get (0 : Fin 2)).claim.targets 0 = 0 := by decide
  rw [hval] at h
  exact (by decide : ¬ alnClaim.weights 0 (msEx 0) = 0) h

/-- **The GUARDED per-slot event for the statement-channel refuter is
EMPTY** — probability 0, not merely `≤ 1/|F|`: the alignment guard
contradicts `alnPrv`'s statement outright. The guard is load-bearing at
exactly the run that killed the unguarded statement — mirroring how
`progLinked_zero` certified the `LinkOpened` clause against `progPrv`. -/
theorem alnGuarded_zero (δ : ℝ) :
    uniformProb ((Fin 2 → ZMod 5) × (Fin 3 → ZMod 5)) (fun coins =>
      hitAt alnPrv (Fin.castSucc (0 : Fin 2)) (0 : Fin 2) coins.1 ∧
      LinkAligned (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
        (srOut alnPrv coins.1).stmt.x goodChain (0 : Fin 2) (msEx 0) ∧
      LinkOpened S₅ qPair (S₅.commit (msEx 0))
        ((srOut alnPrv coins.1).πs (Fin.castSucc (0 : Fin 2)))
        ((srOut alnPrv coins.1).πs (Fin.succ (0 : Fin 2)))
        ((OracleLog.answerOf (srTrace alnPrv coins.1)
          ((srOut alnPrv coins.1).query (Fin.castSucc (0 : Fin 2)))).getD 0) ∧
      (∃ (x' : AccClaim (ZMod 5) (ZMod 5) (Fin 4) 1) (y' : Fin 4 → ZMod 5),
        fiatShamir accReductionBcsShifted_F5 0
            (fsOracle (srOut alnPrv coins.1)
              (srFinalChal alnPrv coins.1 coins.2))
            (srOut alnPrv coins.1) = some (x', y') ∧
        RelaxedMem accReductionBcsShifted_F5.R' δ
          (srOut alnPrv coins.1).stmt.idx x' y'
          (srOut alnPrv coins.1).w') ∧
      ¬ LinkAligned (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
        (srOut alnPrv coins.1).stmt.x goodChain (0 : Fin 2)
        (shiftedLogExtractor (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
          linRoot goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
          (by norm_num) S₅ dom₅ 2 qPair 0
          (srOut alnPrv coins.1) (srTrace alnPrv coins.1) (0 : Fin 2)))
      = 0 := by
  refine uniformProb_false ?_
  rintro coins ⟨-, halign, -⟩
  exact alnAligned_guard_false halign

/-- **The guarded bound, fired on the landed chain**: `[ORACLE-LOG-linked-
aligned]` HOLDS at the honest designation family `msEx` with per-slot price
`1/5` — every hypothesis discharged by a landed witness. -/
theorem oracleLogLinkedAligned_F5 :
    OracleLogLinkedAligned (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot
      goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
      (by norm_num) S₅ dom₅ 2 qPair msEx (fun _ => 1 / 5) := by
  intro s tq P i j δ hδ
  have h := oracleLogLinkedAligned_proved
    (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
    (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
    S₅ dom₅ 2 qPair le_rfl qPair_inj msEx msEx_mem s tq P i j δ hδ
  rwa [show (1 : ℝ) / (Fintype.card (ZMod 5) : ℝ) = 1 / 5 from by
    rw [ZMod.card]; norm_num] at h

/-! ### The linked reduction, fired -/

/-- **The linked reduction, BUILT** on the landed F₅ chain at the deployed
designation family `msEx` — the committed masked link words, whose
designations the honest statement aligns (`msEx_linkAligned`, CITED). -/
@[reducible] noncomputable def accReductionBcsShiftedLinked_F5 : Reduction :=
  accReductionBcsShiftedLinked (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
    linRoot goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
    (by norm_num) S₅ dom₅ 2 qPair msEx

/-- **Satisfiable — the linked verifier accepts the honest fold-root run at
every draw**, with the unlinked output (`linked_verify_honest`, which cites
`shifted_verify_honest` + `linkOpened_honest`; F₅ premise
`linkOpened_msgShifted_F5` is the same check fired pointwise). -/
theorem linked_completeness_F5 (ρs : Fin 3 → ZMod 5) :
    accReductionBcsShiftedLinked_F5.verify () genesis xWord
        (fun c => msgShifted ρs (c : ℕ)) ρs
      = some (aggregate linRoot (padSched fun i : Fin 2 => ρs i.castSucc)
            genesis goodChain,
          flatFold (padSched fun i : Fin 2 => ρs i.castSucc) xWord msEx) :=
  linked_verify_honest (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot
    goodChain (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
    S₅ dom₅ 2 qPair le_rfl qPair_inj genesis xWord_mem msEx_mem ρs

/-- **Teeth — the zero-tether refuter of `[ORACLE-LOG-program]` now dies
INSIDE the verifier**: the linked F₅ verifier returns `none` on `progPrv`'s
message family at every challenge vector — the round-1 link opening against
the deployed designation `msEx 1` forces `2 + ρ = 1 + ρ` through binding
(`progLinkOpened_refuted`'s computation, CITED, at column `qPair 1` where
`msEx 1` opens to `1`). The grown clause is the missing tether, now
load-bearing in the reduction itself. -/
theorem progMsgs_linked_rejected (ρs : Fin 3 → ZMod 5) :
    accReductionBcsShiftedLinked_F5.verify () genesis xWord
        (fun c => progMsgs (ρs (Fin.castSucc (1 : Fin 2))) (c : ℕ)) ρs
      = none := by
  cases hv : accReductionBcsShiftedLinked_F5.verify () genesis xWord
      (fun c => progMsgs (ρs (Fin.castSucc (1 : Fin 2))) (c : ℕ)) ρs with
  | none => rfl
  | some out =>
    exfalso
    obtain ⟨-, hlink⟩ := linked_verify_strengthens
      (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
      (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
      S₅ dom₅ 2 qPair msEx genesis xWord
      (fun c => progMsgs (ρs (Fin.castSucc (1 : Fin 2))) (c : ℕ)) ρs hv
    obtain ⟨lc, lo, hver, hcols⟩ := hlink (1 : Fin 2)
    have hlc : ∀ j, lc j = msEx 1 (qPair j) := binding_columns S₅ rfl hver
    have hc1 := hcols 1
    rw [hlc 1, show msEx 1 (qPair 1) = 1 from by decide] at hc1
    have he : (2 + ρs (Fin.castSucc (1 : Fin 2))) * 1
        = 1 + ρs (Fin.castSucc (1 : Fin 2)) * 1 := hc1
    rw [mul_one, mul_one] at he
    exact absurd (add_right_cancel he) (by decide)

end OracleLogLinkedExample

/-! ## Residual obligation — prose, not a stub

**What CLOSED here.**

* **`[ORACLE-LOG-linked]` is SETTLED — negatively, with teeth** (third
  finding in the `OB2_depth_composition_false` tradition on this route). The
  statement-channel refuter `alnPrv` (TWO queries, on the landed F₅ chain, at
  the HONEST designation family `S₅.commit (msEx k)`) makes the repaired
  per-slot event hold whenever its round-0 challenge is nonzero: it passes
  the link-opening tether honestly (`alnLinkOpened`), accepts exactly
  (`alnVerify`/`alnAggSat` — its own channel `alnW = proj 0` keeps the
  aggregate solvable), and its pinned increment `msEx 0` misaligns against
  its OWN statement's channel (`alnW (msEx 0) = 2 ≠ 0`, kernel-checked)
  while remaining perfectly aligned for the honest genesis
  (`msEx_linkAligned`). Machine-checked: `oracleLogProgramLinked_forces`
  (any admissible `εslot ≥ 4/5`) and
  `oracleLogProgramLinked_accRbrError_false` (the intended `1/|F|` price is
  false). The previous lane's repair re-attached increment↔commitment but
  left statement↔designation untethered — the event measures alignment at
  the ADVERSARY's channel against CALLER-fixed designations, and the landed
  `slotBad`'s statement guard (`stmt ∈ Z`) had been dropped from both
  oracle-log per-slot statements.
* **The guarded per-slot bound is PROVED, at the sharp price `1/|F|`**
  (`OracleLogLinkedAligned` / `oracleLogLinkedAligned_proved`, budget form
  `oracleLogLinkedAligned_accRbrError`, F₅ firing at `1/5`
  `oracleLogLinkedAligned_F5`). The guard is the per-round `Z`-clause
  `LinkAligned C stmt.x ch i (wv i)`; under it the event is CONTAINED in
  `{c_j = 0}`: `hitAt_answerOf` (NEW, generic — the hit-horn's recorded
  answer IS the tested coin, `hitBad_fibre_le`'s `hquery` pinning made a
  portable citation) plus `linkOpened_increment_pinned_free` (NEW — the
  increment pin with NO premise on the previous message's columns, since
  erasure recovery is AFFINE in the columns, `recoverFromColumns_line`) pin
  the extracted increment to the designated word, which the guard says is
  aligned — contradiction with the misalignment conjunct. The hit-horn
  per-slot mass of the deployed-ZK adaptive bound is CLOSED — genuinely
  fixed-pair, no continuation bound, no per-fibre choreography needed. The
  guard's teeth: `alnGuarded_zero` (the refuter's guarded event is EMPTY).
* **The reduction GREW the clause** (derived-path law):
  `accReductionBcsShiftedLinked` conjoins the per-round `LinkOpened` check
  against the designated words into `verify`, superseding the unlinked twin
  for all downstream work. `linked_verify_strengthens` (linked acceptance ⟹
  unlinked acceptance, same output, + all round openings — the composition's
  discharge lemma), `linked_verify_of_shifted` + `linked_verify_honest`
  (completeness, CITING `shifted_verify_honest` and `linkOpened_honest`),
  `linked_completeness_F5` (fired), and `progMsgs_linked_rejected` (teeth:
  the zero-tether refuter of `[ORACLE-LOG-program]` is rejected INSIDE the
  verifier — `progLinkOpened_refuted`'s binding computation at the deployed
  designation).

**`[ORACLE-LOG-linked-resid]`** — what remains for the full deployed-ZK
adaptive bound `(t + k)·accRbrError` over the linked reduction, stated
precisely:

* **(a) The fresh horn at nonzero-target links.** When round `i`'s designated
  prefix is unqueried, the challenge is the output-independent fresh coin
  (`unqueried_chal_fresh`, CITED) and the extractor reads `0`
  (`logIncrement_none_of_unqueried`, CITED). Over the deployed statement set
  the zero word is aligned iff the link's targets vanish (weights are
  linear), so zero-target links have EMPTY fresh events. For a link with
  some nonzero target `τ_{i,j₀} ≠ 0`: the output — hence the last word `y'`
  and every message — is fixed before the fresh coin `d_i` exists, the
  aggregate's `j₀`-target is AFFINE in `d_i` with slope `τ_{i,j₀}`, and
  `RelaxedMem R'` at `δ < dC/2` pins at most ONE good draw by unique
  decoding (two accepted draws give two satisfiers within `2δ < dC` of the
  same `y'`, hence equal, hence equal affine targets, hence equal draws) —
  per-slot mass `1/|F|`. The slicing is `freshBad_le`'s `splitCoord`
  choreography verbatim; the unique-decoding pin is the one genuinely new
  lemma. NOT proved here.
* **(b) The `(t + k)` assembly.** Over
  `Z_dep := {st | AccClaim.Satisfies C st.x st.y ∧
  ∀ i, LinkAligned C st.x ch i (wv i)}` (the deployed statement set: genesis
  true + channel aligned with the chain's designations — the guard's home;
  honest F₅ inhabitant: `genesis` with `msEx_linkAligned`), the linked
  `sound_log` event decomposes: genesis satisfiability collapses
  `¬ RelaxedMem R` to `∃ i, ¬ LinkAligned … (w i)` (the links clause is
  `ystar`-independent); `logSlot_cover` (CITED) splits each round into
  fresh/hit horns; linked acceptance discharges every hit horn's
  `LinkOpened` conjunct (`linked_verify_strengthens`) and `Z_dep` its guard;
  the per-`j` union event `∃ i, hit(i, j) ∧ …` is contained in the SAME
  `{c_j = 0}` (the containment is uniform in `i`), so each of the `t` game
  slots pays `1/|F|` once — not once per round; the `k` fresh slots pay (a);
  `uniformProb_exists_le` (CITED) sums to `(t + k)·accRbrError`. This is
  `gameSlotBound_proved`-shape bookkeeping over landed lemmas — real but
  mechanical; not rerun here.
* **(c) Inherited unchanged**: the shifted state design
  (`[ACC-rbr-bcs-shifted-resid]`(b)), `[ZK-RBR-extract]` lemma A, and the
  floor `[FS-ROM]`/`[COMMIT-CR]`/`hPG` — consumed, never claimed.

**Honest assessment.** The deployed-ZK adaptive-increment bound is NOT yet
closed, and `[ACC-rbr-bcs-shifted-resid]`(a) is NOT yet settled — the task's
premise ("now well-posed after the repair") was FALSE: the repaired per-slot
statement still had a hole, one level up from the one it fixed, and proving
it as posed was impossible. What this lane delivers instead: the refutation
(machine-checked, at the honest designation, with the tether satisfied — so
the finding isolates the statement↔designation channel exactly), the
guarded statement that survives it, and the guarded bound PROVED at `1/|F|`
— the hit-horn mass of the composition, which was the genuinely-contested
piece (the previous refutation showed no fixed pair existed there at all;
now one does, and it prices). The remaining mass — fresh-horn
unique-decoding pin + the `(t + k)` assembly over `Z_dep` — is named sharp
in (a)/(b) and is `freshBad_le`/`gameSlotBound_proved`-shaped work over
landed machinery, with no open structural question left in it.

## Ledger

* `uniformProb_not` / `uniformProb_eq_single` / `uniformProb_prod_coord_le`
  — PROVED: complement counting; one pinned coin coordinate costs `1/|F|`
  (`splitProd1` + `uniformProb_prod_le`, CITED).
* `recoverFromColumns_line` — PROVED: erasure recovery is affine in the
  opened columns (`Lagrange.interpolate` + `evalOnDomain` linearity).
* `linkOpened_increment_pinned_free` — PROVED: the increment pin with NO
  previous-message premise; supersedes the landed pin's `hu`/`hπ` on the
  analysis side (`binding_columns` + `recoverFromColumns_sound`, CITED).
* `hitAt_answerOf` — PROVED (generic): on the hit horn the recorded answer
  IS the tested coin — `hitBad_fibre_le`'s `hquery` pinning, portable.
* `alnW`/`alnClaim`/`alnMsgs`/`alnOut`/`alnQ0`/`alnQ1`/`alnPrv` — BUILT:
  the two-query statement-channel refuter on the landed F₅ chain.
* `alnTrace`/`alnSrOut`/`alnHit`/`alnAnswer0`/`alnChal1`/`alnAggSat`/
  `alnVerify`/`alnLinkOpened`/`alnExtract`/`alnMisaligned` — PROVED: the
  run hits at slot 0, passes the tether honestly, accepts exactly on every
  draw, and its pinned increment misaligns against its own statement at
  every nonzero draw (kernel-checked).
* `oracleLogProgramLinked_forces` / `oracleLogProgramLinked_accRbrError_false`
  — PROVED: `[ORACLE-LOG-linked]` forces `εslot ≥ 4/5`; the intended
  `accRbrError` price is FALSE — at the honest designation.
* `OracleLogLinkedAligned` — STATED (`[ORACLE-LOG-linked-aligned]`,
  statement-first, ATLAS fields): the guarded per-slot obligation.
* `oracleLogLinkedAligned_proved` / `_accRbrError` / `_F5` — PROVED: the
  guarded bound at the SHARP price `1/|F|` (≤ `accRbrError`; `1/5` fired).
* `alnAligned_guard_false` / `alnGuarded_zero` — PROVED (guard teeth): the
  refuter's guarded event is EMPTY.
* `accReductionBcsShiftedLinked` — DEFINED (derived-path): verify GROWN by
  the per-round link-opening clause; `linked_verify_strengthens` /
  `linked_verify_of_shifted` / `linked_verify_honest` — PROVED
  (characterization + completeness, `shifted_verify_honest` +
  `linkOpened_honest` CITED); `linked_completeness_F5` — fired;
  `progMsgs_linked_rejected` — PROVED (teeth: `progPrv`'s family rejected
  inside the verifier, `progLinkOpened_refuted`'s computation CITED).
* `[ORACLE-LOG-linked-resid]` — prose above: (a) fresh-horn unique-decoding
  pin at nonzero-target links, (b) the `(t + k)` assembly over `Z_dep`,
  (c) inherited.

`#print axioms` on `hitAt_answerOf`, `linkOpened_increment_pinned_free`,
`oracleLogLinkedAligned_proved`,
`OracleLogLinkedExample.oracleLogProgramLinked_accRbrError_false`,
`OracleLogLinkedExample.alnGuarded_zero`,
`OracleLogLinkedExample.linked_completeness_F5`,
`OracleLogLinkedExample.progMsgs_linked_rejected`: `propext`,
`Classical.choice`, `Quot.sound` — no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage
