/-
# Selvage.AccRbrBcsShifted — [ACC-rbr-bcs-resid](a): the SHIFTED schedule that
respects the fold-root lag.

`Selvage/AccRbrBcs.lean` closed `[ACC-rbr-bcs]` for the whole-code-mask regime,
where round `i`'s message recommits round `i`'s OWN (masked) word, and named
`[ACC-rbr-bcs-resid]`(a) precisely: the CONSTRAINED-mask deployment opens
columns of the recommitted PARTIAL FOLDS `h_c = partialFold γs f₀ ms c`, and
those roots LAG their challenge — `h_{i+1} = h_i + ρ_i • w_i`
(`partialFold_succ`, CITED) is committable only AFTER `ρ_i`, i.e. inside
round `i+1`'s message, while Defs 4.1/4.2 score `ρ_i` at round `i`'s
extension. This file builds the schedule that fixes the ATTRIBUTION:

* `accReductionBcsShifted` — the chain as a WARP `Reduction` with
  `k = ch.length + 1` rounds whose round-`c` message commits the `c`-th
  partial fold: `h_0` (the genesis recommitment, challenge-free) at round 0,
  `h_{i+1}` at round `i+1` — AFTER `ρ_i`, which round `i` carried. One
  Reduction round exists per fold root; the FINAL round's challenge is inert
  (the deployment has `k+1` roots for `k` fold challenges; the last challenge
  pads the alternation and is never read). The verifier checks every opening,
  anchors round 0's columns to the genesis word, and outputs the aggregate
  together with the LAST message's synthesized word — the recommitted full
  fold itself, no re-folding.
* `shiftedMsg` + the ALIGNMENT pair — the one fact the shift fixes, proved:
  `shiftedMsg_committable` (round `c`'s message reads ONLY challenges at
  rounds `< c` — it is committable from the transcript prefix, which the
  unshifted attribution violates) and `shifted_alignment` (round `k+1`'s
  message-word IS round `k`'s word folded by the ROUND-`k` challenge — the
  word and the challenge that folded it now co-occur, `partialFold_succ`
  CITED). `shifted_increment_recovered` is the seam's `γ⁻¹`-difference map at
  the shifted alphabet: consecutive shifted words return the round increment
  exactly — the column DATA is seam-equivalent, as `[ACC-rbr-bcs-resid]`(a)
  said.
* `shifted_verify_honest` / `shifted_verify_eq_unshifted` — on the honest
  lagged-commitment run the shifted verifier fires and outputs EXACTLY what
  `accReductionBcs`'s verifier outputs on the corresponding increment
  transcript (`partialFold_last` + `foldWords_ofFn`, CITED): the shift
  re-packages the roots, not the reduced statement.
* `accRbrKnowledgeSoundBcsShifted` — Def 4.2 at the shifted alphabet, entered
  STATEMENT-FIRST as a `Prop` (house law): a `RbrKnowledgeSoundness` instance
  whose knowledge state entails committed-column consistency and whose
  per-round error is bounded by `εfold`. NOT inhabited here — inhabiting it
  is `[ACC-rbr-bcs-shifted-resid]`, stated sharply at the bottom: at a
  shifted round's extension the FRESH challenge is inert for the fold data
  (the newly scorable increment is weighted by the PREVIOUS round's
  challenge, already fixed when its fold root was chosen), so Def 4.2's
  `uniformProb` over the fresh challenge cannot be priced by the landed
  fixed-pair `accSound_rbr` event.

**Keystones** (F₅, landed objects REUSED): `accReductionBcsShifted_F5` (the
shifted reduction BUILT on `goodChain` at `C = ⊤`, `S₅`, `qPair`,
`t = d = 2`); `shifted_completeness_F5` (satisfiable: the verifier ACCEPTS
the honest fold-root transcript at EVERY challenge draw and its output claim
is satisfied by its output word — `masked_completeness_F5` CITED);
`shifted_reduces_as_unshifted_F5` (the fold-root run and the landed
increment run `msgBcs` reduce to the SAME statement);
`unshifted_misaligns_F5` (teeth: NO single round-0 message synthesizes
`h_1` for every `ρ_0` — the unshifted attribution is not just unproved but
IMPOSSIBLE; the shift is load-bearing) with `shifted_h1_committed_F5` the
positive contrast. No `sorry`, no vacuous `Prop := True`.
-/
import Selvage.Rbr
import Selvage.ZkExtraction
import Selvage.AccRbrBcs

namespace Minidregg.Selvage

/-! ## The fold schedule's locality — what a partial fold reads -/

section PartialFoldLocality

variable {F : Type} [Field F] {ι : Type*} {n : ℕ}

/-- Partial folds of codewords are codewords — the recommitted roots commit
genuine code elements (linearity; the membership `bcsWord_committed` and
`recoverFromColumns_sound` consume). -/
theorem partialFold_mem {V : Submodule F (ι → F)} (γs : ℕ → F) {f₀ : ι → F}
    {ms : Fin n → ι → F} (hf₀ : f₀ ∈ V) (hms : ∀ k, ms k ∈ V) (c : ℕ) :
    partialFold γs f₀ ms c ∈ V := by
  unfold partialFold
  exact Submodule.add_mem _ hf₀
    (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hms j))

/-- **Schedule locality**: the `c`-th partial fold reads the challenge
schedule ONLY at rounds `< c`. This is the committability content of the
shift — at the moment round `c`'s message is due, exactly the challenges of
rounds `0..c-1` have been sent, and they determine `h_c`. -/
theorem partialFold_sched_local {γs γs' : ℕ → F} (f₀ : ι → F)
    (ms : Fin n → ι → F) {c : ℕ} (h : ∀ j < c, γs j = γs' j) :
    partialFold γs f₀ ms c = partialFold γs' f₀ ms c := by
  unfold partialFold
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [h (j : ℕ) (Finset.mem_filter.mp hj).2]

end PartialFoldLocality

/-! ## The honest shifted message and the alignment pair -/

section ShiftedAlphabet

variable {Root' Op : Type} {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {m t n : ℕ}

/-- **The honest shifted round message**: recommit the `c`-th partial fold,
open its `t` columns, attach honest opening proofs — the constrained-mask
deployment's round-`c` message (`[ACC-rbr-bcs-resid]`(a)'s object). Round 0
carries `h_0 = f₀`'s recommitment; round `i+1` carries
`h_{i+1} = h_i + ρ_i • w_i`, formable because `ρ_i` arrived at round `i`. -/
noncomputable def shiftedMsg (S : BindingCommitment Root' F (Fin m) Op)
    (q : Fin t → Fin m) (γs : ℕ → F) (f₀ : Fin m → F)
    (ms : Fin n → Fin m → F) (c : ℕ) : BcsMsg Root' F Op t :=
  ⟨S.commit (partialFold γs f₀ ms c),
    fun j => partialFold γs f₀ ms c (q j),
    fun j => S.openAt (partialFold γs f₀ ms c) (q j)⟩

omit [Fintype F] [DecidableEq F] in
/-- The honest shifted messages open — commitment-layer completeness. -/
theorem shiftedMsg_opens (S : BindingCommitment Root' F (Fin m) Op)
    (q : Fin t → Fin m) (γs : ℕ → F) (f₀ : Fin m → F)
    (ms : Fin n → Fin m → F) (c : ℕ) :
    ColsOpen S q (shiftedMsg S q γs f₀ ms c) :=
  fun j => S.verifyOpen_commit (partialFold γs f₀ ms c) (q j)

omit [Fintype F] [DecidableEq F] in
/-- The honest shifted message synthesizes its partial fold exactly —
`recoverFromColumns_sound` (CITED) on the fold, whose code membership is
`partialFold_mem`. -/
theorem shiftedMsg_word (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) {d : ℕ} (hdt : d ≤ t) {q : Fin t → Fin m}
    (hq : Function.Injective (dom ∘ q)) (γs : ℕ → F) {f₀ : Fin m → F}
    {ms : Fin n → Fin m → F} (hf₀ : f₀ ∈ reedSolomonCode dom d)
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d) (c : ℕ) :
    bcsWord dom d q (shiftedMsg S q γs f₀ ms c) = partialFold γs f₀ ms c :=
  recoverFromColumns_sound dom hdt hq (partialFold_mem γs hf₀ hms c)
    fun _ => rfl

omit [Fintype F] [DecidableEq F] in
/-- **Alignment, committability half**: round `c`'s shifted message is a
function of the challenges at rounds `< c` ALONE — two schedules agreeing
below `c` produce the SAME message. Under the shifted attribution the prover
genuinely holds everything the round-`c` message reads when it is due; the
unshifted attribution demanded `ρ_c` one message early
(`unshifted_misaligns_F5` shows that demand is unmeetable, not merely
unproved). -/
theorem shiftedMsg_committable (S : BindingCommitment Root' F (Fin m) Op)
    (q : Fin t → Fin m) (f₀ : Fin m → F) (ms : Fin n → Fin m → F)
    {γs γs' : ℕ → F} {c : ℕ} (h : ∀ j < c, γs j = γs' j) :
    shiftedMsg S q γs f₀ ms c = shiftedMsg S q γs' f₀ ms c := by
  unfold shiftedMsg
  rw [partialFold_sched_local f₀ ms h]

omit [Fintype F] [DecidableEq F] in
/-- **Alignment, co-occurrence half — the one fact the shift fixes**: the
round-`k+1` message-word IS the round-`k` message-word folded by the
ROUND-`k` challenge (`partialFold_succ`, CITED). In the shifted transcript
the fold root `h_{k+1}` and the challenge `ρ_k = γs k` that folded it
CO-OCCUR — the challenge sits at round `k`, strictly before the message at
round `k+1` — whereas Defs 4.1/4.2 on the unshifted schedule scored `ρ_k`
against a message sent before `ρ_k` existed. -/
theorem shifted_alignment (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) {d : ℕ} (hdt : d ≤ t) {q : Fin t → Fin m}
    (hq : Function.Injective (dom ∘ q)) (γs : ℕ → F) {f₀ : Fin m → F}
    {ms : Fin n → Fin m → F} (hf₀ : f₀ ∈ reedSolomonCode dom d)
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d) (k : Fin n) :
    bcsWord dom d q (shiftedMsg S q γs f₀ ms ((k : ℕ) + 1))
      = bcsWord dom d q (shiftedMsg S q γs f₀ ms (k : ℕ))
        + γs (k : ℕ) • ms k := by
  rw [shiftedMsg_word S dom hdt hq γs hf₀ hms,
    shiftedMsg_word S dom hdt hq γs hf₀ hms, partialFold_succ]

omit [Fintype F] [DecidableEq F] in
/-- **The seam's `γ⁻¹`-difference map at the shifted alphabet**: consecutive
shifted message-words return the round increment EXACTLY — the same formula
`seamCounterfactual` decodes columnwise (CITED there; here at word level
through the synthesis). The column DATA of the shifted schedule is
seam-equivalent to the increment data; only the root ATTRIBUTION was open,
and the shift is its packaging. -/
theorem shifted_increment_recovered (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) {d : ℕ} (hdt : d ≤ t) {q : Fin t → Fin m}
    (hq : Function.Injective (dom ∘ q)) (γs : ℕ → F) {f₀ : Fin m → F}
    {ms : Fin n → Fin m → F} (hf₀ : f₀ ∈ reedSolomonCode dom d)
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d) (k : Fin n)
    (hγ : γs (k : ℕ) ≠ 0) :
    (γs (k : ℕ))⁻¹ • (bcsWord dom d q (shiftedMsg S q γs f₀ ms ((k : ℕ) + 1))
        - bcsWord dom d q (shiftedMsg S q γs f₀ ms (k : ℕ))) = ms k := by
  rw [shifted_alignment S dom hdt hq γs hf₀ hms k, add_sub_cancel_left,
    smul_smul, inv_mul_cancel₀ hγ, one_smul]

end ShiftedAlphabet

/-! ## `accReductionBcsShifted` — the chain on the lag-respecting schedule -/

section ShiftedInstance

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

open Classical in
/-- **The accumulator chain at the FOLD-ROOT (constrained-mask) schedule** —
`[ACC-rbr-bcs-resid]`(a)'s owed carrier: `k = ch.length + 1` rounds, one per
recommitted partial fold; round `c`'s message is a `BcsMsg` committing `h_c`.
The indexing SHIFT: `h_{i+1}` (which needs `ρ_i`) is round `i+1`'s message —
sent after round `i`'s challenge — where `accReductionBcs` had round `i`'s
message carry round `i`'s data. The deployment has `ch.length + 1` roots for
`ch.length` fold challenges, so the LAST Reduction round's challenge is inert
padding (never read by `verify`; `Reduction` fixes a message-challenge
alternation). The verifier checks EVERY opening, anchors round 0's columns
to the genesis word (`h_0 = f₀` at the spot-checked positions), and outputs
the aggregate at the first `ch.length` challenges together with the LAST
message's synthesized word — the recommitted full fold, spot-checked rather
than re-folded. Source/target relations and the witness type (the INCREMENT
family) are `accReductionBcs`'s, unchanged. -/
@[reducible] noncomputable def accReductionBcsShifted
    (C : Submodule F (Fin m → F)) (foldRoot : Root → F → Root → Root)
    (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
    (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
    (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F) (d : ℕ)
    (q : Fin t → Fin m) : Reduction where
  Idx := Unit
  X := AccClaim Root F (Fin m) r
  A := F
  X' := AccClaim Root F (Fin m) r
  A' := F
  W := Fin ch.length → Fin m → F
  n := m
  n' := m
  n_pos := hm
  n'_pos := hm
  R := fun _ A₀ f₀ w => AccClaim.Satisfies C A₀ f₀ ∧
    ∀ k : Fin ch.length, LinkAligned C A₀ ch k (w k)
  R' := fun _ Agg h _ => AccClaim.Satisfies C Agg h
  k := ch.length + 1
  k_pos := Nat.lt_succ_of_lt hch
  PMsg := BcsMsg Root' F Op t
  Chal := F
  pmsgNonempty := ⟨⟨S.commit 0, fun _ => 0, fun j => S.openAt 0 (q j)⟩⟩
  chalFintype := inferInstance
  chalNonempty := ⟨0⟩
  δstar := δs
  δstar_pos := hδpos
  δstar_le_one := hδone
  verify := fun _ A₀ f₀ πs ρs =>
    if (∀ i, ColsOpen S q (πs i)) ∧ (∀ j, (πs 0).cols j = f₀ (q j)) then
      some (aggregate foldRoot
          (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
        bcsWord dom d q (πs (Fin.last ch.length)))
    else none

/-- **The shifted verifier fires on the honest lagged-commitment run**: with
every round-`c` message the recommitted `c`-th partial fold at the
transcript's own (restricted) challenge schedule, every opening verifies,
the genesis anchor holds (`partialFold_zero`), and the output is the
aggregate together with the FULL fold (`partialFold_last`, CITED) — for
every challenge draw, the inert last challenge included. -/
theorem shifted_verify_honest (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) {d : ℕ} (q : Fin t → Fin m) (hdt : d ≤ t)
    (hq : Function.Injective (dom ∘ q)) (A₀ : AccClaim Root F (Fin m) r)
    {f₀ : Fin m → F} {ms : Fin ch.length → Fin m → F}
    (hf₀ : f₀ ∈ reedSolomonCode dom d)
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    (ρs : Fin (ch.length + 1) → F) :
    (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d
        q).verify () A₀ f₀
        (fun c => shiftedMsg S q
          (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms (c : ℕ)) ρs
      = some (aggregate foldRoot
            (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
          flatFold (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms)
    := by
  classical
  have hopen : ∀ i : Fin (ch.length + 1),
      ColsOpen S q (shiftedMsg S q
        (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms (i : ℕ)) :=
    fun i => shiftedMsg_opens S q _ f₀ ms _
  have hgen : ∀ j, (shiftedMsg S q
      (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms
        ((0 : Fin (ch.length + 1)) : ℕ)).cols j = f₀ (q j) := by
    intro j
    show partialFold (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms
      ((0 : Fin (ch.length + 1)) : ℕ) (q j) = f₀ (q j)
    rw [Fin.val_zero, partialFold_zero]
  show (if (∀ i : Fin (ch.length + 1), ColsOpen S q (shiftedMsg S q
        (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms (i : ℕ)))
      ∧ (∀ j, (shiftedMsg S q
          (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms
            ((0 : Fin (ch.length + 1)) : ℕ)).cols j = f₀ (q j))
      then _ else none) = _
  rw [if_pos ⟨hopen, hgen⟩]
  have hw : bcsWord dom d q (shiftedMsg S q
      (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms
        ((Fin.last ch.length : Fin (ch.length + 1)) : ℕ))
      = flatFold (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms := by
    rw [shiftedMsg_word S dom hdt hq _ hf₀ hms, Fin.val_last, partialFold_last]
  show some (aggregate foldRoot
      (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
    bcsWord dom d q (shiftedMsg S q
      (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms
        ((Fin.last ch.length : Fin (ch.length + 1)) : ℕ))) = _
  rw [hw]

/-- **The shift re-packages the roots, not the reduced statement**: on
honest data the shifted verifier outputs EXACTLY what `accReductionBcs`'s
verifier outputs on the corresponding increment transcript — any unshifted
message family whose synthesized words are the increments, at the restricted
challenge schedule (`foldWords_ofFn` + `partialFold_last`, CITED). The two
reductions reduce every honest committed run to the SAME target claim; what
differs is WHEN each root is committable — the attribution
`[ACC-rbr-bcs-shifted-resid]` prices. -/
theorem shifted_verify_eq_unshifted (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) {d : ℕ} (q : Fin t → Fin m) (hdt : d ≤ t)
    (hq : Function.Injective (dom ∘ q)) (A₀ : AccClaim Root F (Fin m) r)
    {f₀ : Fin m → F} {ms : Fin ch.length → Fin m → F}
    (hf₀ : f₀ ∈ reedSolomonCode dom d)
    (hms : ∀ k, ms k ∈ reedSolomonCode dom d)
    (πs : Fin ch.length → BcsMsg Root' F Op t)
    (hopen : ∀ i, ColsOpen S q (πs i))
    (hword : ∀ i, bcsWord dom d q (πs i) = ms i)
    (ρs : Fin (ch.length + 1) → F) :
    (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d
        q).verify () A₀ f₀
        (fun c => shiftedMsg S q
          (padSched fun i : Fin ch.length => ρs i.castSucc) f₀ ms (c : ℕ)) ρs
      = (accReductionBcs C foldRoot ch hm hch δs hδpos hδone S dom d
          q).verify () A₀ f₀ πs (fun i => ρs i.castSucc) := by
  classical
  rw [shifted_verify_honest C foldRoot ch hm hch δs hδpos hδone S dom q hdt
    hq A₀ hf₀ hms ρs]
  show _ = (if ∀ i, ColsOpen S q (πs i) then
      some (aggregate foldRoot
          (padSched fun i : Fin ch.length => ρs i.castSucc) A₀ ch,
        foldWords (padSched fun i : Fin ch.length => ρs i.castSucc) f₀
          (List.ofFn fun i => bcsWord dom d q (πs i)))
    else none)
  rw [if_pos hopen]
  have hl : (List.ofFn fun i => bcsWord dom d q (πs i)) = List.ofFn ms :=
    congrArg List.ofFn (funext fun i => hword i)
  rw [hl, foldWords_ofFn]

/-- **Def 4.2 at the shifted alphabet — the STATEMENT** (house law:
statement-first; the obligation named before proof work): a
`RbrKnowledgeSoundness` instance for the shifted reduction whose knowledge
state ENTAILS committed-column consistency (the `[ACC-rbr-bcs]` clause that
lets binding pin the fold words) and whose per-round error is bounded by
`εfold` on the paper's `δ`-window. NOT inhabited here — that is
`[ACC-rbr-bcs-shifted-resid]` (module foot), the adaptive-increment round
bound.

ATLAS keystone fields (obligation):
* satisfiable: TODO realizer — the shifted knowledge state (committed-column
  consistency ∧ the IOR state on the DIFFERENCE transcript
  `w_c = ρ_c⁻¹ • (h_{c+1} − h_c)`) plus the round bound for the event whose
  tested increment is committed AFTER its challenge — route (i) BCS/ROM
  oracle-log extraction or route (ii) the adaptive fold-satisfiability
  bound; see the residual.
* teeth: any `εfold < 1` somewhere on the window rules out the degenerate
  state that is false on every proper partial transcript — that state
  concentrates the whole loss at the last round, where satisfiable
  statements force its error to 1; and `unshifted_misaligns_F5` shows the
  attribution being priced is not vacuous.
* premise-inhabitation: `accReductionBcsShifted_F5` is BUILT and its honest
  transcript ACCEPTED (`shifted_completeness_F5`). -/
def accRbrKnowledgeSoundBcsShifted (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m) (εfold : ℝ → ℝ) : Prop :=
  ∃ rbr : RbrKnowledgeSoundness
      (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d q),
    (∀ (δ : ℝ)
        (st : Stmt (accReductionBcsShifted C foldRoot ch hm hch δs hδpos
          hδone S dom d q))
        (tr : Transcript (BcsMsg Root' F Op t) F)
        (w : Fin ch.length → Fin m → F),
        rbr.kstate.state δ st tr w = true → ColsConsistent S q tr.rounds) ∧
    ∀ (i : Fin (ch.length + 1))
      (st : Stmt (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone
        S dom d q)),
      ∀ δ ∈ Set.Ioo (0 : ℝ) δs, rbr.err i st δ ≤ εfold δ

end ShiftedInstance

/-! ## Keystones (ATLAS law 2) — the shifted schedule on the landed F₅ chain -/

namespace AccRbrBcsShiftedExample

open RSExample LCExample ZkHidingExample ZkExtractionExample CommitExample
  AccRbrBcsExample

/-- **The shifted reduction, BUILT** on the landed F₅ chain: `3 = 2 + 1`
rounds — one per recommitted partial fold `h_0, h_1, h_2` — over `goodChain`
at `C = ⊤`, commitment `S₅`, columns at `qPair`, `t = d = 2`, the SAME
window as `accRbrBcs_F5`. -/
@[reducible] noncomputable def accReductionBcsShifted_F5 : Reduction :=
  accReductionBcsShifted (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot
    goodChain (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
    S₅ dom₅ 2 qPair

/-- The honest fold-root message family at the transcript's own challenges:
round `c` recommits `partialFold` at stage `c` of the landed masked chain
(`xWord` genesis, `msEx` increments). -/
noncomputable def msgShifted (ρs : Fin 3 → ZMod 5) (c : ℕ) :
    BcsMsg (Fin 4 → ZMod 5) (ZMod 5) Unit 2 :=
  shiftedMsg S₅ qPair (padSched fun i : Fin 2 => ρs i.castSucc) xWord msEx c

/-- **Satisfiable, fired**: for EVERY challenge draw the shifted verifier
accepts the honest fold-root transcript — openings, genesis anchor, and all —
and outputs the aggregate with the full fold, which SATISFIES it
(`masked_completeness_F5`, CITED, weakened to `⊤`). The lag-respecting
schedule carries the landed masked chain end to end. -/
theorem shifted_completeness_F5 (ρs : Fin 3 → ZMod 5) :
    accReductionBcsShifted_F5.verify () genesis xWord
        (fun c => msgShifted ρs (c : ℕ)) ρs
      = some (aggregate linRoot (padSched fun i : Fin 2 => ρs i.castSucc)
            genesis goodChain,
          flatFold (padSched fun i : Fin 2 => ρs i.castSucc) xWord msEx) ∧
    AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
      (aggregate linRoot (padSched fun i : Fin 2 => ρs i.castSucc) genesis
        goodChain)
      (flatFold (padSched fun i : Fin 2 => ρs i.castSucc) xWord msEx) :=
  ⟨shifted_verify_honest (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot
      goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
      (by norm_num) S₅ dom₅ qPair le_rfl qPair_inj genesis xWord_mem
      msEx_mem ρs,
    ⟨Submodule.mem_top, (masked_completeness_F5 _).2⟩⟩

/-- **The shifted run reduces to the LANDED statement**: the fold-root
transcript and `AccRbrBcs`'s honest increment transcript `msgBcs` produce
the SAME verifier output — the shift changed which roots are sent when, not
what the chain reduces to. `msgBcs_opens`/`msgBcs_word` (CITED) discharge
the increment side. -/
theorem shifted_reduces_as_unshifted_F5 (ρs : Fin 3 → ZMod 5) :
    accReductionBcsShifted_F5.verify () genesis xWord
        (fun c => msgShifted ρs (c : ℕ)) ρs
      = accReductionBcs_F5.verify () genesis xWord msgBcs
          (fun i => ρs i.castSucc) :=
  shifted_verify_eq_unshifted (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
    linRoot goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
    (by norm_num) S₅ dom₅ qPair le_rfl qPair_inj genesis xWord_mem msEx_mem
    msgBcs msgBcs_opens msgBcs_word ρs

/-- **Teeth — the unshifted attribution is IMPOSSIBLE, not merely
unproved**: no single round-0 message synthesizes the first fold root `h_1`
for every draw of `ρ_0`. Under Defs 4.1/4.2's unshifted indexing the
round-0 message precedes `ρ_0`, so committing `h_1 = f₀ + ρ_0 • w_0` there
would require one fixed word equal to a genuinely `ρ_0`-dependent family —
refuted by kernel computation on the landed chain (`msEx 0 ≠ 0`). The shift
is load-bearing. -/
theorem unshifted_misaligns_F5 :
    ¬ ∃ π : BcsMsg (Fin 4 → ZMod 5) (ZMod 5) Unit 2,
        ∀ ρ : ZMod 5,
          bcsWord dom₅ 2 qPair π = partialFold (fun _ => ρ) xWord msEx 1 := by
  rintro ⟨π, hπ⟩
  have h01 : partialFold (fun _ => (0 : ZMod 5)) xWord msEx 1
      = partialFold (fun _ => (1 : ZMod 5)) xWord msEx 1 := by
    rw [← hπ 0, hπ 1]
  have hne : partialFold (fun _ => (0 : ZMod 5)) xWord msEx 1
      ≠ partialFold (fun _ => (1 : ZMod 5)) xWord msEx 1 := by decide
  exact hne h01

/-- The positive contrast: at round 1 — AFTER `ρ_0` — the honest shifted
message commits exactly `h_1` at the transcript's own challenge
(`shiftedMsg_word` instantiated). What no round-0 message can carry, round
1's carries on the nose. -/
theorem shifted_h1_committed_F5 (ρs : Fin 3 → ZMod 5) :
    bcsWord dom₅ 2 qPair (msgShifted ρs 1)
      = partialFold (padSched fun i : Fin 2 => ρs i.castSucc) xWord msEx 1 :=
  shiftedMsg_word S₅ dom₅ le_rfl qPair_inj _ xWord_mem msEx_mem 1

end AccRbrBcsShiftedExample

/-! ## Residual obligation — prose, not a stub

**What CLOSED here.** The lag-respecting carrier `[ACC-rbr-bcs-resid]`(a)
asked for exists: `accReductionBcsShifted` commits each partial fold in the
first round where it is committable (`h_0` challenge-free at round 0,
`h_{i+1}` at round `i+1`, after `ρ_i`), checks every opening plus the
genesis anchor, and outputs the recommitted full fold. The alignment the
shift buys is PROVED: round `c`'s message reads only challenges at rounds
`< c` (`shiftedMsg_committable` via `partialFold_sched_local`), the
round-`k+1` word is the round-`k` word folded by the round-`k` challenge
(`shifted_alignment` via `partialFold_succ`, CITED), consecutive shifted
words return the increment through the seam's `γ⁻¹`-difference map
(`shifted_increment_recovered`), and on honest data the shifted verifier
outputs EXACTLY the landed `accReductionBcs` statement
(`shifted_verify_eq_unshifted` via `partialFold_last` + `foldWords_ofFn`,
CITED). Keystones fire on the landed F₅ chain, and the teeth are a kernel
refutation: no round-0 message synthesizes `h_1` for every `ρ_0`
(`unshifted_misaligns_F5`) while round 1's message carries it exactly
(`shifted_h1_committed_F5`).

**`[ACC-rbr-bcs-shifted-resid]`** — what remains, stated precisely.

* **(a) The adaptive-increment round bound** — inhabiting
  `accRbrKnowledgeSoundBcsShifted` at any useful `εfold`. At the shifted
  round-`i+1` extension `tr‖ρ_{i+1}`, the FRESH challenge is inert for the
  fold data: the increment newly scorable there,
  `w_i = ρ_i⁻¹ • (h_{i+1} − h_i)`, is weighted by the ROUND-`i` challenge,
  which was already fixed when the adversary chose `h_{i+1}`'s root. Def
  4.2's `uniformProb` over the fresh challenge therefore cannot be priced by
  the landed fixed-pair `accSound_rbr` event, whose whole leverage is that
  the tested pair was committed BEFORE the challenge. What is needed is
  either (i) the BCS/ROM commitment extraction — read the committed word out
  of the oracle query log at ROOT time, so `h_{i+1}` is pinned before
  `ρ_{i+1}` and the event re-attaches to a fresh challenge — which lives
  outside `Reduction`'s oracle-free shape (the transcript-layer route); or
  (ii) a genuinely new round bound for "the folded claim is δ-satisfiable
  near an increment committed AFTER its challenge" — the adaptive
  claim-fold-satisfiability event `[ACC-rbr-bcs-resid]`(a)(ii) named. The
  DATA side is closed here (`shifted_increment_recovered`,
  `shifted_verify_eq_unshifted`); the ATTRIBUTION pricing is the residual.
* **(b) The shifted state design.** The intended Def-4.1 state —
  committed-column consistency ∧ the IOR state on the DIFFERENCE transcript
  — hits the zero-challenge wrinkle: at `ρ_c = 0` consecutive folds carry no
  increment information (`γ⁻¹` undefined; honest schedules avoid it with
  probability `1 − 1/|F|`, exactly the `accRbrError` additive term's home),
  while Def 4.1's clauses quantify over ALL transcripts. Plus the boundary
  rounds: round 0 (the genesis recommitment — scored against `R`'s genesis
  clause, no increment to score) and the inert final round (exists to carry
  `h_k`; its error should be 0, but proving its round event empty needs the
  state design). Neither is priced here; both are named.
* **(c) Inherited.** `[ZK-RBR-extract]` open lemma A (sub-unique-decoding
  seam for constrained masks) and the floor `[FS-ROM]`/`[COMMIT-CR]`/`hPG` —
  from `[ACC-rbr-bcs-resid]`(b)(c), unchanged, consumed never claimed.

## Ledger

* `partialFold_mem` / `partialFold_sched_local` — PROVED: folds of codewords
  are codewords; stage `c` reads only challenges `< c`.
* `shiftedMsg` (+ `_opens`, `_word`) — DEFINED/PROVED: the honest fold-root
  message; opens; synthesizes its fold (`recoverFromColumns_sound` CITED).
* `shiftedMsg_committable` + `shifted_alignment` — PROVED (the alignment
  pair): round-`c` messages are prefix-committable, and the round-`k+1` word
  co-occurs with the round-`k` challenge that folded it (`partialFold_succ`
  CITED).
* `shifted_increment_recovered` — PROVED: the seam's `γ⁻¹`-difference map
  returns the increments at the shifted alphabet.
* `accReductionBcsShifted` — DEFINED: `ch.length + 1` rounds, one per fold
  root, opening-checking + genesis-anchoring verifier, last-word output,
  inert final challenge (documented).
* `shifted_verify_honest` / `shifted_verify_eq_unshifted` — PROVED: honest
  runs accepted with the full-fold output; SAME output as `accReductionBcs`
  on the increment transcript (`partialFold_last` + `foldWords_ofFn` CITED).
* `accRbrKnowledgeSoundBcsShifted` — STATED (Def 4.2 at the shifted
  alphabet, statement-first Prop with ATLAS fields): NOT inhabited;
  inhabiting it is `[ACC-rbr-bcs-shifted-resid]`(a)+(b).
* Keystones — `accReductionBcsShifted_F5` (built), `msgShifted`,
  `shifted_completeness_F5` (accepts + satisfies, every draw),
  `shifted_reduces_as_unshifted_F5` (same statement as the landed `msgBcs`
  run), `unshifted_misaligns_F5` (teeth, kernel-computed) +
  `shifted_h1_committed_F5` (the contrast).
* Residual — `[ACC-rbr-bcs-shifted-resid]` (prose above): (a) the
  adaptive-increment round bound (ROM-log or adaptive fold event), (b) the
  shifted state design (zero-challenge wrinkle, boundary rounds), (c)
  inherited lemma A + floor.

`#print axioms` on `shifted_alignment`, `shifted_verify_eq_unshifted`,
`AccRbrBcsShiftedExample.shifted_completeness_F5`,
`AccRbrBcsShiftedExample.shifted_reduces_as_unshifted_F5`,
`AccRbrBcsShiftedExample.unshifted_misaligns_F5`: `propext`,
`Classical.choice`, `Quot.sound` — no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage
