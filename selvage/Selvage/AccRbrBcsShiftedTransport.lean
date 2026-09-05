/-
# Selvage.AccRbrBcsShiftedTransport — census upgrade 5, resolved by RETIRING
the unlinked Def-4.2 object: `accRbrKnowledgeSoundBcsShifted` has a FLOOR OF
ONE for every knowledge state and every extractor, and the deployed-ZK
statement that holds is the log route at the LINKED reduction.

`zkml-research/notes/unit-witness-census.md` §7 item 5 names a half-closed
hole: `Selvage/AccRbrBcsShifted.lean:374` enters Def 4.2 at the constrained-mask
fold-root schedule as a `Prop` and leaves it uninhabited, while
`Selvage/OracleLogLinkedAssembly.lean:461` closes a log-extractor version of the
same content at the true `accRbrError`. The two types, verbatim:

* the demand —
  `accRbrKnowledgeSoundBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d q εfold :=
     ∃ rbr : RbrKnowledgeSoundness (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d q),
       (∀ δ st tr w, rbr.kstate.state δ st tr w = true → ColsConsistent S q tr.rounds) ∧
       ∀ (i : Fin (ch.length + 1)) st, ∀ δ ∈ Set.Ioo 0 δs, rbr.err i st δ ≤ εfold δ`
  — an oracle-free, per-round object at the UNLINKED shifted reduction, whose
  verifier checks every opening, the genesis anchor, and nothing else;
* the supply —
  `linkedAdaptiveIncrementSound_proved errstar hdC hδsC hdt hq hwv hstar :
     LinkedAdaptiveIncrementSound C foldRoot ch hm hch δs hδpos hδone S dom d q wv errstar`,
  i.e. `∃ olr : OracleLogReduction (accReductionBcsShiftedLinked … wv) (linkedStatementSet … wv)
     (accRbrError F errstar), ∀ s, olr.extractLog s = linkedShiftedLogExtractor … s`
  — a ROM-game object at the LINKED reduction (verifier grown by `LinkOpened`
  against the designated family `wv`), over the aligned statement set, with a
  log-reading extractor.

**Decision: RETIRE, with the obstruction proved.** No transport exists because
the demand is FALSE below error one, at every instance with a witness-less
statement whose aggregate is always solvable — and the landed F₅ chain is one:

* `shiftedRbr_floor` — the untethered adversary. The unlinked shifted verifier
  never ties consecutive roots, so a prover that anchors the genesis word,
  commits anything in between, and commits a word SOLVING the aggregate as its
  last message is accepted with a δ-satisfied output at EVERY challenge vector.
  Def 4.2's backward chain then forces the knowledge state to be true at every
  prefix of that adversary's transcript down to the empty one — where Def 4.1
  pins it to `R_{≤δ}`, which the statement does not have. So some round's error
  is `≥ 1`, whatever the state and the extractor. This is the Def-4.2 twin of
  `adaptiveViaLog_accRbrError_false` (`Selvage/OracleLogProgram.lean`): the same
  untethered verifier, priced in the paper's own per-round model.
* `accRbrKnowledgeSoundBcsShifted_one` — the other pole. Every `Reduction`
  carries a Def-4.2 instance at error `1` (`degenerateRbr`: the state that is
  exact at the two ends Def 4.1 pins and false everywhere else), and it meets
  the shifted object's column clause. So the object is inhabited at `εfold ≡ 1`
  and at nothing below it on the window: `foldRoundBound_one` /
  `foldRoundBound_floor`'s pair shape, at the BCS alphabet.
* `AccRbrBcsShiftedTransportExample.shifted_forces_one_F5`,
  `shifted_accRbrError_false_F5` — the floor fired on the landed chain: the
  statement `q2 = 3` at `xWord` (no witness inside `δ < 1/4`), the solver
  `(3 + γ₁) • 1⃗`; the intended price `accRbrError = 1/5` is refuted.
* `shifted_retired_log_stands_F5` — the ledger sentence as a theorem: on ONE
  landed instance the unlinked Def-4.2 object is dead below `1` while the linked
  log object is alive at `1/5` (`linkedAdaptiveIncrementSound_F5`, CITED).

**What remains, named.** `[ACC-rbr-bcs-shifted-linked]` —
`accRbrKnowledgeSoundBcsShiftedLinked`: Def 4.2 at the LINKED reduction, the
oracle-free per-round object the log route's fresh-horn kernel
(`freshAggregateChallenge_injective`) suggests exists. ATLAS fields: satisfiable
at `εfold ≡ 1` (`accRbrKnowledgeSoundBcsShiftedLinked_one`, the same degenerate
state); teeth `linked_zero_false_F5` — at the all-ones designation `εfold ≡ 0`
is FALSE (the fold `xWord + 1⃗ + 1⃗` meets the witness-less aggregate `q2 = 4`
on the nose at the all-ones schedule; a backward chain at error zero would
manufacture a source witness); premise inhabitation
`accReductionBcsShiftedLinked_F5` + `linked_completeness_F5` (CITED). Its
inhabitant at `accRbrError` is the shifted state design
(`[ACC-rbr-bcs-shifted-resid]`(b)), open.

Design record: `zkml-research/notes/shifted-bcs-transport.md`.
-/
import Selvage.OracleLogLinkedAssembly

namespace Minidregg.Selvage

/-! ## The degenerate Def-4.2 instance at error `1` — every reduction has one -/

section Degenerate

variable (r : Reduction)

/-- **The degenerate knowledge state, as a proposition**: exact at the two ends
Def 4.1 pins — `R_{≤δ}` on the empty transcript, accept-with-`R'_{≤δ}` on a
full one — and false on every other transcript. -/
def DegenerateStateProp (δ : ℝ) (st : Stmt r) (tr : Transcript r.PMsg r.Chal)
    (w : r.W) : Prop :=
  (tr.rounds = [] ∧ tr.pending = none ∧ RelaxedMem r.R δ st.idx st.x st.y w) ∨
  (tr.pending = none ∧
    ∃ (πs : Fin r.k → r.PMsg) (ρs : Fin r.k → r.Chal),
      tr.rounds = List.ofFn (fun i => (πs i, ρs i)) ∧
      ∃ (x' : r.X') (y' : Fin r.n' → r.A'),
        r.verify st.idx st.x st.y πs ρs = some (x', y') ∧
        RelaxedMem r.R' δ st.idx x' y' w)

open Classical in
/-- **The degenerate Def-4.1 state of ANY reduction**, all three clauses
proved: the empty transcript reads `R_{≤δ}` (the full clause cannot fire
there, `k > 0`); every pending-message transcript is doomed, so prover moves
preserve doom; the full transcript reads accept-with-`R'_{≤δ}`
(`List.ofFn_injective` pins the messages and challenges). -/
noncomputable def degenerateKState : KStateFn r where
  state := fun δ st tr w => decide (DegenerateStateProp r δ st tr w)
  empty_iff := by
    intro δ hδ st w
    show decide (DegenerateStateProp r δ st ⟨[], none⟩ w) = true ↔ _
    rw [decide_eq_true_iff]
    constructor
    · rintro (⟨-, -, h⟩ | ⟨-, πs, ρs, heq, -⟩)
      · exact h
      · have heq' : ([] : List (r.PMsg × r.Chal))
            = List.ofFn fun i => (πs i, ρs i) := heq
        have hlen : (List.ofFn fun i => (πs i, ρs i)).length = r.k :=
          List.length_ofFn
        rw [← heq'] at hlen
        exact absurd hlen.symm r.k_pos.ne'
    · intro h
      exact Or.inl ⟨rfl, rfl, h⟩
  prover_monotone := by
    intro δ hδ st rs w hlen h π
    show decide (DegenerateStateProp r δ st ⟨rs, some π⟩ w) = false
    rw [decide_eq_false_iff_not]
    rintro (⟨-, hp, -⟩ | ⟨hp, -⟩) <;> exact absurd hp (by simp)
  full_iff := by
    intro δ hδ st πs ρs w
    show decide (DegenerateStateProp r δ st
      ⟨List.ofFn fun i => (πs i, ρs i), none⟩ w) = true ↔ _
    rw [decide_eq_true_iff]
    constructor
    · rintro (⟨hnil, -, -⟩ | ⟨-, πs', ρs', heq, x', y', hver, hrel⟩)
      · have hnil' : (List.ofFn fun i => (πs i, ρs i)) = [] := hnil
        have hlen : (List.ofFn fun i => (πs i, ρs i)).length = r.k :=
          List.length_ofFn
        rw [hnil'] at hlen
        exact absurd hlen.symm r.k_pos.ne'
      · have hfun := List.ofFn_injective heq
        have hπ : πs = πs' := funext fun i => congrArg Prod.fst (congrFun hfun i)
        have hρ : ρs = ρs' := funext fun i => congrArg Prod.snd (congrFun hfun i)
        subst hπ
        subst hρ
        exact ⟨x', y', hver, hrel⟩
    · rintro ⟨x', y', hver, hrel⟩
      exact Or.inr ⟨rfl, πs, ρs, rfl, x', y', hver, hrel⟩

theorem degenerateKState_true_iff (δ : ℝ) (st : Stmt r)
    (tr : Transcript r.PMsg r.Chal) (w : r.W) :
    (degenerateKState r).state δ st tr w = true ↔
      DegenerateStateProp r δ st tr w := by
  classical
  exact decide_eq_true_iff

/-- **Every reduction is Def-4.2 knowledge-sound at error `1`** — the identity
extractor against the degenerate state; a uniform probability is at most `1`.
The universal satisfiable pole for `RbrKnowledgeSoundness`-shaped
obligations: the content of any such obligation is entirely in the error it
demands. -/
noncomputable def degenerateRbr : RbrKnowledgeSoundness r where
  kstate := degenerateKState r
  extract := fun _ _ w => w
  err := fun _ _ _ => 1
  extractTime := fun _ => 0
  extract_sound := fun _ _ _ _ _ _ _ => uniformProb_le_one _

end Degenerate

/-! ## The shifted object's satisfiable pole -/

section ShiftedPoles

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F)) (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F) (d : ℕ)
  (q : Fin t → Fin m)

/-- **Satisfiable at `εfold ≡ 1`**: the degenerate instance meets the shifted
object's column clause — its state is true only on the empty transcript (no
columns owed) or on an ACCEPTED full transcript (every opening verified by
the verifier's first conjunct). -/
theorem accRbrKnowledgeSoundBcsShifted_one :
    accRbrKnowledgeSoundBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d
      q (fun _ => 1) := by
  classical
  refine ⟨degenerateRbr _, ?_, fun _ _ _ _ => le_rfl⟩
  intro δ st tr w hw
  rcases (degenerateKState_true_iff _ δ st tr w).mp hw with
    ⟨hnil, -, -⟩ | ⟨-, πs, ρs, heq, x', y', hver, -⟩
  · rw [hnil]
    exact fun e he => by simp at he
  · rw [heq, colsConsistent_ofFn]
    by_contra hno
    have hnone : (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S
        dom d q).verify st.idx st.x st.y πs ρs = none := by
      show (if (∀ i, ColsOpen S q (πs i)) ∧ (∀ j, (πs 0).cols j = st.y (q j))
          then _ else none) = none
      exact if_neg fun hc => hno hc.1
    rw [hnone] at hver
    cases hver

end ShiftedPoles

/-! ## The untethered adversary at the unlinked shifted verifier -/

section Untethered

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (S : BindingCommitment Root' F (Fin m) Op) (q : Fin t → Fin m)

/-- The honest commitment message of a word at the BCS alphabet: root, the
`t` spot columns, honest opening proofs — `msgBcs`/`shiftedMsg`/`msgOf`'s
shape at an arbitrary word. -/
noncomputable def commitMsg (w : Fin m → F) : BcsMsg Root' F Op t :=
  ⟨S.commit w, fun j => w (q j), fun j => S.openAt w (q j)⟩

omit [Field F] [Fintype F] [DecidableEq F] in
theorem commitMsg_opens (w : Fin m → F) : ColsOpen S q (commitMsg S q w) :=
  fun j => S.verifyOpen_commit w (q j)

omit [Fintype F] [DecidableEq F] in
theorem commitMsg_word (dom : Fin m ↪ F) {d : ℕ} (hdt : d ≤ t)
    (hq : Function.Injective (dom ∘ q)) {w : Fin m → F}
    (hw : w ∈ reedSolomonCode dom d) :
    bcsWord dom d q (commitMsg S q w) = w :=
  recoverFromColumns_sound dom hdt hq hw fun _ => rfl

variable (ch : Chain Root F (Fin m) r)

/-- **The untethered adversary's message at level `c`** of a challenge
schedule `γ`: level `0` anchors the genesis word honestly, the LAST level
commits the solver's word `z` at the restricted schedule (the fold
challenges, read AFTER they were sent), every other level commits zero.
Level `c` reads `γ` only below `c` — it is a legitimate prover strategy. -/
noncomputable def untetheredMsg (f₀ : Fin m → F)
    (z : (Fin ch.length → F) → Fin m → F) (γ : ℕ → F) (c : ℕ) :
    BcsMsg Root' F Op t :=
  if c = 0 then commitMsg S q f₀
  else if c = ch.length then commitMsg S q (z fun i => γ (i : ℕ))
  else commitMsg S q 0

/-- The adversary's completed rounds after `i` levels of the schedule `γ`. -/
noncomputable def untetheredRounds (f₀ : Fin m → F)
    (z : (Fin ch.length → F) → Fin m → F) (γ : ℕ → F) :
    ℕ → List (BcsMsg Root' F Op t × F)
  | 0 => []
  | i + 1 => untetheredRounds f₀ z γ i ++ [(untetheredMsg S q ch f₀ z γ i, γ i)]

omit [Fintype F] [DecidableEq F] in
theorem untetheredRounds_length (f₀ : Fin m → F)
    (z : (Fin ch.length → F) → Fin m → F) (γ : ℕ → F) (i : ℕ) :
    (untetheredRounds S q ch f₀ z γ i).length = i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [untetheredRounds, List.length_append, ih, List.length_singleton]

omit [Fintype F] [DecidableEq F] in
/-- **Committability**: level `c` reads the schedule only at rounds `< c`. -/
theorem untetheredMsg_local (f₀ : Fin m → F)
    (z : (Fin ch.length → F) → Fin m → F) {γ γ' : ℕ → F} {c : ℕ}
    (h : ∀ j < c, γ j = γ' j) :
    untetheredMsg S q ch f₀ z γ c = untetheredMsg S q ch f₀ z γ' c := by
  unfold untetheredMsg
  by_cases h0 : c = 0
  · rw [if_pos h0, if_pos h0]
  · rw [if_neg h0, if_neg h0]
    by_cases hc' : c = ch.length
    · rw [if_pos hc', if_pos hc']
      have hγ : (fun i : Fin ch.length => γ (i : ℕ))
          = fun i : Fin ch.length => γ' (i : ℕ) :=
        funext fun i => h i (by rw [hc']; exact i.isLt)
      rw [hγ]
    · rw [if_neg hc', if_neg hc']

omit [Fintype F] [DecidableEq F] in
theorem untetheredRounds_local (f₀ : Fin m → F)
    (z : (Fin ch.length → F) → Fin m → F) {γ γ' : ℕ → F} {i : ℕ}
    (h : ∀ j < i, γ j = γ' j) :
    untetheredRounds S q ch f₀ z γ i = untetheredRounds S q ch f₀ z γ' i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h' : ∀ j < i, γ j = γ' j := fun j hj => h j (Nat.lt_succ_of_lt hj)
    rw [untetheredRounds, untetheredRounds, ih h',
      untetheredMsg_local S q ch f₀ z h', h i (Nat.lt_succ_self i)]

omit [Fintype F] [DecidableEq F] in
/-- **The round-`i` extension, on-strategy**: replacing the schedule's
coordinate `i` by the fresh challenge `ρ` and completing one more level
appends exactly `(the level-`i` message, ρ)` to the level-`i` prefix. -/
theorem untetheredRounds_update (f₀ : Fin m → F)
    (z : (Fin ch.length → F) → Fin m → F) (γ : ℕ → F) (i : ℕ) (ρ : F) :
    untetheredRounds S q ch f₀ z (Function.update γ i ρ) (i + 1)
      = untetheredRounds S q ch f₀ z γ i
          ++ [(untetheredMsg S q ch f₀ z γ i, ρ)] := by
  have hloc : ∀ j < i, Function.update γ i ρ j = γ j :=
    fun j hj => Function.update_of_ne (Nat.ne_of_lt hj) _ _
  rw [untetheredRounds, untetheredRounds_local S q ch f₀ z hloc,
    untetheredMsg_local S q ch f₀ z hloc, Function.update_self]

omit [Fintype F] [DecidableEq F] in
theorem untetheredRounds_ofFn (f₀ : Fin m → F)
    (z : (Fin ch.length → F) → Fin m → F) (γ : ℕ → F) (i : ℕ) :
    untetheredRounds S q ch f₀ z γ i
      = List.ofFn fun j : Fin i =>
          (untetheredMsg S q ch f₀ z γ (j : ℕ), γ (j : ℕ)) := by
  induction i with
  | zero => rw [List.ofFn_zero]; rfl
  | succ i ih =>
    rw [untetheredRounds, ih, List.ofFn_succ', List.concat_eq_append]
    rfl

variable (C : Submodule F (Fin m → F)) (foldRoot : Root → F → Root → Root)
  (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1) (dom : Fin m ↪ F) (d : ℕ)

/-- **The unlinked shifted verifier accepts the untethered run at EVERY
schedule**, outputting the aggregate with the solver's word: every message
opens, the genesis anchor holds, and the last message's synthesized word is
`z` at the fold challenges. No relation between consecutive roots is ever
checked — `[ORACLE-LOG-program]`'s diagnosis, at the Def-4.2 alphabet. -/
theorem untethered_verify (hdt : d ≤ t) (hq : Function.Injective (dom ∘ q))
    (A₀ : AccClaim Root F (Fin m) r) (f₀ : Fin m → F)
    (z : (Fin ch.length → F) → Fin m → F)
    (hz : ∀ γv, z γv ∈ reedSolomonCode dom d) (γ : ℕ → F) :
    (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d
        q).verify () A₀ f₀
        (fun j : Fin (ch.length + 1) => untetheredMsg S q ch f₀ z γ (j : ℕ))
        (fun j => γ (j : ℕ))
      = some (aggregate foldRoot (padSched fun i : Fin ch.length => γ (i : ℕ))
            A₀ ch,
          z fun i => γ (i : ℕ)) := by
  classical
  have hopen : ∀ j : Fin (ch.length + 1),
      ColsOpen S q (untetheredMsg S q ch f₀ z γ (j : ℕ)) := by
    intro j
    unfold untetheredMsg
    split_ifs <;> exact commitMsg_opens S q _
  have hanchor : ∀ j,
      (untetheredMsg S q ch f₀ z γ ((0 : Fin (ch.length + 1)) : ℕ)).cols j
        = f₀ (q j) := by
    intro j
    rw [Fin.val_zero, untetheredMsg, if_pos rfl]
    rfl
  show (if (∀ j : Fin (ch.length + 1),
          ColsOpen S q (untetheredMsg S q ch f₀ z γ (j : ℕ))) ∧
        (∀ j, (untetheredMsg S q ch f₀ z γ
          ((0 : Fin (ch.length + 1)) : ℕ)).cols j = f₀ (q j)) then
      some (aggregate foldRoot
          (padSched fun i : Fin ch.length =>
            γ ((i.castSucc : Fin (ch.length + 1)) : ℕ)) A₀ ch,
        bcsWord dom d q (untetheredMsg S q ch f₀ z γ
          ((Fin.last ch.length : Fin (ch.length + 1)) : ℕ)))
    else none) = _
  rw [if_pos ⟨hopen, hanchor⟩]
  have hlast : untetheredMsg S q ch f₀ z γ
      ((Fin.last ch.length : Fin (ch.length + 1)) : ℕ)
      = commitMsg S q (z fun i => γ (i : ℕ)) := by
    rw [Fin.val_last, untetheredMsg, if_neg hch.ne', if_pos rfl]
  rw [hlast, commitMsg_word S q dom hdt hq (hz _)]
  rfl

/-- **The floor: `accRbrKnowledgeSoundBcsShifted` forces a round error `≥ 1`
— for EVERY knowledge state and EVERY extractor.** Data: a statement with NO
`R_{≤δ}` witness, and a solver `z` returning, at every fold schedule, an RS
codeword satisfying the aggregate. The untethered adversary's full
transcripts are all accepted with satisfied output, so the full state is
true at every schedule (`full_iff`). If every round error were `< 1`, the
round bound at the adversary's level-`i` prefix would force the state true
there too — the event `{state(prefix) false ∧ state(extension) true}` is
CERTAIN otherwise, `prover_monotone` carrying doom from the pending-free
prefix to the pending one — down to the empty transcript, where `empty_iff`
manufactures the witness the statement does not have.

Read against `accRbrKnowledgeSoundBcsShifted`'s own teeth: the file said any
`εfold < 1` rules out the DEGENERATE state; this says it rules out EVERY
state. The reason is structural: the shifted verifier's output word is the
last message's synthesized word, untethered from the genesis and the links —
the same untethering `adaptiveViaLog_accRbrError_false` priced in the ROM
game, here in the paper's per-round model. -/
theorem shiftedRbr_floor
    (rbr : RbrKnowledgeSoundness
      (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d q))
    (hdt : d ≤ t) (hq : Function.Injective (dom ∘ q))
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) δs)
    (st : Stmt (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S
      dom d q))
    (hno : ∀ w, ¬ RelaxedMem
      (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d q).R
      δ st.idx st.x st.y w)
    (z : (Fin ch.length → F) → Fin m → F)
    (hz : ∀ γv, z γv ∈ reedSolomonCode dom d ∧
      AccClaim.Satisfies C (aggregate foldRoot (padSched γv) st.x ch) (z γv)) :
    ∃ i : Fin (ch.length + 1), 1 ≤ rbr.err i st δ := by
  classical
  have hk : (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom
    d q).k = ch.length + 1 := rfl
  by_contra hlt
  push Not at hlt
  -- the full transcript is alive at every schedule
  have hfull : ∀ γ : ℕ → F, ∃ w : Fin ch.length → Fin m → F,
      rbr.kstate.state δ st
        ⟨untetheredRounds S q ch st.y z γ (ch.length + 1), none⟩ w = true := by
    intro γ
    refine ⟨fun _ _ => 0, ?_⟩
    rw [untetheredRounds_ofFn]
    refine (rbr.kstate.full_iff δ hδ st
      (fun j : Fin (ch.length + 1) => untetheredMsg S q ch st.y z γ (j : ℕ))
      (fun j => γ (j : ℕ)) _).mpr ?_
    refine ⟨_, _, untethered_verify S q ch C foldRoot hm hch δs hδpos hδone dom
      d hdt hq st.x st.y z (fun γv => (hz γv).1) γ, ?_⟩
    refine ⟨z fun i => γ (i : ℕ), (hz _).2, ?_⟩
    rw [fracHamming_self]
    exact hδ.1.le
  -- one step back along the adversary's strategy
  have hstep : ∀ i, i ≤ ch.length →
      (∀ γ : ℕ → F, ∃ w : Fin ch.length → Fin m → F,
        rbr.kstate.state δ st
          ⟨untetheredRounds S q ch st.y z γ (i + 1), none⟩ w = true) →
      ∀ γ : ℕ → F, ∃ w : Fin ch.length → Fin m → F,
        rbr.kstate.state δ st
          ⟨untetheredRounds S q ch st.y z γ i, none⟩ w = true := by
    intro i hi ih γ
    by_contra hnone
    push Not at hnone
    have hdoom : ∀ w, rbr.kstate.state δ st
        ⟨untetheredRounds S q ch st.y z γ i,
          some (untetheredMsg S q ch st.y z γ i)⟩ w = false := by
      intro w
      refine rbr.kstate.prover_monotone δ hδ st _ w ?_
        (Bool.eq_false_iff.mpr (hnone w)) _
      rw [untetheredRounds_length]
      omega
    have hb := rbr.extract_sound δ hδ st ⟨i, by omega⟩
      (untetheredRounds S q ch st.y z γ i)
      (untetheredRounds_length S q ch st.y z γ i)
      (untetheredMsg S q ch st.y z γ i)
    have hone : (1 : ℝ) ≤ rbr.err ⟨i, by omega⟩ st δ := by
      refine le_trans (le_of_eq (uniformProb_eq_one ?_).symm) hb
      intro ρ
      obtain ⟨w, hw⟩ := ih (Function.update γ i ρ)
      rw [untetheredRounds_update S q ch st.y z γ i ρ] at hw
      exact ⟨w, hdoom _, hw⟩
    exact absurd hone (not_le.mpr (hlt _))
  -- descend from the full transcript to the empty one
  have hall : ∀ j i, i + j = ch.length + 1 →
      ∀ γ : ℕ → F, ∃ w : Fin ch.length → Fin m → F,
        rbr.kstate.state δ st
          ⟨untetheredRounds S q ch st.y z γ i, none⟩ w = true := by
    intro j
    induction j with
    | zero =>
      intro i hi
      have hi' : i = ch.length + 1 := by omega
      subst hi'
      exact hfull
    | succ j ih =>
      intro i hi
      exact hstep i (by omega) (ih (i + 1) (by omega))
  obtain ⟨w, hw⟩ := hall (ch.length + 1) 0 (by omega) (fun _ => 0)
  exact hno w ((rbr.kstate.empty_iff δ hδ st w).mp hw)

/-- **The Prop itself has a floor of one**: any `εfold` the shifted object
holds at is `≥ 1` at every `δ` on the window where a witness-less,
always-solvable statement exists. -/
theorem accRbrKnowledgeSoundBcsShifted_forces_one (εfold : ℝ → ℝ)
    (h : accRbrKnowledgeSoundBcsShifted C foldRoot ch hm hch δs hδpos hδone S
      dom d q εfold)
    (hdt : d ≤ t) (hq : Function.Injective (dom ∘ q))
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) δs)
    (st : Stmt (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S
      dom d q))
    (hno : ∀ w, ¬ RelaxedMem
      (accReductionBcsShifted C foldRoot ch hm hch δs hδpos hδone S dom d q).R
      δ st.idx st.x st.y w)
    (z : (Fin ch.length → F) → Fin m → F)
    (hz : ∀ γv, z γv ∈ reedSolomonCode dom d ∧
      AccClaim.Satisfies C (aggregate foldRoot (padSched γv) st.x ch) (z γv)) :
    1 ≤ εfold δ := by
  obtain ⟨rbr, -, herr⟩ := h
  obtain ⟨i, hi⟩ := shiftedRbr_floor S q ch C foldRoot hm hch δs hδpos hδone
    dom d rbr hdt hq hδ st hno z hz
  exact le_trans hi (herr i st δ hδ)

end Untethered

/-! ## `[ACC-rbr-bcs-shifted-linked]` — Def 4.2 at the LINKED reduction, named -/

section Linked

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

variable (C : Submodule F (Fin m → F)) (foldRoot : Root → F → Root → Root)
  (ch : Chain Root F (Fin m) r) (hm : 0 < m) (hch : 0 < ch.length)
  (δs : ℝ) (hδpos : 0 < δs) (hδone : δs ≤ 1)
  (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F) (d : ℕ)
  (q : Fin t → Fin m)

/-- **Def 4.2 at the LINKED shifted reduction — the STATEMENT**
(`[ACC-rbr-bcs-shifted-linked]`): `accRbrKnowledgeSoundBcsShifted`'s shape
at `accReductionBcsShiftedLinked … wv`, the verifier that ties every
consecutive root pair to the designated link word through `LinkOpened`. This
is the oracle-free, per-round object the log route's fresh-horn kernel
(`freshAggregateChallenge_injective`) suggests, and the one whose inhabitant
would let `OB2_depth_composition_nonneg_proved` / `fsKeystone_proved` price
the deployed-ZK shape instead of the bespoke `(t + k)` assembly.

ATLAS keystone fields (obligation):
* satisfiable: `accRbrKnowledgeSoundBcsShiftedLinked_one` — at `εfold ≡ 1`,
  the degenerate state.
* teeth: `AccRbrBcsShiftedTransportExample.linked_zero_false_F5` — at the
  all-ones designation on the landed chain, `εfold ≡ 0` is FALSE: a
  backward chain at error zero would manufacture a witness for `q2 = 3` at
  `xWord`.
* premise-inhabitation: `accReductionBcsShiftedLinked_F5` is BUILT and its
  honest run ACCEPTED (`linked_completeness_F5`, CITED).
Its inhabitant at `accRbrError` is the shifted state design —
`[ACC-rbr-bcs-shifted-resid]`(b), re-homed here; open. -/
def accRbrKnowledgeSoundBcsShiftedLinked (wv : Fin ch.length → Fin m → F)
    (εfold : ℝ → ℝ) : Prop :=
  ∃ rbr : RbrKnowledgeSoundness
      (accReductionBcsShiftedLinked C foldRoot ch hm hch δs hδpos hδone S dom d
        q wv),
    (∀ (δ : ℝ)
        (st : Stmt (accReductionBcsShiftedLinked C foldRoot ch hm hch δs hδpos
          hδone S dom d q wv))
        (tr : Transcript (BcsMsg Root' F Op t) F)
        (w : Fin ch.length → Fin m → F),
        rbr.kstate.state δ st tr w = true → ColsConsistent S q tr.rounds) ∧
    ∀ (i : Fin (ch.length + 1))
      (st : Stmt (accReductionBcsShiftedLinked C foldRoot ch hm hch δs hδpos
        hδone S dom d q wv)),
      ∀ δ ∈ Set.Ioo (0 : ℝ) δs, rbr.err i st δ ≤ εfold δ

/-- **Satisfiable at `εfold ≡ 1`**: the degenerate instance, whose full
clause reads the linked verifier's acceptance — openings first. -/
theorem accRbrKnowledgeSoundBcsShiftedLinked_one
    (wv : Fin ch.length → Fin m → F) :
    accRbrKnowledgeSoundBcsShiftedLinked C foldRoot ch hm hch δs hδpos hδone S
      dom d q wv (fun _ => 1) := by
  classical
  refine ⟨degenerateRbr _, ?_, fun _ _ _ _ => le_rfl⟩
  intro δ st tr w hw
  rcases (degenerateKState_true_iff _ δ st tr w).mp hw with
    ⟨hnil, -, -⟩ | ⟨-, πs, ρs, heq, x', y', hver, -⟩
  · rw [hnil]
    exact fun e he => by simp at he
  · rw [heq, colsConsistent_ofFn]
    by_contra hno
    have hnone : (accReductionBcsShiftedLinked C foldRoot ch hm hch δs hδpos
        hδone S dom d q wv).verify st.idx st.x st.y πs ρs = none := by
      show (if (∀ i, ColsOpen S q (πs i)) ∧ (∀ j, (πs 0).cols j = st.y (q j)) ∧
          ∀ i : Fin ch.length,
            LinkOpened S q (S.commit (wv i)) (πs i.castSucc) (πs i.succ)
              (ρs i.castSucc) then _ else none) = none
      exact if_neg fun hc => hno hc.1
    rw [hnone] at hver
    cases hver

end Linked

/-! ## The backward chain at error zero — a generic tooth-maker -/

/-- A uniform probability that is `≤ 0` has an EMPTY event — the converse of
`uniformProb_false` (`Selvage/Depth.lean`) and the contrapositive of
`AccRbrFold.uniformProb_pos_of_witness`, restated here because that file is
outside this import cone; owner to hoist both into `Depth.lean`. -/
theorem not_of_uniformProb_le_zero {C : Type} [Fintype C] {p : C → Prop}
    (h : uniformProb C p ≤ 0) : ∀ c, ¬ p c := by
  intro c hc
  unfold uniformProb at h
  have hnum : (0 : ℝ) < (Nat.card {c : C // p c} : ℝ) := by
    have : Nonempty {c : C // p c} := ⟨⟨c, hc⟩⟩
    exact_mod_cast (Nat.card_pos : 0 < Nat.card {c : C // p c})
  have hden : (0 : ℝ) < (Fintype.card C : ℝ) := by
    exact_mod_cast (@Fintype.card_pos C _ ⟨c⟩)
  exact absurd h (not_le.mpr (div_pos hnum hden))

/-- **At round errors `≤ 0` the Def-4.2 chain is deterministic**: a witness
alive at any pending-free prefix un-folds, round by round, to a witness alive
at the empty transcript. Each round event is EMPTY (a single witness would
make its uniform probability positive, `not_of_uniformProb_le_zero`), so the
extractor's output is alive at the pending prefix, and `prover_monotone`
(contrapositive) carries it to the pending-free one. -/
theorem rbr_chain_of_err_zero {r : Reduction} (rbr : RbrKnowledgeSoundness r)
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) r.δstar) (st : Stmt r)
    (hzero : ∀ i, rbr.err i st δ ≤ 0) :
    ∀ rs : List (r.PMsg × r.Chal), rs.length ≤ r.k →
      (∃ w, rbr.kstate.state δ st ⟨rs, none⟩ w = true) →
      ∃ w, rbr.kstate.state δ st ⟨[], none⟩ w = true := by
  intro rs
  induction rs using List.reverseRecOn with
  | nil => exact fun _ h => h
  | append_singleton rs' e ih =>
    rintro hlen ⟨w, hw⟩
    obtain ⟨π, ρ⟩ := e
    have hlt : rs'.length < r.k := by
      rw [List.length_append, List.length_singleton] at hlen
      omega
    have hb := rbr.extract_sound δ hδ st ⟨rs'.length, hlt⟩ rs' rfl π
    have hpre : rbr.kstate.state δ st ⟨rs', some π⟩
        (rbr.extract st ⟨rs' ++ [(π, ρ)], none⟩ w) = true := by
      by_contra hf
      exact not_of_uniformProb_le_zero (le_trans hb (hzero ⟨rs'.length, hlt⟩))
        ρ ⟨w, Bool.eq_false_iff.mpr hf, hw⟩
    have hfree : rbr.kstate.state δ st ⟨rs', none⟩
        (rbr.extract st ⟨rs' ++ [(π, ρ)], none⟩ w) = true := by
      by_contra hf
      have := rbr.kstate.prover_monotone δ hδ st rs' _ hlt
        (Bool.eq_false_iff.mpr hf) π
      rw [this] at hpre
      exact Bool.noConfusion hpre
    exact ih (by rw [List.length_append] at hlen; omega) ⟨_, hfree⟩

/-! ## Keystones on the landed F₅ chain -/

namespace AccRbrBcsShiftedTransportExample

open RSExample LCExample AccExample ZkHidingExample ZkExtractionExample
  CommitExample AccRbrBcsExample AccRbrBcsShiftedExample AccSoundRbrExample
  OracleLogLinkedExample OracleLogLinkedAssemblyExample

/-- The witness-less genesis: `q2 = 3`, while `q2 xWord = 2` and nothing
inside `δ < 1/4` of `xWord` differs from it. -/
def farGenesis : AccClaim (ZMod 5) (ZMod 5) (Fin 4) 1 := ⟨0, fun _ => (q2, 3)⟩

/-- The statement of the shifted F₅ reduction at `farGenesis` over `xWord`. -/
noncomputable def farSt : Stmt accReductionBcsShifted_F5 :=
  ⟨(), farGenesis, xWord⟩

/-- **No source witness inside the window**: the `δ`-ball around `xWord` is
`{xWord}` for `δ < 1/4` (`one_div_card_le_relDist`), and `q2 xWord = 2 ≠ 3`;
the first conjunct of `R` does not read `w`. -/
theorem farSt_no_witness {δ : ℝ} (hδ : δ < 1 / 4)
    (w : Fin 2 → Fin 4 → ZMod 5) :
    ¬ RelaxedMem accReductionBcsShifted_F5.R δ () farGenesis xWord w := by
  rintro ⟨ystar, ⟨⟨-, hq⟩, -⟩, hclose⟩
  have hy : xWord = ystar := by
    by_contra hne
    have h1 := one_div_card_le_relDist (F := ZMod 5) hne
    rw [← fracHamming_eq_relDist, Fintype.card_fin] at h1
    have h4 : (1 : ℝ) / 4 ≤ fracHamming xWord ystar := by
      simpa using h1
    linarith
  subst hy
  exact absurd (hq 0) (by decide)

/-- The solver: at fold challenges `γv`, the word `(3 + γ₁) • 1⃗` — an RS
codeword with `q2 = 3 + γ₀·0 + γ₁·1`, the aggregate's target on the nose. -/
def farZ (γv : Fin 2 → ZMod 5) : Fin 4 → ZMod 5 := (3 + γv 1) • oneWord

theorem farZ_solves (γv : Fin 2 → ZMod 5) :
    farZ γv ∈ reedSolomonCode dom₅ 2 ∧
    AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
      (aggregate linRoot (padSched γv) farGenesis goodChain) (farZ γv) := by
  have hagg : ∀ γs : ℕ → ZMod 5,
      aggregate linRoot γs farGenesis goodChain
        = foldClaims linRoot (foldClaims linRoot farGenesis claim₀ (γs 0))
            claim₁ (γs 1) := fun γs => rfl
  refine ⟨Submodule.smul_mem _ _ oneWord_mem, Submodule.mem_top, fun jj => ?_⟩
  rw [hagg]
  show q2 (farZ γv) = 3 + padSched γv 0 * 0 + padSched γv 1 * 1
  have h1 : padSched γv 1 = γv 1 := padSched_lt γv (by norm_num)
  rw [h1]
  unfold farZ
  rw [map_smul, smul_eq_mul, show q2 oneWord = (1 : ZMod 5) from rfl]
  ring

/-- **The floor, FIRED on the landed chain**: any `εfold` the shifted object
holds at is `≥ 1` on the whole window. -/
theorem shifted_forces_one_F5 (εfold : ℝ → ℝ)
    (h : accRbrKnowledgeSoundBcsShifted
      (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
      (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
      S₅ dom₅ 2 qPair εfold) :
    ∀ δ ∈ Set.Ioo (0 : ℝ) (1 / 16), 1 ≤ εfold δ := by
  intro δ hδ
  exact accRbrKnowledgeSoundBcsShifted_forces_one S₅ qPair goodChain
    (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot (by norm_num) (by decide)
    (1 / 16) (by norm_num) (by norm_num) dom₅ 2 εfold h le_rfl qPair_inj hδ
    farSt (farSt_no_witness (by linarith [hδ.2])) farZ farZ_solves

/-- **The intended price is dead at the Def-4.2 seam**: the shifted object at
`εfold = accRbrError = 1/5` is FALSE on the landed instance. -/
theorem shifted_accRbrError_false_F5 :
    ¬ accRbrKnowledgeSoundBcsShifted
      (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
      (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
      S₅ dom₅ 2 qPair (accRbrError (ZMod 5) (fun _ => 0)) := by
  intro h
  have h1 := shifted_forces_one_F5 _ h (1 / 32)
    (by rw [Set.mem_Ioo]; exact ⟨by norm_num, by norm_num⟩)
  rw [accRbrError_zero_five] at h1
  norm_num at h1

/-- **The ledger sentence as a theorem**: on the landed F₅ chain the unlinked
Def-4.2 object is dead below error `1` while the linked log object stands at
`accRbrError = 1/5` with its extractor pinned
(`linkedAdaptiveIncrementSound_F5`, CITED). The log route supersedes; nothing
is half-closed. -/
theorem shifted_retired_log_stands_F5 :
    (∀ εfold : ℝ → ℝ,
      accRbrKnowledgeSoundBcsShifted
        (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
        (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
        S₅ dom₅ 2 qPair εfold →
      ∀ δ ∈ Set.Ioo (0 : ℝ) (1 / 16), 1 ≤ εfold δ) ∧
    LinkedAdaptiveIncrementSound
      (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
      (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
      S₅ dom₅ 2 qPair msEx (fun _ => 0) :=
  ⟨shifted_forces_one_F5, linkedAdaptiveIncrementSound_F5⟩

/-! ### Teeth for the linked obligation: `εfold ≡ 0` is false -/

/-- The linked F₅ reduction at the all-ones designation `wv ≡ 1⃗`. -/
@[reducible] noncomputable def linkedOnes_F5 : Reduction :=
  accReductionBcsShiftedLinked (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
    linRoot goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
    (by norm_num) S₅ dom₅ 2 qPair (fun _ => oneWord)

/-- The witness-less statement at the linked reduction. -/
noncomputable def farStLinked : Stmt linkedOnes_F5 := ⟨(), farGenesis, xWord⟩

/-- **The all-ones schedule is lucky**: the honest fold `xWord + 1⃗ + 1⃗` has
`q2 = 4`, and the aggregate of `farGenesis` at `(1, 1)` asks for
`3 + 1·0 + 1·1 = 4` — the witness-less claim is met exactly, on the nose. -/
theorem farFold_satisfies_ones :
    AccClaim.Satisfies (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
      (aggregate linRoot (padSched fun _ : Fin 2 => (1 : ZMod 5)) farGenesis
        goodChain)
      (flatFold (padSched fun _ : Fin 2 => (1 : ZMod 5)) xWord
        fun _ : Fin 2 => oneWord) :=
  ⟨Submodule.mem_top, by decide⟩

/-- **Teeth for `[ACC-rbr-bcs-shifted-linked]`**: at the all-ones designation
on the landed chain, `εfold ≡ 0` is FALSE. The linked verifier accepts the
honest shifted run of `xWord` with increments `1⃗` at the all-ones schedule
(`linked_verify_honest`, CITED) with a satisfied output, so the full state is
alive; a backward chain at error zero (`rbr_chain_of_err_zero`) would land a
witness at the empty transcript for a statement that has none. The linked
object's price is genuinely positive — it is the `1/|F|` lucky-fold mass the
log route's fresh horn pays. -/
theorem linked_zero_false_F5 :
    ¬ accRbrKnowledgeSoundBcsShiftedLinked
      (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
      (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
      S₅ dom₅ 2 qPair (fun _ => oneWord) (fun _ => 0) := by
  rintro ⟨rbr, -, herr⟩
  have hδ : (1 / 32 : ℝ) ∈ Set.Ioo (0 : ℝ) (1 / 16) := by
    rw [Set.mem_Ioo]
    exact ⟨by norm_num, by norm_num⟩
  have hfull : ∃ w : Fin 2 → Fin 4 → ZMod 5,
      rbr.kstate.state (1 / 32) farStLinked
        (Transcript.ofFull
          (fun c : Fin 3 => shiftedMsg S₅ qPair
            (padSched fun i : Fin 2 => (fun _ : Fin 3 => (1 : ZMod 5)) i.castSucc)
            xWord (fun _ : Fin 2 => oneWord) (c : ℕ))
          (fun _ => 1)) w = true := by
    refine ⟨fun _ _ => 0, ?_⟩
    refine (rbr.kstate.full_iff (1 / 32) hδ farStLinked _ _ _).mpr ?_
    refine ⟨_, _, linked_verify_honest (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
      linRoot goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
      (by norm_num) S₅ dom₅ 2 qPair le_rfl qPair_inj farGenesis xWord_mem
      (fun _ => oneWord_mem) (fun _ => 1), ?_⟩
    refine ⟨_, farFold_satisfies_ones, ?_⟩
    exact le_trans (le_of_eq (fracHamming_self _)) (by norm_num)
  obtain ⟨w, hw⟩ := rbr_chain_of_err_zero rbr hδ farStLinked
    (fun i => herr i farStLinked (1 / 32) hδ) _
    (by rw [List.length_ofFn]; exact le_rfl) hfull
  exact farSt_no_witness (by norm_num) w
    ((rbr.kstate.empty_iff (1 / 32) hδ farStLinked w).mp hw)

end AccRbrBcsShiftedTransportExample

/-! ## Axiom audit -/

/-- info: 'Minidregg.Selvage.degenerateRbr' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms degenerateRbr
/-- info: 'Minidregg.Selvage.accRbrKnowledgeSoundBcsShifted_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accRbrKnowledgeSoundBcsShifted_one
/-- info: 'Minidregg.Selvage.untethered_verify' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms untethered_verify
/-- info: 'Minidregg.Selvage.shiftedRbr_floor' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms shiftedRbr_floor
/-- info: 'Minidregg.Selvage.accRbrKnowledgeSoundBcsShifted_forces_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accRbrKnowledgeSoundBcsShifted_forces_one
/-- info: 'Minidregg.Selvage.accRbrKnowledgeSoundBcsShiftedLinked_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms accRbrKnowledgeSoundBcsShiftedLinked_one
/-- info: 'Minidregg.Selvage.rbr_chain_of_err_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms rbr_chain_of_err_zero
/-- info: 'Minidregg.Selvage.AccRbrBcsShiftedTransportExample.shifted_forces_one_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AccRbrBcsShiftedTransportExample.shifted_forces_one_F5
/-- info: 'Minidregg.Selvage.AccRbrBcsShiftedTransportExample.shifted_accRbrError_false_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AccRbrBcsShiftedTransportExample.shifted_accRbrError_false_F5
/-- info: 'Minidregg.Selvage.AccRbrBcsShiftedTransportExample.shifted_retired_log_stands_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AccRbrBcsShiftedTransportExample.shifted_retired_log_stands_F5
/-- info: 'Minidregg.Selvage.AccRbrBcsShiftedTransportExample.linked_zero_false_F5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms AccRbrBcsShiftedTransportExample.linked_zero_false_F5

end Minidregg.Selvage
