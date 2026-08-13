/-
# Selvage.AccRbrBcs — [ACC-rbr-bcs]: the native RBR instance at the DEPLOYED
BCS/root alphabet — `AccRbrInstance`'s construction re-run with
`PMsg = recommitted root + opened columns + opening proofs`.

`Selvage/AccRbrInstance.lean` closed `[ZK-RBR-game-resid]` at the IOR resolution
and named `[ACC-rbr-bcs]` precisely: the `Reduction` whose prover messages are
the DEPLOYED message alphabet (a recommitted root, its `t` opened columns, the
opening proofs), whose knowledge state demands COMMITTED-COLUMN CONSISTENCY
(so binding pins the words — `binding_columns`), and whose extractor
synthesizes the round word from one execution's columns (`recoverFromColumns`
through binding — the inner step of `seamCounterfactual`, composed end to end
in `extractChain_committed_seam`). This file builds that instance. The algebra
is landed (`Selvage/ZkExtraction.lean`, `Selvage/Commitment.lean`, `Selvage/Erasure.lean`)
and is CITED, never re-derived; what is new here is only the Def-4.1/4.2
packaging at the root alphabet.

* `BcsMsg` / `ColsOpen` / `ColsConsistent` / `bcsWord` / `bcsRounds` — the
  deployed alphabet: a round message is `(root, cols, ops)`; its word is
  SYNTHESIZED by erasure decoding the opened columns
  (`recoverFromColumns`, CITED); a transcript over messages reads as a
  transcript over words (`bcsRounds`). `bcsWord_committed`: binding pins the
  synthesis — a message whose openings verify against a root committing a
  codeword synthesizes THAT codeword (`binding_columns` +
  `recoverFromColumns_sound`, both CITED).
* `accReductionBcs` — the accumulator chain as a WARP `Reduction` at the BCS
  alphabet: `k = ch.length` rounds, `Chal = F`, `PMsg = BcsMsg`; the verifier
  CHECKS EVERY OPENING (`verifyOpen` — this verifier genuinely rejects, unlike
  the IOR instance's) and on success outputs the aggregate and the fold of the
  synthesized words. Source/target relations unchanged from `accReduction`
  (genesis + aligned-channel links; word-level aggregate).
* `accKStateBcs` — Def 4.1 at the root alphabet, three clauses PROVED: the
  state is COMMITTED-COLUMN CONSISTENCY (every completed round's columns
  verify against its root) ∧ the IOR knowledge state on the SYNTHESIZED
  transcript. Empty: columns vacuous, collapses to `R_{≤δ}`. Prover moves:
  pending-blind. Full: collapses to accept-with-`R'_{≤δ}` — where "accept"
  now includes the opening checks.
* `accRbrKnowledgeSoundBcs` — Def 4.2 at the root alphabet, `extract_sound`
  PROVED: the extractor peels the round's message, synthesizes its word
  through the columns, and decodes at the canonical radius `δ⋆`
  (`decodeLink`, reused); the per-round `∃ w`-event refines into the SAME
  fold event `accSound_rbr` (CITED) prices — the falseness choreography of
  `AccRbrInstance` runs verbatim with the synthesized word in the sent
  word's place. `err = accRbrError`, no slack.
* `wAt_bcs` + `accRbrBcs_backward_committed` — the backward composition
  (Construction B.5) at the BCS alphabet is the IOR composition on the
  synthesized transcript (`wAt` commutes with `bcsRounds`), so on an honestly
  committed chain — roots committing the (masked) round words, columns
  verified, words in the code — it returns EXACTLY the committed word family,
  through binding, citing `accRbr_backward_masked`. The F₅ keystone
  `bcs_extract_is_seam` then identifies its output with
  `extractChain ∘ seamCounterfactual`'s on the landed instance
  (`seam_extraction_committed_F5`, CITED): the native BCS extractor IS the
  seam object, not a lookalike.
* `accFsSound_bcs` — `FsOfRbrSound` (PROVED, `fsKeystone_proved`) applied to
  the BCS pair: Fiat–Shamir OF THE DEPLOYED TRANSCRIPT SHAPE — the proof
  string carries roots + columns + proofs, and the oracle hashes those, not
  full words — is straightline knowledge-sound at `(t + k)·accRbrError`.

**Honest scope — what closes and what remains.** The BCS-alphabet quadruple —
root-and-columns messages, an opening-checking verifier, the
committed-column-consistent knowledge state, the binding-composed synthesis
extractor, `extract_sound` at the landed `accRbrError` price, and FS on top —
is BUILT and PROVED here, no sorry, no `Prop := True`. Its deployment
coverage is the WHOLE-CODE-MASK / UNIQUE-DECODING regime (`t ≥ d`), where the
per-round recommitted words are exactly the objects the ZK schedule may
commit and open (`seam_hiding_coexist_at_d`: at `t = d` the columns determine
the masked word AND hide the witness). What remains is `[ACC-rbr-bcs-resid]`,
named precisely at the bottom: (a) the FOLD-ROOT schedule — the constrained-
mask deployment opens columns of the recommitted PARTIAL FOLDS, whose roots
lag their challenge by one message (`h_{i+1}` is committed only after `ρ_i`),
while Defs 4.1/4.2 score `ρ_i` at round `i`'s extension; re-attributing the
knowledge state to the lagged fold roots needs either the BCS oracle-log
extraction (outside `Reduction`'s shape) or a claim-fold-satisfiability round
bound that is NOT the landed fixed-pair `accSound_rbr` event — the column
DATA is seam-equivalent (exhibited by `bcs_extract_is_seam`), the root
attribution is the open packaging; (b) the sub-unique-decoding seam for
constrained masks — `[ZK-RBR-extract]` open lemma A, inherited unchanged;
(c) the floor — `[FS-ROM]`/`[COMMIT-CR]`/`hPG`, inherited unchanged.

**Keystones** (F₅, landed objects REUSED): `accReductionBcs_F5`/`accRbrBcs_F5`
— the BCS instance BUILT on `goodChain` at `C = ⊤`, commitment
`CommitExample.S₅`, columns `qPair` at `t = d = 2`, every floor hypothesis
discharged by landed witnesses; `bcs_state_alive` (the state fires TRUE on
the FULL honest committed transcript — openings verified, fold synthesized,
aggregate satisfied); `bcs_err_computes` (`err ≡ 1/5`); `bcs_extract_masked`
(the backward composition returns the masked words exactly, any seed);
`bcs_extract_is_seam` (its output = `extractChain ∘ seamCounterfactual`
through `S₅` binding — the seam citation made real); `bcs_fs_fired` (FS at
the deployed alphabet, `(t + 2)·(1/5)`); `bcs_root_pins_word` +
`bcs_teeth_columns` (teeth: a reused root forces the SAME synthesized word
through binding — generic and computed). No `sorry`, no vacuous
`Prop := True`.
-/
import Selvage.Rbr
import Selvage.FiatShamir
import Selvage.Commitment
import Selvage.ZkExtraction
import Selvage.AccRbrInstance

namespace Minidregg.Selvage

/-! ## The deployed message alphabet: root + opened columns + opening proofs -/

/-- **A BCS round message**: the recommitted root, the `t` opened column
values, and their opening proofs — the DEPLOYED alphabet (`[ACC-rbr-bcs]`'s
`PMsg`). The full word is never sent; it is SYNTHESIZED from the columns
(`bcsWord`) and PINNED by the root (`bcsWord_committed`). -/
structure BcsMsg (Root' F Op : Type) (t : ℕ) : Type where
  /-- The recommitted root. -/
  root : Root'
  /-- The opened column values at the `t` spot-checked positions. -/
  cols : Fin t → F
  /-- The opening proofs (Merkle paths in deployment). -/
  ops : Fin t → Op

section BcsAlphabet

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

/-- The message's openings all verify against its root — the per-message
commitment check the deployed verifier runs. Stated at `OpeningScheme`,
because running the verifier consumes no binding: a scheme that equivocates
still HAS accepted openings, and refusing to say so is exactly how an
adversary's opening attempt gets erased before a collision reduction can read
it. Binding-typed call sites are unchanged — `BindingCommitment` coerces. -/
def ColsOpen (S : OpeningScheme Root' F (Fin m) Op) (q : Fin t → Fin m)
    (π : BcsMsg Root' F Op t) : Prop :=
  ∀ j, S.verifyOpen π.root (q j) (π.cols j) (π.ops j)

/-- **Committed-column consistency** of a transcript prefix: every completed
round's columns open from its root — the clause `[ACC-rbr-bcs]` demanded of
the knowledge state. -/
def ColsConsistent (S : OpeningScheme Root' F (Fin m) Op)
    (q : Fin t → Fin m) (rs : List (BcsMsg Root' F Op t × F)) : Prop :=
  ∀ e ∈ rs, ColsOpen S q e.1

omit [Field F] [Fintype F] [DecidableEq F] in
theorem colsConsistent_ofFn (S : OpeningScheme Root' F (Fin m) Op)
    (q : Fin t → Fin m) {kk : ℕ} (πs : Fin kk → BcsMsg Root' F Op t)
    (ρs : Fin kk → F) :
    ColsConsistent S q (List.ofFn fun i => (πs i, ρs i))
      ↔ ∀ i, ColsOpen S q (πs i) := by
  unfold ColsConsistent
  constructor
  · intro h i
    exact h (πs i, ρs i) (by rw [List.mem_ofFn]; exact ⟨i, rfl⟩)
  · intro h e he
    rw [List.mem_ofFn] at he
    obtain ⟨i, hi⟩ := he
    rw [← hi]
    exact h i

/-- **The word a message carries**: erasure-decode the opened columns —
`recoverFromColumns` (CITED, `Selvage/Erasure.lean`), exactly the inner step of
`seamCounterfactual`. A pure function of the message; the root's role is to
PIN it (`bcsWord_committed`). -/
noncomputable def bcsWord (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m)
    (π : BcsMsg Root' F Op t) : Fin m → F :=
  recoverFromColumns dom d q π.cols

omit [Fintype F] [DecidableEq F] in
/-- **Synthesis needs column AGREEMENT, not binding.** If the message's
columns are literally the codeword's symbols at the opened positions, erasure
recovery (`recoverFromColumns_sound`, CITED) returns that codeword — no root,
no verifier, no commitment scheme appears in this statement at all.

This is the honest core of `bcsWord_committed` below, separated out because
the two hypotheses are cryptographically very different: `hcols` is a fact
about what the adversary actually submitted, while binding is a CR-priced
assumption about what it could have submitted. A reduction that wants to
extract a collision from an unequal submitted column must keep that column;
if binding is consumed first, the column has already been rewritten and the
collision branch is unreachable. -/
theorem bcsWord_of_colsExact (dom : Fin m ↪ F) {d : ℕ} (hdt : d ≤ t)
    {q : Fin t → Fin m} (hq : Function.Injective (dom ∘ q)) {wd : Fin m → F}
    (hwd : wd ∈ reedSolomonCode dom d) {π : BcsMsg Root' F Op t}
    (hcols : ∀ j, π.cols j = wd (q j)) :
    bcsWord dom d q π = wd :=
  recoverFromColumns_sound dom hdt hq hwd hcols

omit [Fintype F] [DecidableEq F] in
/-- **Binding pins the synthesis**: a message whose openings verify against a
root committing a codeword synthesizes THAT codeword — `binding_columns`
(CITED) attaches the columns, then `bcsWord_of_colsExact` decodes them. The
committed-column route of `[ACC-rbr-bcs]`, per message. Binding enters here
and ONLY here: its whole job is to discharge `hcols`. -/
theorem bcsWord_committed (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) {d : ℕ} (hdt : d ≤ t) {q : Fin t → Fin m}
    (hq : Function.Injective (dom ∘ q)) {wd : Fin m → F}
    (hwd : wd ∈ reedSolomonCode dom d) {π : BcsMsg Root' F Op t}
    (hrt : π.root = S.commit wd) (hver : ColsOpen S q π) :
    bcsWord dom d q π = wd :=
  bcsWord_of_colsExact dom hdt hq hwd (binding_columns S hrt hver)

omit [Fintype F] [DecidableEq F] in
/-- **The retained opening attempt.** At a scheme with no binding field, an
accepted column that DISAGREES with the committed word is a real object: two
openings of one root at one position carrying different values. This is the
`BindingFailure` shape the deployed Merkle reduction consumes, stated here
where the message alphabet lives. `bcsWord_committed` cannot produce it — its
binding premise refutes the conclusion. -/
def ColumnEquivocation (S : OpeningScheme Root' F (Fin m) Op)
    (q : Fin t → Fin m) (π : BcsMsg Root' F Op t) (wd : Fin m → F) : Prop :=
  ∃ j, S.verifyOpen π.root (q j) (π.cols j) (π.ops j) ∧
    S.verifyOpen π.root (q j) (wd (q j)) (S.openAt wd (q j)) ∧
    π.cols j ≠ wd (q j)

omit [Fintype F] [DecidableEq F] in
/-- **The honest split, binding-free.** An accepted message against a root
that commits `wd` either has exactly `wd`'s columns — and therefore
synthesizes `wd` — or exhibits a retained equivocation at a named position.
No scheme property is assumed; the disjunction is where a deployment pays for
collision-resistance instead of assuming it. -/
theorem bcsWord_or_columnEquivocation (S : OpeningScheme Root' F (Fin m) Op)
    (dom : Fin m ↪ F) {d : ℕ} (hdt : d ≤ t) {q : Fin t → Fin m}
    (hq : Function.Injective (dom ∘ q)) {wd : Fin m → F}
    (hwd : wd ∈ reedSolomonCode dom d) {π : BcsMsg Root' F Op t}
    (hrt : π.root = S.commit wd) (hver : ColsOpen S q π) :
    bcsWord dom d q π = wd ∨ ColumnEquivocation S q π wd := by
  by_cases hcols : ∀ j, π.cols j = wd (q j)
  · exact Or.inl (bcsWord_of_colsExact dom hdt hq hwd hcols)
  · obtain ⟨j, hj⟩ := not_forall.mp hcols
    exact Or.inr ⟨j, hver j, by rw [hrt]; exact S.verifyOpen_commit wd (q j), hj⟩

omit [Fintype F] [DecidableEq F] in
/-- Binding kills the second branch. This is the exact step that makes a
binding-typed carrier unable to host a collision reduction: at a
`BindingCommitment` the retained attempt does not merely go unused, it is
REFUTED. -/
theorem not_columnEquivocation (S : BindingCommitment Root' F (Fin m) Op)
    {q : Fin t → Fin m} {π : BcsMsg Root' F Op t} {wd : Fin m → F} :
    ¬ColumnEquivocation S q π wd := by
  rintro ⟨j, hleft, hright, hne⟩
  exact hne (S.binding π.root (q j) (π.cols j) (wd (q j)) (π.ops j)
    (S.openAt wd (q j)) hleft hright)

omit [Fintype F] [DecidableEq F] in
/-- **Teeth — a root binds its columns, the columns determine the word**: two
messages sharing one root whose openings both verify carry EQUAL column
values (`BindingCommitment.binding`, CITED, pointwise) and hence EQUAL
synthesized words. The message alphabet cannot equivocate below the word
alphabet. -/
theorem bcs_root_pins_word (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) (d : ℕ) {q : Fin t → Fin m}
    {π π' : BcsMsg Root' F Op t} (hroot : π.root = π'.root)
    (h : ColsOpen S q π) (h' : ColsOpen S q π') :
    π.cols = π'.cols ∧ bcsWord dom d q π = bcsWord dom d q π' := by
  have hc : π.cols = π'.cols := funext fun j =>
    S.binding π.root (q j) (π.cols j) (π'.cols j) (π.ops j) (π'.ops j) (h j)
      (by rw [hroot]; exact h' j)
  exact ⟨hc, by unfold bcsWord; rw [hc]⟩

/-- Read a message transcript as a word transcript: each round's message is
replaced by its synthesized word, challenges untouched. -/
noncomputable def bcsRounds (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m)
    (rs : List (BcsMsg Root' F Op t × F)) : List ((Fin m → F) × F) :=
  rs.map fun e => (bcsWord dom d q e.1, e.2)

omit [Fintype F] [DecidableEq F] in
@[simp] theorem bcsRounds_length (dom : Fin m ↪ F) (d : ℕ)
    (q : Fin t → Fin m) (rs : List (BcsMsg Root' F Op t × F)) :
    (bcsRounds dom d q rs).length = rs.length := by
  unfold bcsRounds
  rw [List.length_map]

omit [Fintype F] [DecidableEq F] in
@[simp] theorem bcsRounds_nil (dom : Fin m ↪ F) (d : ℕ)
    (q : Fin t → Fin m) :
    bcsRounds dom d q ([] : List (BcsMsg Root' F Op t × F)) = [] := rfl

omit [Fintype F] [DecidableEq F] in
theorem bcsRounds_append (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m)
    (rs : List (BcsMsg Root' F Op t × F)) (π : BcsMsg Root' F Op t) (ρ : F) :
    bcsRounds dom d q (rs ++ [(π, ρ)])
      = bcsRounds dom d q rs ++ [(bcsWord dom d q π, ρ)] := by
  unfold bcsRounds
  rw [List.map_append]
  rfl

omit [Fintype F] [DecidableEq F] in
theorem bcsRounds_ofFn (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m)
    {kk : ℕ} (πs : Fin kk → BcsMsg Root' F Op t) (ρs : Fin kk → F) :
    bcsRounds dom d q (List.ofFn fun i => (πs i, ρs i))
      = List.ofFn fun i => (bcsWord dom d q (πs i), ρs i) := by
  unfold bcsRounds
  rw [List.map_ofFn]
  rfl

omit [Fintype F] [DecidableEq F] in
theorem bcsRounds_take (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m)
    (rs : List (BcsMsg Root' F Op t × F)) (n : ℕ) :
    bcsRounds dom d q (rs.take n) = (bcsRounds dom d q rs).take n := by
  unfold bcsRounds
  rw [List.map_take]

end BcsAlphabet

/-! ## `accReductionBcs` — the chain at the deployed alphabet -/

section AccBcsInstance

variable {Root Root' Op : Type} {F : Type} [Field F] [Fintype F]
  [DecidableEq F] {m r t : ℕ}

open Classical in
/-- **The accumulator chain as a WARP reduction at the DEPLOYED (BCS/root)
alphabet** — `[ACC-rbr-bcs]`'s owed carrier: `k = ch.length` rounds, challenge
alphabet `F`, prover message a `BcsMsg` (recommitted root + `t` opened
columns + opening proofs). The verifier CHECKS EVERY OPENING against its root
(`verifyOpen` — unlike the IOR instance, this verifier genuinely rejects) and
on success outputs the challenge-determined aggregate together with the fold
of the SYNTHESIZED words (`bcsWord` — erasure decoding of the columns).
Source and target relations are `accReduction`'s, unchanged: genesis +
aligned-channel link witnessing on the source side, the word-level aggregate
on the target side. -/
@[reducible] noncomputable def accReductionBcs (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m) : Reduction where
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
  k := ch.length
  k_pos := hch
  PMsg := BcsMsg Root' F Op t
  Chal := F
  pmsgNonempty := ⟨⟨S.commit 0, fun _ => 0, fun j => S.openAt 0 (q j)⟩⟩
  chalFintype := inferInstance
  chalNonempty := ⟨0⟩
  δstar := δs
  δstar_pos := hδpos
  δstar_le_one := hδone
  verify := fun _ A₀ f₀ πs ρs =>
    if ∀ i, ColsOpen S q (πs i) then
      some (aggregate foldRoot (padSched ρs) A₀ ch,
        foldWords (padSched ρs) f₀ (List.ofFn fun i => bcsWord dom d q (πs i)))
    else none

/-! ## The committed-column-consistent knowledge state -/

/-- **The BCS knowledge-state proposition**: COMMITTED-COLUMN CONSISTENCY
(every completed round's columns verify against its root — the clause that
lets binding pin the words) ∧ the IOR knowledge state (`AccStateProp`,
reused) on the SYNTHESIZED transcript (`bcsRounds`). Pending messages are
read through the same synthesis, and the state never inspects them
(pending-blindness rides on `AccStateProp`'s). -/
def AccStatePropBcs (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (S : BindingCommitment Root' F (Fin m) Op) (dom : Fin m ↪ F) (d : ℕ)
    (q : Fin t → Fin m) (δ : ℝ) (A₀ : AccClaim Root F (Fin m) r)
    (f₀ : Fin m → F) (rs : List (BcsMsg Root' F Op t × F))
    (pend : Option (BcsMsg Root' F Op t)) (w : Fin ch.length → Fin m → F) :
    Prop :=
  ColsConsistent S q rs ∧
    AccStateProp C foldRoot ch δ A₀ f₀ (bcsRounds dom d q rs)
      (pend.map (bcsWord dom d q)) w

open Classical in
/-- **The knowledge state function at the BCS alphabet** (WARP Def 4.1), all
three clauses PROVED — `accKState`'s proofs re-run on the synthesized
transcript with the committed-column conjunct threaded through: `empty_iff`
(no rounds, no columns owed; collapses to `R_{≤δ}`), `prover_monotone`
(pending-blind — neither conjunct reads the dangling message), `full_iff`
(the verifier's opening checks ARE the state's column conjunct, and the
word-level clause collapses to accept-with-`R'_{≤δ}` through
`chainClaim_ofFn`/`chainWord_ofFn` on the synthesized rounds). -/
noncomputable def accKStateBcs (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m) :
    KStateFn (accReductionBcs C foldRoot ch hm hch δs hδpos hδone S dom d q)
    where
  state := fun δ st tr w =>
    decide (AccStatePropBcs C foldRoot ch S dom d q δ st.x st.y tr.rounds
      tr.pending w)
  empty_iff := by
    intro δ hδ st w
    simp only [Transcript.empty, decide_eq_true_eq]
    unfold AccStatePropBcs AccStateProp RelaxedMem
    constructor
    · rintro ⟨-, ⟨w', hd, hs⟩, hrest⟩
      have hrem : ∀ k : Fin ch.length, LinkAligned C st.x ch k (w k) := by
        rcases hrest with ⟨h0, -⟩ | hrem
        · exact absurd h0 (Nat.ne_of_lt hch)
        · exact fun k => hrem k (Nat.zero_le _)
      refine ⟨w', ⟨hs, hrem⟩, ?_⟩
      rw [fracHamming_eq_relDist]
      exact hd
    · rintro ⟨ystar, ⟨hsat, hlinks⟩, hdist⟩
      rw [fracHamming_eq_relDist] at hdist
      exact ⟨fun e he => absurd he (by simp),
        ⟨ystar, hdist, hsat⟩, Or.inr fun k _ => hlinks k⟩
  prover_monotone := by
    intro δ hδ st rs w hlen h π
    rw [decide_eq_false_iff_not] at h ⊢
    intro hP
    apply h
    obtain ⟨hcols, hfold, hrest⟩ := hP
    refine ⟨hcols, hfold, ?_⟩
    rcases hrest with ⟨-, hpend⟩ | hrem
    · exact absurd hpend (by simp)
    · exact Or.inr hrem
  full_iff := by
    intro δ hδ st πs ρs w
    simp only [Transcript.ofFull, decide_eq_true_eq]
    unfold AccStatePropBcs AccStateProp
    have hmap : bcsRounds dom d q (List.ofFn fun i => (πs i, ρs i))
        = List.ofFn fun i => (bcsWord dom d q (πs i), ρs i) :=
      bcsRounds_ofFn dom d q πs ρs
    have hlen : (bcsRounds dom d q
        (List.ofFn fun i => (πs i, ρs i))).length = ch.length := by
      rw [bcsRounds_length, List.length_ofFn]
    constructor
    · rintro ⟨hcols, hfold, -⟩
      refine ⟨aggregate foldRoot (padSched ρs) st.x ch,
        foldWords (padSched ρs) st.y
          (List.ofFn fun i => bcsWord dom d q (πs i)), ?_, ?_⟩
      · rw [if_pos ((colsConsistent_ofFn S q πs ρs).mp hcols)]
      · obtain ⟨w', hd, hs⟩ := hfold
        refine ⟨w', ?_, ?_⟩
        · rw [hmap, chainClaim_ofFn] at hs
          exact hs
        · rw [fracHamming_eq_relDist]
          rw [hmap, chainWord_ofFn] at hd
          exact hd
    · rintro ⟨x', y', heq, hrel⟩
      by_cases hall : ∀ i, ColsOpen S q (πs i)
      · rw [if_pos hall] at heq
        have heq' : (aggregate foldRoot (padSched ρs) st.x ch,
            foldWords (padSched ρs) st.y
              (List.ofFn fun i => bcsWord dom d q (πs i))) = (x', y') :=
          Option.some.inj heq
        obtain ⟨hx, hy⟩ := Prod.mk.injEq .. ▸ heq'
        subst hx
        subst hy
        obtain ⟨ystar, hsat, hdist⟩ := hrel
        refine ⟨(colsConsistent_ofFn S q πs ρs).mpr hall,
          ⟨ystar, ?_, ?_⟩, Or.inl ⟨hlen, rfl⟩⟩
        · rw [hmap, chainWord_ofFn, ← fracHamming_eq_relDist]
          exact hdist
        · rw [hmap, chainClaim_ofFn]
          exact hsat
      · rw [if_neg hall] at heq
        exact absurd heq (by simp)

open Classical in
/-- The state, unfolded — the shape the soundness proof manipulates. -/
theorem accKStateBcs_state_eq (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m) (δ : ℝ)
    (st : Stmt (accReductionBcs C foldRoot ch hm hch δs hδpos hδone S dom d q))
    (tr : Transcript (BcsMsg Root' F Op t) F)
    (w : Fin ch.length → Fin m → F) :
    (accKStateBcs C foldRoot ch hm hch δs hδpos hδone S dom d q).state δ st
        tr w
      = decide (AccStatePropBcs C foldRoot ch S dom d q δ st.x st.y tr.rounds
          tr.pending w) := rfl

/-! ## The round extractor: synthesize the word, decode at the canonical
radius -/

/-- **The BCS round extractor**: read the extended transcript's last message,
SYNTHESIZE its word from the opened columns (`bcsWord` — through binding this
is the committed word), and install its `decodeLink`-decoding as the round's
link witness — `accExtract` (reused) on the synthesized transcript.
Straightline and δ-oblivious, exactly as at the IOR resolution. -/
noncomputable def accExtractBcs (C : Submodule F (Fin m → F))
    (A₀ : AccClaim Root F (Fin m) r) (ch : Chain Root F (Fin m) r) (ρ₀ : ℝ)
    (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m)
    (tr : Transcript (BcsMsg Root' F Op t) F)
    (w : Fin ch.length → Fin m → F) : Fin ch.length → Fin m → F :=
  accExtract C A₀ ch ρ₀ ⟨bcsRounds dom d q tr.rounds, none⟩ w

/-- The extractor on a one-round extension, in closed form. -/
theorem accExtractBcs_append (C : Submodule F (Fin m → F))
    (A₀ : AccClaim Root F (Fin m) r) (ch : Chain Root F (Fin m) r) (ρ₀ : ℝ)
    (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m)
    {rs : List (BcsMsg Root' F Op t × F)} {j : ℕ} (hj : rs.length = j)
    (hlt : j < ch.length) (π : BcsMsg Root' F Op t) (ρ : F)
    (w : Fin ch.length → Fin m → F) :
    accExtractBcs C A₀ ch ρ₀ dom d q ⟨rs ++ [(π, ρ)], none⟩ w
      = Function.update w ⟨j, hlt⟩
          (decodeLink C A₀ ch ρ₀ ⟨j, hlt⟩ (bcsWord dom d q π)) := by
  show accExtract C A₀ ch ρ₀ ⟨bcsRounds dom d q (rs ++ [(π, ρ)]), none⟩ w = _
  rw [bcsRounds_append]
  exact accExtract_append C A₀ ch ρ₀ (by rw [bcsRounds_length]; exact hj) hlt
    (bcsWord dom d q π) ρ w

/-! ## `accRbrKnowledgeSoundBcs` — Def 4.2 at the deployed alphabet -/

/-- **The Def-4.2 instance at the BCS alphabet** — `[ACC-rbr-bcs]`'s owed
quadruple: `kstate = accKStateBcs` (committed-column-consistent),
`extract = accExtractBcs` (synthesize the round word from the columns, decode
at the canonical radius `δ⋆`), `err = accRbrError` (the landed round price,
no slack), and `extract_sound` PROVED by the SAME refinement as the IOR
instance with the synthesized word in the sent word's place:

* a knowledge-state witness alive at the extended transcript carries the fold
  event at the fresh challenge on the SYNTHESIZED transcript
  (`chainWord_append`/`chainClaim_append` through `bcsRounds_append`);
* the extractor's output dead at the shorter transcript forces the falseness
  package `hfar` for the pair (synthesized running fold, synthesized round
  word) — the accumulator component or the decoder component;
* when neither doom holds the round event is EMPTY — the alive witness's
  column consistency restricts to the prefix and its remaining links rebuild
  the shorter state through the decoder.

The probability bound is `accSound_rbr` (CITED) verbatim; the mutual-CA floor
rides as hypotheses exactly as at the IOR resolution. -/
noncomputable def accRbrKnowledgeSoundBcs (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m) {dC Bstar : ℝ}
    (errstar : ℝ → ℝ)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hBstar : δs ≤ 1 - Bstar) (hdC2 : δs ≤ dC / 2)
    (hstar : ∀ δ ∈ Set.Ioo (0 : ℝ) δs, 0 ≤ errstar δ) :
    RbrKnowledgeSoundness
      (accReductionBcs C foldRoot ch hm hch δs hδpos hδone S dom d q) where
  kstate := accKStateBcs C foldRoot ch hm hch δs hδpos hδone S dom d q
  extract := fun st tr w => accExtractBcs C st.x ch δs dom d q tr w
  err := fun _i _st δ => accRbrError F errstar δ
  extractTime := fun _ => 0
  extract_sound := by
    classical
    intro δ hδ st i rs hlen π
    haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    have hi : rs.length < ch.length := by
      rw [hlen]
      exact i.isLt
    have hδB : δ < 1 - Bstar := lt_of_lt_of_le hδ.2 hBstar
    have hδC : δ < dC / 2 := lt_of_lt_of_le hδ.2 hdC2
    have hlt' : (bcsRounds dom d q rs).length < ch.length := by
      rw [bcsRounds_length]
      exact hi
    have hidx : (⟨(bcsRounds dom d q rs).length, hlt'⟩ : Fin ch.length)
        = i := Fin.ext (by
      show (bcsRounds dom d q rs).length = (i : ℕ)
      rw [bcsRounds_length, hlen])
    -- the alive fold conjunct IS the accSound_rbr event, on the synthesized
    -- transcript
    have hstep : ∀ ρ : F,
        FoldTracks C foldRoot ch δ st.x st.y
            (bcsRounds dom d q (rs ++ [(π, ρ)])) ↔
          ∃ w', relDist (chainWord st.y (bcsRounds dom d q rs)
              + ρ • bcsWord dom d q π) w' ≤ δ ∧
            AccClaim.Satisfies C
              (foldClaims foldRoot
                (chainClaim foldRoot st.x ch (bcsRounds dom d q rs))
                (ch.get i).claim ρ) w' := by
      intro ρ
      unfold FoldTracks
      rw [bcsRounds_append, chainWord_append,
        chainClaim_append foldRoot st.x ch (bcsWord dom d q π) ρ hlt', hidx]
    by_cases hdoom : FoldTracks C foldRoot ch δ st.x st.y
        (bcsRounds dom d q rs) ∧
        LinkAligned C st.x ch i (decodeLink C st.x ch δs i (bcsWord dom d q π))
    · -- no doom: the round event is EMPTY — the alive witness rebuilds the
      -- shorter state through the decoder
      refine le_trans (le_of_eq (uniformProb_false fun ρ hev => ?_))
        (accRbrError_nonneg (hstar δ hδ))
      obtain ⟨w, hdead, halive⟩ := hev
      rw [accKStateBcs_state_eq, decide_eq_true_eq] at halive
      rw [accKStateBcs_state_eq, decide_eq_false_iff_not] at hdead
      apply hdead
      show AccStatePropBcs C foldRoot ch S dom d q δ st.x st.y rs (some π)
        (accExtractBcs C st.x ch δs dom d q ⟨rs ++ [(π, ρ)], none⟩ w)
      obtain ⟨hcols, hfold, hrest⟩ := halive
      refine ⟨fun e he => hcols e (List.mem_append_left _ he), hdoom.1,
        Or.inr ?_⟩
      rw [accExtractBcs_append C st.x ch δs dom d q hlen i.isLt π ρ w]
      intro k hk
      have hk' : rs.length ≤ (k : ℕ) := by
        rwa [bcsRounds_length] at hk
      rcases eq_or_ne k (⟨(i : ℕ), i.isLt⟩ : Fin ch.length) with rfl | hne
      · rw [Function.update_self]
        exact hdoom.2
      · rw [Function.update_of_ne hne]
        have hkv : (k : ℕ) ≠ rs.length := by
          rw [hlen]
          exact fun hc => hne (Fin.ext hc)
        have hlen1 : (bcsRounds dom d q (rs ++ [(π, ρ)])).length
            = rs.length + 1 := by
          rw [bcsRounds_length]
          simp
        rcases hrest with ⟨hfull, -⟩ | hrem
        · rw [hlen1] at hfull
          have := k.isLt
          omega
        · refine hrem k ?_
          rw [hlen1]
          omega
    · -- doom: the event refines into the fold event, priced by accSound_rbr
      have hfar : ∀ u ∈ C, ∀ v ∈ C,
          relDist (chainWord st.y (bcsRounds dom d q rs)) u ≤ δ →
          relDist (bcsWord dom d q π) v ≤ δ →
          ∃ j, ¬((chainClaim foldRoot st.x ch
                (bcsRounds dom d q rs)).weights j u
              = (chainClaim foldRoot st.x ch (bcsRounds dom d q rs)).targets
                  j ∧
            (chainClaim foldRoot st.x ch (bcsRounds dom d q rs)).weights j v
              = (ch.get i).claim.targets j) := by
        intro u hu v hv hfu hgv
        by_contra hcon
        push Not at hcon
        rcases not_and_or.mp hdoom with hnF | hnD
        · exact hnF ⟨u, hfu, hu, fun j => (hcon j).1⟩
        · refine hnD (decodeLink_sat C st.x ch δs i (bcsWord dom d q π)
            ⟨v, ⟨hv, fun j => ?_⟩, le_trans hgv hδ.2.le⟩)
          have hj := (hcon j).2
          rwa [congrFun (chainClaim_weights foldRoot st.x ch
            (bcsRounds dom d q rs)) j] at hj
      have hsound := accSound_rbr (C := C) foldRoot hdC hMCA hδ.1 hδB hδC hfar
      refine le_trans (uniformProb_mono ?_) hsound
      rintro ρ ⟨w, -, halive⟩
      rw [accKStateBcs_state_eq, decide_eq_true_eq] at halive
      exact (hstep ρ).mp halive.2.1

/-! ## The backward composition at the BCS alphabet -/

/-- **`wAt` commutes with the synthesis**: the BCS instance's Construction-B.5
witness chain equals the IOR instance's on the synthesized transcript — the
backward composition never sees the roots except through the per-round word
synthesis. The bridge that lets `accRbr_backward_masked` (CITED) carry the
BCS extraction. -/
theorem wAt_bcs (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m) {dC Bstar : ℝ}
    (errstar : ℝ → ℝ)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hBstar : δs ≤ 1 - Bstar) (hdC2 : δs ≤ dC / 2)
    (hstar : ∀ δ ∈ Set.Ioo (0 : ℝ) δs, 0 ≤ errstar δ)
    (st : Stmt (accReductionBcs C foldRoot ch hm hch δs hδpos hδone S dom d q))
    (L : List (BcsMsg Root' F Op t × F)) (w' : Fin ch.length → Fin m → F)
    (i : ℕ) :
    wAt (accRbrKnowledgeSoundBcs C foldRoot ch hm hch δs hδpos hδone S dom d
        q errstar hdC hMCA hBstar hdC2 hstar) st L w' i
      = wAt (accRbrKnowledgeSound C foldRoot ch hm hch δs hδpos hδone errstar
          hdC hMCA hBstar hdC2 hstar) ⟨(), st.x, st.y⟩
          (bcsRounds dom d q L) w' i := by
  have key : ∀ nn ii : ℕ, L.length ≤ ii + nn →
      wAt (accRbrKnowledgeSoundBcs C foldRoot ch hm hch δs hδpos hδone S dom
          d q errstar hdC hMCA hBstar hdC2 hstar) st L w' ii
        = wAt (accRbrKnowledgeSound C foldRoot ch hm hch δs hδpos hδone
            errstar hdC hMCA hBstar hdC2 hstar) ⟨(), st.x, st.y⟩
            (bcsRounds dom d q L) w' ii := by
    intro nn
    induction nn with
    | zero =>
      intro ii hii
      rw [wAt_of_le _ _ _ _ (by omega : L.length ≤ ii),
        wAt_of_le _ _ _ _ (by rw [bcsRounds_length]; omega)]
    | succ nn ih =>
      intro ii hii
      by_cases h : L.length ≤ ii
      · rw [wAt_of_le _ _ _ _ h,
          wAt_of_le _ _ _ _ (by rw [bcsRounds_length]; exact h)]
      · have h' : ii < L.length := Nat.not_le.mp h
        have hlt2 : ii < (bcsRounds dom d q L).length := by
          rw [bcsRounds_length]
          exact h'
        rw [wAt_of_lt _ _ _ _ h',
          wAt_of_lt (accRbrKnowledgeSound C foldRoot ch hm hch δs hδpos
              hδone errstar hdC hMCA hBstar hdC2 hstar)
            ⟨(), st.x, st.y⟩ (bcsRounds dom d q L) w' hlt2,
          ih (ii + 1) (by omega)]
        show accExtract C st.x ch δs
            ⟨bcsRounds dom d q ((L.take (ii + 1))), none⟩ _
          = accExtract C st.x ch δs
            ⟨(bcsRounds dom d q L).take (ii + 1), none⟩ _
        rw [bcsRounds_take]
  exact key L.length i (by omega)

/-- **The BCS backward composition returns the committed words, exactly** —
Construction B.5 at the deployed alphabet, on any transcript whose messages'
roots commit codewords that witness their links and whose openings all
verify: the synthesized words are the committed ones (`bcsWord_committed` —
binding + erasure recovery, CITED), so the composition is
`accRbr_backward_masked` (CITED) on the synthesized transcript and returns
the committed word family on the nose, for every seed. On the deployed ZK
chain those committed words are the MASKED words — the theorem-backed extract
target `[ZK-RBR-extract]` lemma B fixed. -/
theorem accRbrBcs_backward_committed (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) {d : ℕ} (q : Fin t → Fin m) {dC Bstar : ℝ}
    (errstar : ℝ → ℝ)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hBstar : δs ≤ 1 - Bstar) (hdC2 : δs ≤ dC / 2)
    (hstar : ∀ δ ∈ Set.Ioo (0 : ℝ) δs, 0 ≤ errstar δ)
    (hdt : d ≤ t) (hq : Function.Injective (dom ∘ q))
    (st : Stmt (accReductionBcs C foldRoot ch hm hch δs hδpos hδone S dom d q))
    (ms : Fin ch.length → Fin m → F) (γv : Fin ch.length → F)
    (πs : Fin ch.length → BcsMsg Root' F Op t)
    (hroot : ∀ k, (πs k).root = S.commit (ms k))
    (hopen : ∀ k, ColsOpen S q (πs k))
    (hmem : ∀ k, ms k ∈ reedSolomonCode dom d)
    (halign : ∀ k, LinkAligned C st.x ch k (ms k))
    (w' : Fin ch.length → Fin m → F) :
    wAt (accRbrKnowledgeSoundBcs C foldRoot ch hm hch δs hδpos hδone S dom d
        q errstar hdC hMCA hBstar hdC2 hstar) st
      (List.ofFn fun k => (πs k, γv k)) w' 0 = fun k => ms k := by
  rw [wAt_bcs]
  have hmapped : bcsRounds dom d q (List.ofFn fun k => (πs k, γv k))
      = List.ofFn fun k => (ms k, γv k) := by
    rw [bcsRounds_ofFn]
    exact congrArg List.ofFn (funext fun k => by
      rw [bcsWord_committed S dom hdt hq (hmem k) (hroot k) (hopen k)])
  rw [hmapped]
  exact accRbr_backward_masked C foldRoot ch hm hch δs hδpos hδone errstar
    hdC hMCA hBstar hdC2 hstar ⟨(), st.x, st.y⟩ ms γv halign w'

/-! ## `accFsSound_bcs` — Fiat–Shamir at the deployed alphabet -/

/-- **FS of the DEPLOYED transcript shape**: the Fiat–Shamir compilation of
the BCS-alphabet instance — the proof string carries roots + opened columns +
opening proofs, and the oracle hashes THOSE, exactly what the deployed
protocol hashes — is straightline knowledge-sound at the
`(t + k)·accRbrError` grinding factor. `accFsSound` (riding
`fsKeystone_proved`'s unconditional `FsOfRbrSound`, CITED) on the BCS pair
with `hbound := le_refl`. Covered scope in one sentence: at the root/column
message alphabet, given the mutual-CA floor, FS of the accumulator chain is
straightline knowledge-sound with the pessimistic proved numbers
`(t + ch.length)·(err⋆(δ) + 1/|F|)` — proven parameters only. -/
theorem accFsSound_bcs (C : Submodule F (Fin m → F))
    (foldRoot : Root → F → Root → Root) (ch : Chain Root F (Fin m) r)
    (hm : 0 < m) (hch : 0 < ch.length) (δs : ℝ) (hδpos : 0 < δs)
    (hδone : δs ≤ 1) (S : BindingCommitment Root' F (Fin m) Op)
    (dom : Fin m ↪ F) (d : ℕ) (q : Fin t → Fin m) {dC Bstar : ℝ}
    (errstar : ℝ → ℝ)
    (hdC : ∀ u ∈ C, ∀ v ∈ C, u ≠ v → dC ≤ relDist u v)
    (hMCA : HasMutualCorrelatedAgreement (affineGenerator F) C Bstar errstar)
    (hBstar : δs ≤ 1 - Bstar) (hdC2 : δs ≤ dC / 2)
    (hstar : ∀ δ ∈ Set.Ioo (0 : ℝ) δs, 0 ≤ errstar δ)
    (Z : Set (Stmt (accReductionBcs C foldRoot ch hm hch δs hδpos hδone S dom
      d q))) :
    FsStraightlineKnowledgeSoundness
      (accReductionBcs C foldRoot ch hm hch δs hδpos hδone S dom d q) Z
      (fun _s b δ => ((b : ℝ) + (ch.length : ℝ))
        * accRbrError F errstar δ) :=
  accFsSound (accReductionBcs C foldRoot ch hm hch δs hδpos hδone S dom d q)
    (accRbrKnowledgeSoundBcs C foldRoot ch hm hch δs hδpos hδone S dom d q
      errstar hdC hMCA hBstar hdC2 hstar)
    Z F errstar hstar (fun _i _st _hst _δ _hδ => le_refl _)

end AccBcsInstance

/-! ## Keystones (ATLAS law 2: satisfiable + teeth + premise inhabitation)

The BCS instance BUILT and FIRED on the landed F₅ chain: `goodChain` at
`C = ⊤` (mutual-CA landed exactly: `hasMutualCorrelatedAgreement_top_affine`
with `err⋆ ≡ 0`, `minDistLB_inhabited` with `dC = 1/4`), `δ⋆ = 1/16` — the
SAME window as `accRbr_F5` — with commitment `CommitExample.S₅` (the ideal
binding scheme, binding PROVED) and columns opened at `qPair`, `t = d = 2`:
the landed coexistence point where the columns determine the masked word AND
hide the witness (`seam_hiding_coexist_at_d`). -/

namespace AccRbrBcsExample

open RSExample AccExample LCExample ZkHidingExample AccExtractChainExample
  ZkExtractionExample AccSoundRbrExample AccRbrInstanceExample CommitExample

/-- **The BCS reduction, BUILT** on the landed F₅ chain: `k = 2` rounds,
`Chal = ZMod 5`, messages = roots over `S₅` + 2 columns at `qPair` + trivial
opening proofs. -/
@[reducible] noncomputable def accReductionBcs_F5 : Reduction :=
  accReductionBcs (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
    (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
    S₅ dom₅ 2 qPair

/-- **The BCS Def-4.2 instance, BUILT — satisfiable + premise inhabitation**:
every hypothesis discharged by a landed witness, the SAME floor package as
`accRbr_F5`. -/
noncomputable def accRbrBcs_F5 : RbrKnowledgeSoundness accReductionBcs_F5 :=
  accRbrKnowledgeSoundBcs (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot
    goodChain (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
    S₅ dom₅ 2 qPair (fun _ => 0) (minDistLB_inhabited _)
    hasMutualCorrelatedAgreement_top_affine
    (by
      rw [Fintype.card_fin, max_eq_left (by norm_num)]
      norm_num)
    (by
      rw [Fintype.card_fin]
      norm_num)
    (fun _ _ => le_refl 0)

/-- The genesis statement of the BCS game — the landed genesis pair. -/
noncomputable def stBcs_F5 : Stmt accReductionBcs_F5 := ⟨(), genesis, xWord⟩

/-- The honest committed round message: the round's MASKED word (the landed
`msEx`) recommitted under `S₅`, its two columns opened at `qPair`, honest
opening proofs. -/
def msgBcs (k : Fin 2) : BcsMsg (Fin 4 → ZMod 5) (ZMod 5) Unit 2 :=
  ⟨S₅.commit (msEx k), fun j => msEx k (qPair j),
    fun j => S₅.openAt (msEx k) (qPair j)⟩

/-- The honest messages open — completeness of the commitment layer, fired. -/
theorem msgBcs_opens (k : Fin 2) : ColsOpen S₅ qPair (msgBcs k) :=
  fun j => S₅.verifyOpen_commit (msEx k) (qPair j)

/-- The honest messages synthesize the masked words exactly —
`recoverFromColumns_sound` at `t = d = 2` on the landed codewords
(`msEx_mem`, CITED). -/
theorem msgBcs_word (k : Fin 2) :
    bcsWord dom₅ 2 qPair (msgBcs k) = msEx k :=
  recoverFromColumns_sound dom₅ le_rfl qPair_inj (msEx_mem k) fun _ => rfl

/-- **The knowledge state fires TRUE on the FULL honest committed
transcript** — the state is inhabited at the deployed alphabet with real
opening checks: every column verifies (`verifyOpen_commit`), the synthesized
fold is the masked chain word, and it satisfies the aggregate (via
`masked_completeness_F5`, CITED, weakened to `⊤`). -/
theorem bcs_state_alive :
    accRbrBcs_F5.kstate.state (1 / 32) stBcs_F5
      (Transcript.ofFull msgBcs fun k => γbase (k : ℕ))
      (fun k => msEx k) = true := by
  classical
  refine (accRbrBcs_F5.kstate.full_iff (1 / 32)
    (by
      rw [Set.mem_Ioo]
      exact ⟨by norm_num, by show (1 : ℝ) / 32 < 1 / 16; norm_num⟩)
    stBcs_F5 msgBcs (fun k => γbase (k : ℕ)) (fun k => msEx k)).mpr ?_
  refine ⟨aggregate linRoot (padSched fun k : Fin 2 => γbase (k : ℕ)) genesis
      goodChain,
    foldWords (padSched fun k : Fin 2 => γbase (k : ℕ)) xWord
      (List.ofFn fun i => bcsWord dom₅ 2 qPair (msgBcs i)), ?_, ?_⟩
  · show (if ∀ i, ColsOpen S₅ qPair (msgBcs i) then _ else none) = _
    rw [if_pos fun i => msgBcs_opens i]
    rfl
  · refine ⟨foldWords (padSched fun k : Fin 2 => γbase (k : ℕ)) xWord
      (List.ofFn fun i => bcsWord dom₅ 2 qPair (msgBcs i)), ?_, ?_⟩
    · have hfn : (List.ofFn fun i => bcsWord dom₅ 2 qPair (msgBcs i))
          = List.ofFn msEx :=
        congrArg List.ofFn (funext fun i => msgBcs_word i)
      rw [hfn, foldWords_ofFn]
      exact ⟨Submodule.mem_top,
        (masked_completeness_F5 (padSched fun k : Fin 2 => γbase (k : ℕ))).2⟩
    · show fracHamming _ _ ≤ (1 : ℝ) / 32
      rw [fracHamming_self]
      norm_num

/-- **The err field computes**: the BCS instance's per-round price is `1/5` —
`accRbrError_zero_five` (CITED) through the instance, exactly as at the IOR
resolution. The deployed alphabet costs no slack. -/
theorem bcs_err_computes (i : Fin accReductionBcs_F5.k)
    (st : Stmt accReductionBcs_F5) (δ : ℝ) :
    accRbrBcs_F5.err i st δ = 1 / 5 :=
  accRbrError_zero_five δ

/-- **The backward extraction, fired at the deployed alphabet**: Construction
B.5 on the honest COMMITTED transcript of `goodChain` — roots, columns, and
proofs only; no word is ever sent — returns EXACTLY the masked word family,
for every seed. `accRbrBcs_backward_committed` with every hypothesis
discharged by landed objects. -/
theorem bcs_extract_masked (w' : Fin 2 → Fin 4 → ZMod 5) :
    wAt accRbrBcs_F5 stBcs_F5
      (List.ofFn fun k => (msgBcs k, γbase (k : ℕ))) w' 0
      = fun k => msEx k :=
  accRbrBcs_backward_committed (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5))
    linRoot goodChain (by norm_num) (by decide) (1 / 16) (by norm_num)
    (by norm_num) S₅ dom₅ qPair (fun _ => 0) (minDistLB_inhabited _)
    hasMutualCorrelatedAgreement_top_affine
    (by
      rw [Fintype.card_fin, max_eq_left (by norm_num)]
      norm_num)
    (by
      rw [Fintype.card_fin]
      norm_num)
    (fun _ _ => le_refl 0) le_rfl qPair_inj stBcs_F5 msEx
    (fun k => γbase (k : ℕ)) msgBcs (fun _ => rfl) msgBcs_opens msEx_mem
    msEx_linkAligned w'

/-- **The BCS extractor IS the seam** — the citation made real on the landed
instance: the native backward composition at the root alphabet produces the
SAME list as `extractChain` fed `seamCounterfactual`'s synthesized
counterfactuals through `S₅`'s binding (`seam_extraction_committed_F5`,
CITED — itself `extractChain_committed_seam` fired end to end). One
straightline execution's committed columns serve the whole extraction, and
this file's extract field computes exactly that object. -/
theorem bcs_extract_is_seam (w' : Fin 2 → Fin 4 → ZMod 5) :
    List.ofFn (wAt accRbrBcs_F5 stBcs_F5
        (List.ofFn fun k => (msgBcs k, γbase (k : ℕ))) w' 0)
      = extractChain γbase γalt₂ (flatFold γbase xWord msEx)
          (seamCounterfactual (n := 2) dom₅ 2 qPair γbase γalt₂
            (flatFold γbase xWord msEx)
            (fun c j => partialFold γbase xWord msEx c (qPair j))) := by
  rw [bcs_extract_masked]
  exact seam_extraction_committed_F5.symm

/-- **FS at the DEPLOYED alphabet, FIRED**: straightline FS knowledge
soundness for the accumulator chain whose proof strings carry roots + opened
columns + opening proofs — the objects the deployed protocol hashes — at
`(t + 2)·(1/5)` (`bcs_err_computes`). The sentence `[ACC-rbr-bcs]` owed. -/
theorem bcs_fs_fired :
    FsStraightlineKnowledgeSoundness accReductionBcs_F5 Set.univ
      (fun _s b δ => ((b : ℝ) + (accReductionBcs_F5.k : ℝ))
        * accRbrError (ZMod 5) (fun _ => 0) δ) :=
  accFsSound_bcs (⊤ : Submodule (ZMod 5) (Fin 4 → ZMod 5)) linRoot goodChain
    (by norm_num) (by decide) (1 / 16) (by norm_num) (by norm_num)
    S₅ dom₅ 2 qPair (fun _ => 0) (minDistLB_inhabited _)
    hasMutualCorrelatedAgreement_top_affine
    (by
      rw [Fintype.card_fin, max_eq_left (by norm_num)]
      norm_num)
    (by
      rw [Fintype.card_fin]
      norm_num)
    (fun _ _ => le_refl 0) Set.univ

/-- **Teeth, generic, fired**: ANY message reusing round 0's recommitted root
whose openings verify synthesizes the SAME word — the root pins the word
through binding (`bcs_root_pins_word` on built objects). -/
theorem bcs_root_pins_F5 (π' : BcsMsg (Fin 4 → ZMod 5) (ZMod 5) Unit 2)
    (hroot : π'.root = (msgBcs 0).root) (hopen : ColsOpen S₅ qPair π') :
    bcsWord dom₅ 2 qPair π' = bcsWord dom₅ 2 qPair (msgBcs 0) :=
  (bcs_root_pins_word S₅ dom₅ 2 hroot hopen (msgBcs_opens 0)).2

/-- **Teeth, computed**: the OTHER word's columns cannot be opened from round
1's recommitted root — the concrete equivocation attempt (attributing
`oneWord`'s columns to the root that commits `msEx 1 = oneWord + mask`) is
refuted by kernel computation. Binding is load-bearing at the deployed
alphabet, not decoration. -/
theorem bcs_teeth_columns :
    ¬ ∀ j : Fin 2, S₅.verifyOpen (msgBcs 1).root (qPair j)
        (oneWord (qPair j)) () := by
  show ¬ ∀ j : Fin 2, msEx 1 (qPair j) = oneWord (qPair j)
  decide

/-! ### Without binding: the retained attempt, exhibited

`bcs_teeth_columns` above shows binding refuting an equivocation at `S₅`. The
witnesses below are the other half of the same fact, and the half a collision
reduction actually needs: at a scheme with NO binding field the attempt is not
refuted, it is a built object, and the synthesized word is WRONG. -/

/-- A message submitted to the equivocator carrying `oneWord`'s columns —
against a root that commits `xWord`. Nothing here is hypothetical: every
field is constructed. -/
def equivocalMsg : BcsMsg Unit (ZMod 5) Unit 2 where
  root := ()
  cols := fun j => oneWord (qPair j)
  ops := fun _ => ()

/-- Its root IS the equivocator's commitment of `xWord` — the exact premise
shape `bcsWord_committed` consumes. -/
theorem equivocalMsg_root :
    equivocalMsg.root = CommitExample.equivocal.commit xWord := rfl

/-- Its openings all verify — the exact second premise. -/
theorem equivocalMsg_opens :
    ColsOpen CommitExample.equivocal qPair equivocalMsg := fun _ => trivial

/-- **Satisfiable**: the retained equivocation is inhabited. Both premises of
`bcsWord_committed` hold and the conclusion still fails, so the second branch
of `bcsWord_or_columnEquivocation` is a real disjunct rather than dead code. -/
theorem equivocalMsg_columnEquivocation :
    ColumnEquivocation CommitExample.equivocal qPair equivocalMsg xWord :=
  ⟨0, trivial, trivial, by decide⟩

/-- **Computed**: the word this root synthesizes is `oneWord`, by erasure
recovery from the submitted columns alone — `bcsWord_of_colsExact` with no
scheme in sight. -/
theorem equivocalMsg_word :
    bcsWord dom₅ 2 qPair equivocalMsg = oneWord :=
  bcsWord_of_colsExact dom₅ le_rfl qPair_inj oneWord_mem fun _ => rfl

/-- **Teeth**: and it is NOT the committed word. A root committing `xWord`
synthesizes `oneWord` at the equivocator, so `bcsWord_committed`'s conclusion
is false here and its binding premise is doing real work. -/
theorem equivocalMsg_word_ne_committed :
    bcsWord dom₅ 2 qPair equivocalMsg ≠ xWord := by
  rw [equivocalMsg_word]
  decide

/-- The same fact stated against the theorem it constrains: no
`BindingCommitment` extends the equivocator, so `bcsWord_committed` is
genuinely inapplicable to `equivocalMsg` — this is a refutation, not a gap in
the library. -/
theorem equivocalMsg_no_binding_route :
    ¬ ∃ S : BindingCommitment Unit (ZMod 5) (Fin 4) Unit,
        S.toOpeningScheme = CommitExample.equivocal :=
  CommitExample.equivocal_no_binding_extension

end AccRbrBcsExample

/-! ## Residual obligation — prose, not a stub

**What CLOSED here.** `[ACC-rbr-bcs]` named the BCS-resolution instance: a
`Reduction` whose `PMsg` is the deployed message alphabet (recommitted root +
opened columns + opening proofs), a `KStateFn` demanding committed-column
consistency, and an extract field synthesizing the round words from one
execution's columns through binding. ALL THREE are BUILT and PROVED here at
that alphabet — `accReductionBcs` (opening-checking verifier),
`accKStateBcs` (all three Def-4.1 clauses), `accRbrKnowledgeSoundBcs`
(`extract_sound` at the landed `accRbrError` price, `accSound_rbr` cited
never re-derived), `accFsSound_bcs` (FS of the deployed transcript shape at
`(t + k)·accRbrError`), with the backward composition returning the committed
(masked) words exactly (`accRbrBcs_backward_committed`, riding
`accRbr_backward_masked`) and IDENTIFIED with the seam object on the landed
instance (`bcs_extract_is_seam` = `extractChain ∘ seamCounterfactual` through
`S₅` binding, citing `seam_extraction_committed_F5`).

**`[ACC-rbr-bcs-resid]`** — what remains, stated precisely.

* **(a) The fold-root schedule.** This file's round message commits the
  round's OWN (masked) word — deployment-faithful for the WHOLE-CODE-MASK /
  unique-decoding regime (`t ≥ d`), where opening the recommitted round word
  is exactly the landed coexistence point (`seam_hiding_coexist_at_d`: the
  columns determine the masked word and hide the witness). The
  CONSTRAINED-mask deployment instead opens columns of the recommitted
  PARTIAL FOLDS, and those roots LAG their challenge: `h_{i+1} = h_i +
  ρ_i·w_i` can only be committed after `ρ_i`, i.e. inside round `i+1`'s
  message — while Defs 4.1/4.2 score challenge `ρ_i` at round `i`'s
  extension, where that root has not yet been sent. Re-attributing the
  knowledge state to the lagged fold roots therefore needs either (i) the
  BCS/ROM commitment extraction (read the committed word out of the oracle
  QUERY LOG at root time — outside `Reduction`'s oracle-free shape; the
  transcript-layer route), or (ii) a round bound for the event "the folded
  CLAIM is δ-satisfiable near an adversary-chosen point committed AFTER the
  challenge" — a claim-fold-satisfiability bound that is genuinely NOT the
  landed fixed-pair `accSound_rbr` event. The column DATA is equivalent
  either way (successive fold columns and increment columns interconvert by
  the seam's `γ⁻¹`-difference map — the same formula inside
  `seamCounterfactual`, and `bcs_extract_is_seam` exhibits this file's
  extractor equal to the seam's output); the ROOT attribution is the open
  packaging.
* **(b) Sub-unique-decoding.** For constrained masks (the homogeneous masks
  that make masked words witnesses) the seam must recover increments from
  `t ≤ d − r` columns — `[ZK-RBR-extract]` open lemma A, inherited unchanged.
* **(c) The floor.** `[FS-ROM]` (the sponge realizing the handler),
  `[COMMIT-CR]` (the Merkle/sponge scheme realizing `BindingCommitment`), and
  the standing `hPG` mutual-CA package at RS with macroscopic δ — inherited,
  consumed as hypotheses, never claimed.

**Where the ZK argument now stands, honestly.** `selvage_zk_argument`'s RBR/FS
carrier exists at the root/column message alphabet with a committed-column
knowledge state and a binding-composed extractor — the deployed shape for the
whole-code-mask/UD regime, with proven parameters `(t + k)·(err⋆(δ) + 1/|F|)`
under the mutual-CA floor. It is NOT yet "deployed resolution, full stop":
the constrained-mask fold-root schedule (a) and lemma A (b) still gap, and
everything rides the floor (c). Nothing sharper is claimed.

## Ledger

* `BcsMsg` / `ColsOpen` / `ColsConsistent` (+ `colsConsistent_ofFn`) —
  DEFINED/PROVED: the deployed message alphabet and its opening checks.
* `bcsWord` / `bcsWord_committed` — DEFINED/PROVED: per-message word
  synthesis by erasure decoding; binding pins it (`binding_columns` +
  `recoverFromColumns_sound`, CITED).
* `bcs_root_pins_word` — PROVED (teeth): one root, one column vector, one
  synthesized word.
* `bcsRounds` (+ `_length`, `_nil`, `_append`, `_ofFn`, `_take`) —
  DEFINED/PROVED: message transcripts read as word transcripts.
* `accReductionBcs` — DEFINED: the chain as a WARP `Reduction` at
  `PMsg = BcsMsg`, verifier checking every opening.
* `AccStatePropBcs` / `accKStateBcs` (+ `_state_eq`) — DEFINED, all three
  Def-4.1 clauses PROVED: committed-column consistency ∧ the IOR state on the
  synthesized transcript.
* `accExtractBcs` (+ `_append`) — DEFINED/PROVED: synthesize the round word,
  decode at the canonical radius.
* `accRbrKnowledgeSoundBcs` — BUILT, `extract_sound` PROVED via
  `accSound_rbr` (CITED): Def 4.2 at the deployed alphabet,
  `err = accRbrError`, no slack.
* `wAt_bcs` / `accRbrBcs_backward_committed` — PROVED: Construction B.5 at
  the BCS alphabet = the IOR composition on the synthesized transcript;
  committed chains extract exactly (`accRbr_backward_masked` CITED).
* `accFsSound_bcs` — PROVED: FS of the deployed transcript shape,
  straightline, `(t + k)·accRbrError`.
* Keystones — `accReductionBcs_F5` / `accRbrBcs_F5` (built, landed
  witnesses); `msgBcs` + `msgBcs_opens` + `msgBcs_word`; `bcs_state_alive`
  (the state fires on the FULL honest committed transcript);
  `bcs_err_computes` (`1/5`); `bcs_extract_masked` (the masked words, any
  seed); `bcs_extract_is_seam` (= `extractChain ∘ seamCounterfactual`
  through binding, `seam_extraction_committed_F5` CITED); `bcs_fs_fired`
  (FS at the deployed alphabet); `bcs_root_pins_F5` + `bcs_teeth_columns`
  (teeth, generic + computed).
* Residual — `[ACC-rbr-bcs-resid]` (prose above): (a) the constrained-mask
  fold-root schedule (lagged recommitment attribution), (b) lemma A, (c) the
  floor — each inherited or named, none silently absorbed.

`#print axioms` on `accRbrKnowledgeSoundBcs`, `accFsSound_bcs`,
`accRbrBcs_backward_committed`, `AccRbrBcsExample.accRbrBcs_F5`,
`AccRbrBcsExample.bcs_state_alive`, `AccRbrBcsExample.bcs_extract_is_seam`,
`AccRbrBcsExample.bcs_fs_fired`: `propext`, `Classical.choice`, `Quot.sound`
— no `sorryAx` anywhere in the file. -/

end Minidregg.Selvage
