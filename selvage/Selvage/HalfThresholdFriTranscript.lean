/-
# Selvage.HalfThresholdFriTranscript -- committed FRI words and opened queries

`Selvage.HalfThresholdFriTower` proves challenge soundness for the DERIVED fold
tower.  A deployed prover instead commits to an adversarial word at every
level and opens only queried symbols.  This file introduces that missing
statement/event vocabulary and closes everything available at exact-opening
resolution.

The public statement is genuinely statement-first: `FriCommittedStatement`
contains every level word, its root, and the equation saying that root commits
to that word.  The object is fixed before a challenge vector is supplied to
the acceptance event.  `OpenedFriQuery` checks three authenticated symbols
for one multiplicative FRI fibre -- the two source values and the next-level
value -- plus the exact fold equation.  Position binding then pins the opened
equation to the statement's committed words (`openedFriQuery_pins`).

At ALL-position resolution, consistent openings force every committed level
to equal the derived folding tower.  Therefore the committed acceptance event
is contained in `acceptSet`, and the half-threshold tower bound transfers
without loss (`committedFri_sound_halfThen_UD`).

This file deliberately does NOT turn `q` sampled positions into all-position
consistency.  That implication is precisely the query-miss event, with kernel
`column_sampling_bridge_pr` and price `(1-delta/2)^q`, plus deployed Merkle
collision resistance.  It also records only the exact Fiat--Shamir syntax
bridge supplied by `fsOracle_query`; encoding this FRI event as an RBR
`Reduction` and invoking the ROM game remains a named protocol floor.
-/
import Selvage.HalfThresholdFriTower
import Selvage.Commitment
import Selvage.FiatShamir

namespace Minidregg.Selvage

/-! ## Statement-first committed level words -/

structure FriCommittedStatement
    {F : Type*} {ι : ℕ → Type*} {Root Op : ℕ → Type*}
    (S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n)) where
  /-- The word attributed to every level root, fixed before challenges. -/
  word : ∀ n, ι n → F
  /-- The public level roots. -/
  root : ∀ n, Root n
  /-- Each root commits to its statement-fixed word. -/
  root_eq_commit : ∀ n, root n = (S n).commit (word n)

/-! ## One exact opened FRI query -/

/-- The values and authentication paths opened for one FRI fibre. -/
structure FriQueryOpening (F OpBig OpSmall : Type*) where
  left : F
  right : F
  next : F
  leftPath : OpBig
  rightPath : OpBig
  nextPath : OpSmall

section OpenedQuery

variable {F : Type*} [Field F]
variable {ι κ RootBig RootSmall OpBig OpSmall : Type*}
variable {dom : ι ↪ F} {domSq : κ ↪ F}

/-- Exact verifier predicate for one opened multiplicative-FRI fibre.

The verifier authenticates `f(sec k)`, `f(neg (sec k))`, and the alleged
next word at `k`, then checks the literal FRI fold equation. -/
def OpenedFriQuery
    (Sbig : OpeningScheme RootBig F ι OpBig)
    (Ssmall : OpeningScheme RootSmall F κ OpSmall)
    (D : FoldingData F dom domSq) (rt : RootBig) (rt' : RootSmall)
    (alpha : F) (k : κ) (o : FriQueryOpening F OpBig OpSmall) : Prop :=
  Sbig.verifyOpen rt (D.sec k) o.left o.leftPath ∧
  Sbig.verifyOpen rt (D.neg (D.sec k)) o.right o.rightPath ∧
  Ssmall.verifyOpen rt' k o.next o.nextPath ∧
  o.next = (o.left + o.right) / 2
    + alpha * ((o.left - o.right) / (2 * dom (D.sec k)))

/-- Honest committed words always have a valid exact fibre opening. -/
theorem openedFriQuery_honest
    (Sbig : OpeningScheme RootBig F ι OpBig)
    (Ssmall : OpeningScheme RootSmall F κ OpSmall)
    (D : FoldingData F dom domSq) (w : ι → F) (alpha : F) (k : κ) :
    ∃ o : FriQueryOpening F OpBig OpSmall,
      OpenedFriQuery Sbig Ssmall D (Sbig.commit w)
        (Ssmall.commit (fold D w alpha)) alpha k o := by
  refine ⟨{
    left := w (D.sec k)
    right := w (D.neg (D.sec k))
    next := fold D w alpha k
    leftPath := Sbig.openAt w (D.sec k)
    rightPath := Sbig.openAt w (D.neg (D.sec k))
    nextPath := Ssmall.openAt (fold D w alpha) k }, ?_⟩
  refine ⟨Sbig.verifyOpen_commit _ _, Sbig.verifyOpen_commit _ _,
    Ssmall.verifyOpen_commit _ _, ?_⟩
  rfl

/-- A raw accepted FRI fibre that is not attached to the two committed words
retains an explicit equivocation at one of its three authenticated symbols.
The submitted value and path are not rewritten away by an ideal binding
assumption. -/
def FriQueryEquivocation
    (Sbig : OpeningScheme RootBig F ι OpBig)
    (Ssmall : OpeningScheme RootSmall F κ OpSmall)
    (D : FoldingData F dom domSq) (rt : RootBig) (rt' : RootSmall)
    (w : ι → F) (w' : κ → F) (k : κ)
    (o : FriQueryOpening F OpBig OpSmall) : Prop :=
  Sbig.PositionEquivocation rt (D.sec k) o.left o.leftPath w ∨
  Sbig.PositionEquivocation rt (D.neg (D.sec k)) o.right o.rightPath w ∨
  Ssmall.PositionEquivocation rt' k o.next o.nextPath w'

/-- **Raw verifier split.**  Against roots produced from fixed words, every
accepted opened fibre either pins the literal fold equation to those words or
exhibits a retained position equivocation.  No binding property is assumed.
This is the exact branch point at which a deployed Merkle implementation pays
its collision-resistance term. -/
theorem openedFriQuery_pins_or_equivocation
    (Sbig : OpeningScheme RootBig F ι OpBig)
    (Ssmall : OpeningScheme RootSmall F κ OpSmall)
    (D : FoldingData F dom domSq)
    {w : ι → F} {w' : κ → F} {rt : RootBig} {rt' : RootSmall}
    (hrt : rt = Sbig.commit w) (hrt' : rt' = Ssmall.commit w')
    {alpha : F} {k : κ} {o : FriQueryOpening F OpBig OpSmall}
    (hopen : OpenedFriQuery Sbig Ssmall D rt rt' alpha k o) :
    w' k = fold D w alpha k ∨
      FriQueryEquivocation Sbig Ssmall D rt rt' w w' k o := by
  rcases hopen with ⟨hleft, hright, hnext, heq⟩
  by_cases hl : o.left = w (D.sec k)
  · by_cases hr : o.right = w (D.neg (D.sec k))
    · by_cases hn : o.next = w' k
      · left
        rw [← hn, heq, hl, hr]
        rfl
      · right
        exact Or.inr (Or.inr ⟨hnext,
          Ssmall.verifyOpen_of_commit_eq hrt' k, hn⟩)
    · right
      exact Or.inr (Or.inl ⟨hright,
        Sbig.verifyOpen_of_commit_eq hrt (D.neg (D.sec k)), hr⟩)
  · right
    exact Or.inl ⟨hleft, Sbig.verifyOpen_of_commit_eq hrt (D.sec k), hl⟩

/-- A pair of perfectly position-binding schemes makes the equivocation
branch of the raw split impossible. -/
theorem not_friQueryEquivocation
    (Sbig : BindingCommitment RootBig F ι OpBig)
    (Ssmall : BindingCommitment RootSmall F κ OpSmall)
    (D : FoldingData F dom domSq) (rt : RootBig) (rt' : RootSmall)
    (w : ι → F) (w' : κ → F) (k : κ)
    (o : FriQueryOpening F OpBig OpSmall) :
    ¬ FriQueryEquivocation Sbig Ssmall D rt rt' w w' k o := by
  rintro (hleft | hright | hnext)
  · exact Sbig.not_positionEquivocation rt (D.sec k)
      o.left o.leftPath w hleft
  · exact Sbig.not_positionEquivocation rt (D.neg (D.sec k))
      o.right o.rightPath w hright
  · exact Ssmall.not_positionEquivocation rt' k
      o.next o.nextPath w' hnext

/-- **Binding reattaches the opened equation to the committed pair.**  A
valid opened fibre forces the statement-committed next word to equal the
actual fold of the statement-committed source word at that coordinate. -/
theorem openedFriQuery_pins
    (Sbig : BindingCommitment RootBig F ι OpBig)
    (Ssmall : BindingCommitment RootSmall F κ OpSmall)
    (D : FoldingData F dom domSq)
    {w : ι → F} {w' : κ → F} {rt : RootBig} {rt' : RootSmall}
    (hrt : rt = Sbig.commit w) (hrt' : rt' = Ssmall.commit w')
    {alpha : F} {k : κ} {o : FriQueryOpening F OpBig OpSmall}
    (hopen : OpenedFriQuery Sbig Ssmall D rt rt' alpha k o) :
    w' k = fold D w alpha k := by
  rcases hopen with ⟨hleft, hright, hnext, heq⟩
  have hleftHonest :=
    Sbig.toOpeningScheme.verifyOpen_of_commit_eq hrt (D.sec k)
  have hrightHonest :=
    Sbig.toOpeningScheme.verifyOpen_of_commit_eq hrt (D.neg (D.sec k))
  have hnextHonest :=
    Ssmall.toOpeningScheme.verifyOpen_of_commit_eq hrt' k
  have hl : o.left = w (D.sec k) :=
    Sbig.binding rt (D.sec k) o.left (w (D.sec k))
      o.leftPath (Sbig.openAt w (D.sec k)) hleft hleftHonest
  have hr : o.right = w (D.neg (D.sec k)) :=
    Sbig.binding rt (D.neg (D.sec k)) o.right (w (D.neg (D.sec k)))
      o.rightPath (Sbig.openAt w (D.neg (D.sec k))) hright hrightHonest
  have hn : o.next = w' k :=
    Ssmall.binding rt' k o.next (w' k)
      o.nextPath (Ssmall.openAt w' k) hnext hnextHonest
  rw [← hn, heq, hl, hr]
  rfl

end OpenedQuery

/-! ## Fixed-round query-miss theorem -/

section RoundQueryMiss

variable {F : Type*} [Field F] [DecidableEq F]
variable {ι κ RootBig RootSmall OpBig OpSmall : Type*}
variable [Fintype κ] [Nonempty κ]
variable {dom : ι ↪ F} {domSq : κ ↪ F}

/-- A selected-query schedule is accepted when there EXISTS opening data
authenticating every queried fibre and satisfying every exact fold equation.
The opening data remains adversarial/existential; binding removes it in the
soundness theorem below. -/
def FriRoundQueriesAccept
    (Sbig : BindingCommitment RootBig F ι OpBig)
    (Ssmall : BindingCommitment RootSmall F κ OpSmall)
    (D : FoldingData F dom domSq) (rt : RootBig) (rt' : RootSmall)
    (alpha : F) {qCount : ℕ} (q : Fin qCount → κ) : Prop :=
  ∃ opening : ∀ _a : Fin qCount, FriQueryOpening F OpBig OpSmall,
    ∀ a, OpenedFriQuery Sbig Ssmall D rt rt' alpha (q a) (opening a)

/-- Finite set of accepted query schedules for one fixed committed round. -/
noncomputable def friRoundQueryAcceptSet
    (Sbig : BindingCommitment RootBig F ι OpBig)
    (Ssmall : BindingCommitment RootSmall F κ OpSmall)
    (D : FoldingData F dom domSq) (rt : RootBig) (rt' : RootSmall)
    (alpha : F) (qCount : ℕ) : Finset (Fin qCount → κ) :=
  @Finset.filter (Fin qCount → κ)
    (FriRoundQueriesAccept Sbig Ssmall D rt rt' alpha)
    (Classical.decPred _) Finset.univ

/-- **Fixed-round query-miss count, with adversarial opening data.**  If the
committed next word is `tau`-far from the honest fold of the committed source
word, then accepted `qCount`-query schedules have mass at most
`(1-tau)^qCount`.

Proof: position binding pins every existentially supplied opened equation to
the two committed words; hence every queried coordinate lies in their true
agreement set.  `column_sampling_bridge` then performs the exact counting. -/
theorem friRound_query_miss_count
    (Sbig : BindingCommitment RootBig F ι OpBig)
    (Ssmall : BindingCommitment RootSmall F κ OpSmall)
    (D : FoldingData F dom domSq)
    {w : ι → F} {w' : κ → F} {rt : RootBig} {rt' : RootSmall}
    (hrt : rt = Sbig.commit w) (hrt' : rt' = Ssmall.commit w')
    (alpha : F) (qCount : ℕ) {tau : ℝ}
    (hfar : tau ≤ relDist w' (fold D w alpha)) :
    ((friRoundQueryAcceptSet Sbig Ssmall D rt rt' alpha qCount).card : ℝ)
      ≤ (1 - tau) ^ qCount * (Fintype.card κ : ℝ) ^ qCount := by
  classical
  set agree : Finset (Fin qCount → κ) := Finset.univ.filter fun q =>
    ∀ a, w' (q a) = fold D w alpha (q a) with hagree
  have hsub : friRoundQueryAcceptSet Sbig Ssmall D rt rt' alpha qCount ⊆ agree := by
    intro q hq
    obtain ⟨opening, hopen⟩ := (Finset.mem_filter.mp hq).2
    rw [hagree, Finset.mem_filter]
    refine ⟨Finset.mem_univ q, fun a => ?_⟩
    exact openedFriQuery_pins Sbig Ssmall D hrt hrt' (hopen a)
  have hcard :
      ((friRoundQueryAcceptSet Sbig Ssmall D rt rt' alpha qCount).card : ℝ)
        ≤ (agree.card : ℝ) := by
    exact_mod_cast Finset.card_le_card hsub
  refine le_trans hcard ?_
  rw [hagree]
  exact column_sampling_bridge qCount hfar

/-- Probability rendering of `friRound_query_miss_count`. -/
theorem friRound_query_miss_pr
    (Sbig : BindingCommitment RootBig F ι OpBig)
    (Ssmall : BindingCommitment RootSmall F κ OpSmall)
    (D : FoldingData F dom domSq)
    {w : ι → F} {w' : κ → F} {rt : RootBig} {rt' : RootSmall}
    (hrt : rt = Sbig.commit w) (hrt' : rt' = Ssmall.commit w')
    (alpha : F) (qCount : ℕ) {tau : ℝ}
    (hfar : tau ≤ relDist w' (fold D w alpha)) :
    ((friRoundQueryAcceptSet Sbig Ssmall D rt rt' alpha qCount).card : ℝ)
        / (Fintype.card κ : ℝ) ^ qCount
      ≤ (1 - tau) ^ qCount := by
  have hden : (0 : ℝ) < (Fintype.card κ : ℝ) ^ qCount := by positivity
  rw [div_le_iff₀ hden]
  exact friRound_query_miss_count Sbig Ssmall D hrt hrt'
    alpha qCount hfar

/-- The half-threshold specialization: a `delta/2`-far committed deviation
survives `qCount` independent queries with probability at most
`(1-delta/2)^qCount`. -/
theorem friRound_query_miss_halfThreshold
    (Sbig : BindingCommitment RootBig F ι OpBig)
    (Ssmall : BindingCommitment RootSmall F κ OpSmall)
    (D : FoldingData F dom domSq)
    {w : ι → F} {w' : κ → F} {rt : RootBig} {rt' : RootSmall}
    (hrt : rt = Sbig.commit w) (hrt' : rt' = Ssmall.commit w')
    (alpha : F) (qCount : ℕ) {delta : ℝ}
    (hfar : delta / 2 ≤ relDist w' (fold D w alpha)) :
    ((friRoundQueryAcceptSet Sbig Ssmall D rt rt' alpha qCount).card : ℝ)
        / (Fintype.card κ : ℝ) ^ qCount
      ≤ (1 - delta / 2) ^ qCount :=
  friRound_query_miss_pr Sbig Ssmall D hrt hrt' alpha qCount hfar

end RoundQueryMiss

/-! ## Query batches and all-round acceptance -/

section CommittedTower

variable {F : Type*} [Field F]
variable {ι : ℕ → Type*} {Root Op : ℕ → Type*}
variable {m : ℕ}
variable (S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n))
variable (T : FoldingTower F ι m)

/-- Exact consistency on a selected batch of next-level coordinates. -/
def OpenedFriQueries {j : ℕ} (hj : j < m)
    (st : FriCommittedStatement S) (alpha : F)
    {qCount : ℕ} (q : Fin qCount → ι (j + 1))
    (opening : ∀ _a : Fin qCount, FriQueryOpening F (Op j) (Op (j + 1))) : Prop :=
  ∀ a, OpenedFriQuery (S j) (S (j + 1)) (T.data j hj)
    (st.root j) (st.root (j + 1)) alpha (q a) (opening a)

/-- Binding pins every selected query to the committed fold equation. -/
theorem openedFriQueries_pins {j : ℕ} (hj : j < m)
    (st : FriCommittedStatement S) (alpha : F)
    {qCount : ℕ} (q : Fin qCount → ι (j + 1))
    (opening : ∀ _a : Fin qCount, FriQueryOpening F (Op j) (Op (j + 1)))
    (hopen : OpenedFriQueries S T hj st alpha q opening) :
    ∀ a, st.word (j + 1) (q a) = fold (T.data j hj) (st.word j) alpha (q a) := by
  intro a
  exact openedFriQuery_pins (S j) (S (j + 1)) (T.data j hj)
    (st.root_eq_commit j) (st.root_eq_commit (j + 1)) (hopen a)

/-- All-position opened consistency for every round.  This is the exact
resolution at which binding deterministically identifies the committed tower
with the derived tower. -/
def FriAllRoundsOpened (st : FriCommittedStatement S) (alpha : ℕ → F) : Prop :=
  ∀ j (hj : j < m) (k : ι (j + 1)),
    ∃ o : FriQueryOpening F (Op j) (Op (j + 1)),
      OpenedFriQuery (S j) (S (j + 1)) (T.data j hj)
        (st.root j) (st.root (j + 1)) (alpha j) k o

/-- All-position consistency forces every committed word to be the derived
fold tower of the committed level-zero word. -/
theorem committedWord_eq_towerWord
    (st : FriCommittedStatement S) (alpha : ℕ → F)
    (hopen : FriAllRoundsOpened S T st alpha) :
    ∀ n (hn : n ≤ m),
      st.word n = T.word (st.word 0) alpha n hn := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ j ih =>
      intro hn
      rw [T.word_succ, ← ih (Nat.le_of_succ_le hn)]
      funext k
      obtain ⟨o, ho⟩ := hopen j hn k
      exact openedFriQuery_pins (S j) (S (j + 1)) (T.data j hn)
        (st.root_eq_commit j) (st.root_eq_commit (j + 1)) ho

/-- The adversarial committed-word acceptance event at whole-opening
resolution: every round is opened consistently and the final committed word
passes the base RS membership check. -/
def FriCommittedAccepts (deg : ℕ → ℕ) (st : FriCommittedStatement S)
    (r : Fin m → F) : Prop :=
  FriAllRoundsOpened S T st (chalExt r) ∧
    st.word m ∈ reedSolomonCode (T.dom m) (deg m)

/-- A committed transcript accepted at whole-opening resolution makes the
derived proximity test accept on the same challenge tuple. -/
theorem friCommittedAccepts_implies_proximityTest
    (deg : ℕ → ℕ) (st : FriCommittedStatement S) {r : Fin m → F}
    (hacc : FriCommittedAccepts S T deg st r) :
    proximityTest T deg (st.word 0) (chalExt r) := by
  unfold proximityTest
  rw [← committedWord_eq_towerWord S T st (chalExt r) hacc.1 m le_rfl]
  exact hacc.2

end CommittedTower

/-! ## Committed acceptance set and half-threshold soundness -/

section CommittedSoundness

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)]
variable {Root Op : ℕ → Type*} {m : ℕ}
variable (S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n))

/-- Finite set of challenge tuples accepted by fixed, statement-first
committed level words. -/
noncomputable def friCommittedAcceptSet
    (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    (st : FriCommittedStatement S) : Finset (Fin m → F) :=
  @Finset.filter (Fin m → F)
    (fun r => FriCommittedAccepts S T deg st r)
    (Classical.decPred _) Finset.univ

omit [DecidableEq F] [∀ n, Fintype (ι n)] [∀ n, DecidableEq (ι n)] in
/-- Committed acceptance is contained in derived-tower acceptance. -/
theorem friCommittedAcceptSet_subset
    (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    (st : FriCommittedStatement S) :
    friCommittedAcceptSet S T deg st ⊆ acceptSet T deg (st.word 0) := by
  classical
  intro r hr
  exact mem_acceptSet.mpr (friCommittedAccepts_implies_proximityTest S T deg st
    (Finset.mem_filter.mp hr).2)

/-- **Strongest closed committed-oracle theorem.**  At all-position opening
resolution, binding reduces adversarial intermediate commitments to the
derived tower, so the unconditional half-threshold/one-third-UD challenge
bound transfers unchanged. -/
theorem committedFri_sound_halfThen_UD
    (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    (st : FriCommittedStatement S) {delta : ℝ}
    (hm : 0 < m) (hdelta : 0 < delta)
    (hnonempty : ∀ n, n ≤ m → Nonempty (ι n))
    (hdeg : ∀ j, j < m → deg j = 2 * deg (j + 1))
    (hband : ∀ j, j < m → 0 < j →
      delta / 2 < 1 - (2 + (deg (j + 1) : ℝ) /
        (Fintype.card (ι (j + 1)) : ℝ)) / 3)
    (hfar : ¬ close delta (reedSolomonCode (T.dom 0) (deg 0)) (st.word 0)) :
    (friCommittedAcceptSet S T deg st).card ≤
      m * (Fintype.card (ι 0) * Fintype.card F ^ (m - 1)) := by
  exact le_trans (Finset.card_le_card (friCommittedAcceptSet_subset S T deg st))
    (proximity_sound_halfThen_UD T deg hm hdelta hnonempty hdeg hband hfar)

end CommittedSoundness

/-! ## Exact Fiat--Shamir syntax bridge, without a ROM overclaim -/

/-- Read the designated Fiat--Shamir transcript-prefix queries as a challenge
vector. -/
def friFsChallenges {red : Reduction} {s : ℕ} (o : SrOutput red s)
    (H : SrMove red s → red.Chal) : Fin red.k → red.Chal :=
  fun i => H (o.query i)

/-- The canonical `fsOracle` realizes exactly the supplied FRI challenge
vector at all designated prefix queries. -/
theorem friFsChallenges_fsOracle {red : Reduction} {s : ℕ}
    (o : SrOutput red s) (rho : Fin red.k → red.Chal) :
    friFsChallenges o (fsOracle o rho) = rho := by
  funext i
  exact fsOracle_query o rho i

/-- Consequently ANY transcript event on the challenge vector is transported
exactly through the canonical FS oracle.  This is syntax/evaluation only; it
does not assert ROM soundness for FRI. -/
theorem friEvent_fsOracle_iff {red : Reduction} {s : ℕ}
    (o : SrOutput red s) (rho : Fin red.k → red.Chal)
    (event : (Fin red.k → red.Chal) → Prop) :
    event (friFsChallenges o (fsOracle o rho)) ↔ event rho := by
  rw [friFsChallenges_fsOracle]

/-! ## F5 teeth: a fixed committed fold accepts only its matching challenge -/

namespace HalfThresholdFriTranscriptExample

open ProximityExample

abbrev idealRoot (n : ℕ) : Type := levels n → ZMod 5
abbrev idealOp (_n : ℕ) : Type := Unit

def idealSchemes (n : ℕ) :
    BindingCommitment (idealRoot n) (ZMod 5) (levels n) (idealOp n) :=
  idealCommitment (ZMod 5) (levels n)

/-- Fixed adversarial statement: level zero is the spike; level one is its
fold at challenge `3`.  The words and roots exist before the verifier chooses
the challenge. -/
def spikeStatementWord : ∀ n, levels n → ZMod 5
  | 0 => spikeWord
  | 1 => fold data0 spikeWord 3
  | _ + 2 => Fin.elim0

def spikeStatement : FriCommittedStatement idealSchemes where
  word := spikeStatementWord
  root := spikeStatementWord
  root_eq_commit := fun _ => rfl

/-- The statement's committed fold opens consistently at its matching
challenge `3`. -/
theorem spike_allOpened_at_three :
    FriAllRoundsOpened idealSchemes ldtTower spikeStatement (chalExt ![3]) := by
  intro j hj k
  have hj0 : j = 0 := by omega
  subst j
  change ∃ o, OpenedFriQuery (idealSchemes 0).toOpeningScheme
    (idealSchemes 1).toOpeningScheme data0
    ((idealSchemes 0).commit spikeWord)
    ((idealSchemes 1).commit (fold data0 spikeWord 3)) 3 k o
  exact openedFriQuery_honest (idealSchemes 0).toOpeningScheme
    (idealSchemes 1).toOpeningScheme
    data0 spikeWord 3 k

/-- The committed transcript ACCEPTS at challenge `3`. -/
theorem spike_committed_accepts_three :
    FriCommittedAccepts idealSchemes ldtTower degSched spikeStatement ![3] := by
  refine ⟨spike_allOpened_at_three, ?_⟩
  change fold data0 spikeWord 3 ∈ reedSolomonCode dom1 1
  have h := (spike_accept_iff (3 : ZMod 5)).mpr rfl
  change fold data0 spikeWord 3 ∈ reedSolomonCode dom1 1 at h
  exact h

/-- **Binding tooth.**  The SAME fixed roots cannot pass at challenge `1`:
otherwise exact opened consistency would make the derived spike tower accept,
contradicting the computed `spike_accept_iff`. -/
theorem spike_committed_rejects_one :
    ¬ FriCommittedAccepts idealSchemes ldtTower degSched spikeStatement ![1] := by
  intro hacc
  have htest := friCommittedAccepts_implies_proximityTest
    idealSchemes ldtTower degSched spikeStatement hacc
  have hnot := (spike_accept_iff (1 : ZMod 5)).not.mpr (by decide)
  exact hnot htest

def queryZero : Fin 1 → Fin 2 := fun _ => 0
def queryOne : Fin 1 → Fin 2 := fun _ => 1

/-- The wrong-challenge committed round still passes if the verifier happens
to query the coordinate on which the two folded words agree.  Thus the query
miss event is genuinely inhabited. -/
theorem spike_wrongChallenge_queryZero_accepts :
    FriRoundQueriesAccept (idealSchemes 0) (idealSchemes 1) data0
      ((idealSchemes 0).commit spikeWord)
      ((idealSchemes 1).commit (fold data0 spikeWord 3)) 1 queryZero := by
  refine ⟨fun _ => {
    left := spikeWord (data0.sec 0)
    right := spikeWord (data0.neg (data0.sec 0))
    next := fold data0 spikeWord 3 0
    leftPath := ()
    rightPath := ()
    nextPath := () }, ?_⟩
  intro a
  have ha : a = 0 := Subsingleton.elim _ _
  subst a
  simp [OpenedFriQuery, idealSchemes, idealCommitment, queryZero,
    fold, foldEven, foldOdd]
  decide

/-- Querying the differing coordinate rejects the same fixed roots.  Binding
makes adversarial opening data unable to repair the false fold equation. -/
theorem spike_wrongChallenge_queryOne_rejects :
    ¬ FriRoundQueriesAccept (idealSchemes 0) (idealSchemes 1) data0
      ((idealSchemes 0).commit spikeWord)
      ((idealSchemes 1).commit (fold data0 spikeWord 3)) 1 queryOne := by
  rintro ⟨opening, hopen⟩
  have hpinned := openedFriQuery_pins
    (idealSchemes 0) (idealSchemes 1) data0 rfl rfl (hopen 0)
  have hne : fold data0 spikeWord 3 (1 : Fin 2)
      ≠ fold data0 spikeWord 1 (1 : Fin 2) := by decide
  exact hne (by simpa [queryOne] using hpinned)

/-- The committed wrong-challenge word is at least `1/2`-far from the honest
fold -- the fixed-round sampling theorem's premise is genuinely inhabited. -/
theorem spike_wrongChallenge_distance :
    (1 / 2 : ℝ) ≤ relDist (fold data0 spikeWord 3) (fold data0 spikeWord 1) := by
  have hne : fold data0 spikeWord 3 ≠ fold data0 spikeWord 1 := by
    intro h
    have hpoint := congrFun h (1 : Fin 2)
    have hdiff : fold data0 spikeWord 3 (1 : Fin 2)
        ≠ fold data0 spikeWord 1 (1 : Fin 2) := by decide
    exact hdiff hpoint
  have hfloor := one_div_card_le_relDist (F := ZMod 5) hne
  norm_num [Fintype.card_fin] at hfloor ⊢
  exact hfloor

/-- The binding-aware query-miss theorem FIRES at the tooth and yields the
expected one-query `1/2` survival bound. -/
theorem spike_wrongChallenge_queryMiss_bound :
    ((friRoundQueryAcceptSet (idealSchemes 0) (idealSchemes 1) data0
      ((idealSchemes 0).commit spikeWord)
      ((idealSchemes 1).commit (fold data0 spikeWord 3)) 1 1).card : ℝ)
        / (Fintype.card (Fin 2) : ℝ)
      ≤ (1 - (1 / 2 : ℝ)) ^ 1 := by
  letI : Nonempty (levels 1) := ⟨(0 : Fin 2)⟩
  simpa using friRound_query_miss_pr
    (idealSchemes 0) (idealSchemes 1) data0 rfl rfl
    (1 : ZMod 5) 1 spike_wrongChallenge_distance

end HalfThresholdFriTranscriptExample

/-! ## Honest residual ledger -/

/-
* CLOSED: statement-first committed words/roots; exact selected-query
  verification; binding pinning at every selected coordinate; all-position
  committed tower = derived tower; committed acceptance containment; the
  unconditional half-threshold challenge bound; canonical FS-oracle event
  transport; an accepting and rejecting fixed-root tooth.
* `[HALF-FRI-query]`: from only `q` selected coordinates, prove that a
  committed deviation survives with probability at most
  `(1-delta/2)^q`, using `column_sampling_bridge_pr`, and compose across
  adaptive committed rounds.
* `[COMMIT-CR]`: instantiate `BindingCommitment` with the deployed Merkle /
  sponge commitment rather than the proved ideal commitment.
* `[HALF-FRI-FS]`: encode this committed FRI verifier as a `Reduction` and
  compose its event with the landed straightline/ROM theorem.  The exact
  `fsOracle` evaluation bridge is proved above; no ROM theorem is asserted
  before the game encoding exists.
-/

/-- info: 'Minidregg.Selvage.openedFriQuery_pins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms openedFriQuery_pins
/-- info: 'Minidregg.Selvage.friRound_query_miss_halfThreshold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms friRound_query_miss_halfThreshold
/-- info: 'Minidregg.Selvage.committedWord_eq_towerWord' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms committedWord_eq_towerWord
/-- info: 'Minidregg.Selvage.friCommittedAccepts_implies_proximityTest' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms friCommittedAccepts_implies_proximityTest
/-- info: 'Minidregg.Selvage.committedFri_sound_halfThen_UD' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms committedFri_sound_halfThen_UD
/-- info: 'Minidregg.Selvage.friEvent_fsOracle_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms friEvent_fsOracle_iff
/-- info: 'Minidregg.Selvage.HalfThresholdFriTranscriptExample.spike_committed_accepts_three' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HalfThresholdFriTranscriptExample.spike_committed_accepts_three
/-- info: 'Minidregg.Selvage.HalfThresholdFriTranscriptExample.spike_committed_rejects_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HalfThresholdFriTranscriptExample.spike_committed_rejects_one
/-- info: 'Minidregg.Selvage.HalfThresholdFriTranscriptExample.spike_wrongChallenge_queryMiss_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms HalfThresholdFriTranscriptExample.spike_wrongChallenge_queryMiss_bound

end Minidregg.Selvage
