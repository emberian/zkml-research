/-
# Selvage.BaseFoldCommittedIor — one honest sampled opening transcript

`BaseFoldIor` assembles the full-word algebraic verifier.  The committed FRI
files separately model prefix-adaptive level roots and sampled authenticated
fold equations.  This file joins their honest sides under one challenge
stream.

`derivedFriAdaptiveTranscript` commits, at level `n`, to the literal first
`n` folds of the top word under the challenge prefix available at that point.
`BaseFoldCommittedIorAccepts` then checks the degree-two sumcheck messages,
their Boolean recurrences, every sampled FRI opening, the terminal code, and
the braided terminal MLE equation.  `basefoldCommittedIor_complete` proves all
of those checks together for every challenge tuple and every query schedule.

This is perfect-binding interactive completeness.  It does not price the raw
equivocation branch, random-oracle compilation, or query soundness a second
time: `HalfThresholdFriTranscript` now retains equivocations, while
`HalfThresholdFriQuery` and `HalfThresholdFriCoherent` own the sampled-query
bounds.
-/
import Selvage.BaseFoldIor
import Selvage.HalfThresholdFriCoherent

namespace Minidregg.Selvage

open Polynomial

variable {F : Type} [Field F]
variable {ι : ℕ → Type} {Root Op : ℕ → Type} {m : ℕ}

/-! ## The honest prefix-adaptive committed tower -/

/-- Commit at level `n` to the literal derived fold word under exactly the
first `n` challenges.  Values beyond the tower height are irrelevant and are
filled with the zero word so the adaptive family remains total in `n`. -/
noncomputable def derivedFriAdaptiveTranscript
    (S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (word0 : ι 0 → F) :
    FriAdaptiveTranscript S where
  word := fun n pfx =>
    if hn : n ≤ m then T.word word0 (chalExt pfx) n hn else 0
  root := fun n pfx => (S n).commit
    (if hn : n ≤ m then T.word word0 (chalExt pfx) n hn else 0)
  root_eq_commit := fun _ _ => rfl

/-- Reading the derived adaptive transcript with a full challenge tuple gives
exactly the ordinary folding-tower word on that tuple. -/
theorem derivedFriAdaptiveTranscript_wordAt
    (S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (word0 : ι 0 → F)
    (r : Fin m → F) (n : ℕ) (hn : n ≤ m) :
    (derivedFriAdaptiveTranscript S T word0).wordAt r n hn =
      T.word word0 (chalExt r) n hn := by
  unfold FriAdaptiveTranscript.wordAt derivedFriAdaptiveTranscript
  dsimp only
  rw [dif_pos hn]
  apply T.word_congr word0 n hn
  intro j hj
  rw [chalExt, dif_pos hj, chalExt, dif_pos (lt_of_lt_of_le hj hn)]
  rfl

/-- Every queried fibre of the derived transcript has the literal honest
opening and fold equation. -/
theorem derivedFriAdaptiveRoundQueries_accept
    (S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (word0 : ι 0 → F)
    (r : Fin m → F) (j : Fin m) {qCount : ℕ}
    (q : Fin qCount → ι (j + 1)) :
    FriAdaptiveRoundQueriesAccept S T
      (derivedFriAdaptiveTranscript S T word0) r j q := by
  let st := derivedFriAdaptiveTranscript S T word0
  let src := st.wordAt r j (Nat.le_of_lt j.isLt)
  have hnext : st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt) =
      fold (T.data j j.isLt) src (r j) := by
    dsimp only [st, src]
    rw [derivedFriAdaptiveTranscript_wordAt,
      derivedFriAdaptiveTranscript_wordAt, T.word_succ, chalExt_coe]
  refine ⟨fun a => {
    left := src ((T.data j j.isLt).sec (q a))
    right := src ((T.data j j.isLt).neg ((T.data j j.isLt).sec (q a)))
    next := fold (T.data j j.isLt) src (r j) (q a)
    leftPath := (S j).openAt src ((T.data j j.isLt).sec (q a))
    rightPath := (S j).openAt src
      ((T.data j j.isLt).neg ((T.data j j.isLt).sec (q a)))
    nextPath := (S (j + 1)).openAt (fold (T.data j j.isLt) src (r j)) (q a)
  }, ?_⟩
  intro a
  unfold OpenedFriQuery
  rw [(st.rootAt_eq_commit r j (Nat.le_of_lt j.isLt)),
    (st.rootAt_eq_commit r (j + 1) (Nat.succ_le_iff.mpr j.isLt)), hnext]
  exact ⟨(S j).verifyOpen_commit _ _, (S j).verifyOpen_commit _ _,
    (S (j + 1)).verifyOpen_commit _ _, rfl⟩

/-- The honest derived transcript passes every sampled FRI equation and its
terminal low-degree check, for every query schedule. -/
theorem derivedFriAdaptiveSampled_complete
    (S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (table : (Fin m → Bool) → F)
    (qCount : ℕ) (r : Fin m → F)
    (Q : FriIndependentQuerySchedule ι m qCount) :
    FriAdaptiveSampledAccepts S T (basefoldDegSched m)
      (derivedFriAdaptiveTranscript S T
        (fun i => (booleanMobiusPolynomial m table).eval (T.dom 0 i)))
      qCount r Q := by
  refine ⟨fun j => derivedFriAdaptiveRoundQueries_accept S T _ r j (Q j), ?_⟩
  rw [derivedFriAdaptiveTranscript_wordAt]
  exact basefold_proximityTest T table (chalExt r)

/-! ## The sampled committed BaseFold verifier -/

/-- The interactive sampled-commitment resolution of one BaseFold opening.
The prover's sumcheck messages and committed FRI level words are both
prefix-adaptive and consume the same field challenge tuple. -/
def BaseFoldCommittedIorAccepts
    (S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (st : FriAdaptiveTranscript S)
    (z : Fin m → F) (H : F)
    (prover : (ℕ → F) → ℕ → Polynomial F) (qCount : ℕ)
    (r : Fin m → F) (Q : FriIndependentQuerySchedule ι m qCount) : Prop :=
  (∀ i, i < m →
      (prover (chalOf r) i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) ∧
  (∀ i, i < m →
      (prover (chalOf r) i).eval 0 + (prover (chalOf r) i).eval 1 =
        scChain H (prover (chalOf r)) (chalOf r) i) ∧
  FriAdaptiveSampledAccepts S T (basefoldDegSched m) st qCount r Q ∧
  ∀ k : ι m,
    scChain H (prover (chalOf r)) (chalOf r) m =
      st.wordAt r m le_rfl k * eqMle z r

/-- If the accepted committed terminal word is the literal terminal derived
from `word`, the sampled committed verifier refines to the already-proved
full-word IOR event.  This is the algebra/query boundary: the only new fact
needed from the sampled Merkle game is terminal-word consistency. -/
theorem BaseFoldCommittedIorAccepts.toFullWord
    (S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (st : FriAdaptiveTranscript S)
    (z : Fin m → F) (H : F) (word : ι 0 → F)
    (prover : (ℕ → F) → ℕ → Polynomial F) (qCount : ℕ)
    (r : Fin m → F) (Q : FriIndependentQuerySchedule ι m qCount)
    (hfinal : st.wordAt r m le_rfl = T.word word (chalExt r) m le_rfl)
    (hacc : BaseFoldCommittedIorAccepts S T st z H prover qCount r Q) :
    BaseFoldIorAccepts T z H word prover r := by
  refine ⟨hacc.1, hacc.2.1, ?_, ?_⟩
  · unfold proximityTest
    rw [← hfinal]
    exact hacc.2.2.1.2
  · intro k
    rw [← hfinal]
    exact hacc.2.2.2 k

section SoundnessHandoff

variable [Fintype F] [DecidableEq F] [∀ n, Fintype (ι n)]

/-- ⭐ **Committed-to-IOR soundness handoff.**  If every accepted sampled
transcript has the correct derived terminal, then adding an arbitrary uniform
query schedule does not change the arbitrary-word BaseFold algebraic bound
`m * 3 / |F|`.  A concrete sampled protocol must prove `hfinal` off its named
query-miss/equivocation event; this theorem deliberately does not erase that
remaining branch. -/
theorem basefoldCommittedIor_exact_sound_of_terminalConsistency
    (S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (st : FriAdaptiveTranscript S)
    (z : Fin m → F) (H : F) (word : ι 0 → F)
    (prover : (ℕ → F) → ℕ → Polynomial F) (qCount : ℕ)
    (hne : ∀ n, n ≤ m → Nonempty (ι n))
    (hfalse : ¬ BaseFoldExactClaim T z H word)
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (χ : ℕ → F) (i : ℕ), i < m →
      (prover χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ))
    (hfinal : ∀ (r : Fin m → F)
        (Q : FriIndependentQuerySchedule ι m qCount),
      BaseFoldCommittedIorAccepts S T st z H prover qCount r Q →
        st.wordAt r m le_rfl = T.word word (chalExt r) m le_rfl) :
    uniformProb
      (FriIndependentQuerySchedule ι m qCount × (Fin m → F))
      (fun x => BaseFoldCommittedIorAccepts S T st z H prover qCount x.2 x.1)
      ≤ (m : ℝ) * (3 / Fintype.card F) := by
  apply uniformProb_prod_le
  · positivity
  · intro Q
    refine le_trans (uniformProb_mono fun r hacc =>
      BaseFoldCommittedIorAccepts.toFullWord S T st z H word prover qCount r Q
        (hfinal r Q hacc) hacc) ?_
    exact basefoldIor_exact_sound T z H word prover hne hfalse hpm hdeg

end SoundnessHandoff

/-- ⭐ **End-to-end interactive completeness at sampled-commitment
resolution.**  The honest adaptive roots, all sampled authentication paths,
the BaseFold degree-two sumcheck, terminal code check, and braided MLE equation
accept together for every verifier challenge and query schedule. -/
theorem basefoldCommittedIor_complete
    (S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (table : (Fin m → Bool) → F)
    (z : Fin m → F) (qCount : ℕ) (r : Fin m → F)
    (Q : FriIndependentQuerySchedule ι m qCount) :
    BaseFoldCommittedIorAccepts S T
      (derivedFriAdaptiveTranscript S T
        (fun i => (booleanMobiusPolynomial m table).eval (T.dom 0 i)))
      z (mle table z) (basefoldHonest table z) qCount r Q := by
  refine ⟨fun i hi => basefoldHonest_degree table z (chalOf r) i hi,
    basefoldHonest_boolean_sum table z r,
    derivedFriAdaptiveSampled_complete S T table qCount r Q, ?_⟩
  intro k
  rw [derivedFriAdaptiveTranscript_wordAt]
  exact basefold_braid_terminal T table z r k

/-! ## F5 premise inhabitation -/

namespace BaseFoldCommittedIorExample

open BaseFoldExample ProximityExample HalfThresholdFriTranscriptExample

def queryScheduleZero : FriIndependentQuerySchedule levels 1 1 := by
  intro j _
  have hj : j = (0 : Fin 1) := Subsingleton.elim _ _
  subst j
  exact (0 : Fin 2)

/-- The complete sampled-commitment verifier fires on the landed F5 opening
at challenge `3` and one coherent zero-coordinate query. -/
theorem committedIor_fires_f5 :
    BaseFoldCommittedIorAccepts idealSchemes ldtTower
      (derivedFriAdaptiveTranscript idealSchemes ldtTower
        (fun i => (booleanMobiusPolynomial 1 table).eval (ldtTower.dom 0 i)))
      ![3] (mle table ![3]) (basefoldHonest table ![3]) 1 ![3]
      queryScheduleZero :=
  basefoldCommittedIor_complete idealSchemes ldtTower table ![3] 1 ![3]
    queryScheduleZero

end BaseFoldCommittedIorExample

end Minidregg.Selvage
