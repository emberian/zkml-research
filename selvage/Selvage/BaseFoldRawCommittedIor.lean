/-
# Selvage.BaseFoldRawCommittedIor — retain the commitment break at the top event

`BaseFoldCommittedIor` proves the sampled BaseFold bound while carrying a
`BindingCommitment`.  That is the right ideal theorem, but it is one layer too
strong for a deployed Merkle verifier: the verifier executes only
`OpeningScheme.verifyOpen`, and collision resistance is supposed to be a
priced failure event rather than an unobservable premise.

This file moves that boundary without duplicating the algebra:

* `RawFriAdaptiveTranscript` and `BaseFoldRawCommittedIorAccepts` use only the
  opening scheme actually executed by the verifier;
* `FriRawAdaptiveEquivocates` retains the exact round, query, submitted value,
  and authentication path of a position equivocation;
* `basefoldRawCommittedIor_toIdeal_or_equivocation` maps every raw acceptance
  either to the identity-commitment ideal verifier on the SAME adaptive words
  or to that concrete equivocation; and
* `basefoldRawCommittedIor_coherent_exact_sound` therefore exposes the exact
  deployment handoff

    `Pr[raw accept] <= m*3/|F| + (1-tau)^q + Pr[equivocation]`.

No collision term is guessed here.  A Merkle/sponge instantiation must map the
retained last event to its actual collision game and codec/work budget.
-/
import Selvage.BaseFoldCommittedIor

namespace Minidregg.Selvage

open Polynomial

/-! ## A prefix-adaptive transcript over a raw opening scheme -/

/-- A prover strategy carrying only executable commitment/opening operations.
Unlike `FriAdaptiveTranscript`, no perfect-binding field is present. -/
structure RawFriAdaptiveTranscript
    {F : Type} {ι : ℕ → Type} {Root Op : ℕ → Type}
    (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n)) where
  word : ∀ n, (Fin n → F) → ι n → F
  root : ∀ n, (Fin n → F) → Root n
  root_eq_commit : ∀ n p, root n p = (S n).commit (word n p)

namespace RawFriAdaptiveTranscript

variable {F : Type} {ι : ℕ → Type} {Root Op : ℕ → Type}
variable {S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n)}
variable {m : ℕ}

def wordAt (st : RawFriAdaptiveTranscript S) (r : Fin m → F)
    (n : ℕ) (hn : n ≤ m) : ι n → F :=
  st.word n (friPrefix r n hn)

def rootAt (st : RawFriAdaptiveTranscript S) (r : Fin m → F)
    (n : ℕ) (hn : n ≤ m) : Root n :=
  st.root n (friPrefix r n hn)

theorem rootAt_eq_commit (st : RawFriAdaptiveTranscript S) (r : Fin m → F)
    (n : ℕ) (hn : n ≤ m) :
    st.rootAt r n hn = (S n).commit (st.wordAt r n hn) :=
  st.root_eq_commit n (friPrefix r n hn)

/-- Forgetting a carried binding proof gives a raw transcript with identical
words, roots, and executed opening scheme. -/
def ofBinding
    (B : ∀ n, BindingCommitment (Root n) F (ι n) (Op n))
    (st : FriAdaptiveTranscript B) :
    RawFriAdaptiveTranscript (fun n => (B n).toOpeningScheme) where
  word := st.word
  root := st.root
  root_eq_commit := st.root_eq_commit

/-- Reinterpret the raw transcript's adaptive words under the identity
commitment.  This is the ideal event used by the soundness theorem; it changes
only roots/openings, never the algebraic prover strategy or its words. -/
def toIdeal (st : RawFriAdaptiveTranscript S) :
    FriAdaptiveTranscript (fun n => idealCommitment F (ι n)) where
  word := st.word
  root := st.word
  root_eq_commit := fun _ _ => rfl

@[simp] theorem toIdeal_wordAt (st : RawFriAdaptiveTranscript S)
    (r : Fin m → F) (n : ℕ) (hn : n ≤ m) :
    st.toIdeal.wordAt r n hn = st.wordAt r n hn := rfl

@[simp] theorem toIdeal_rootAt (st : RawFriAdaptiveTranscript S)
    (r : Fin m → F) (n : ℕ) (hn : n ≤ m) :
    st.toIdeal.rootAt r n hn = st.wordAt r n hn := rfl

end RawFriAdaptiveTranscript

/-! ## The raw sampled verifier and its retained equivocation event -/

variable {F : Type} [Field F]
variable {ι : ℕ → Type} {Root Op : ℕ → Type} {m : ℕ}

/-- Exact sampled consistency at one round, using only the raw verifier. -/
def RawFriAdaptiveRoundQueriesAccept
    (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (st : RawFriAdaptiveTranscript S)
    (r : Fin m → F) (j : Fin m) {qCount : ℕ}
    (q : Fin qCount → ι (j + 1)) : Prop :=
  ∃ opening : ∀ _a : Fin qCount,
      FriQueryOpening F (Op j) (Op (j + 1)),
    ∀ a, OpenedFriQuery (S j) (S (j + 1)) (T.data j j.isLt)
      (st.rootAt r j (Nat.le_of_lt j.isLt))
      (st.rootAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
      (r j) (q a) (opening a)

/-- All raw sampled fold checks plus the terminal RS membership check. -/
def RawFriAdaptiveSampledAccepts
    (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    (st : RawFriAdaptiveTranscript S) (qCount : ℕ)
    (r : Fin m → F) (Q : FriIndependentQuerySchedule ι m qCount) : Prop :=
  (∀ j, RawFriAdaptiveRoundQueriesAccept S T st r j (Q j)) ∧
    st.wordAt r m le_rfl ∈ reedSolomonCode (T.dom m) (deg m)

/-- The raw top-level sampled BaseFold verifier.  Every predicate here is
executable without assuming position binding. -/
def BaseFoldRawCommittedIorAccepts
    (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (st : RawFriAdaptiveTranscript S)
    (z : Fin m → F) (H : F)
    (prover : (ℕ → F) → ℕ → Polynomial F) (qCount : ℕ)
    (r : Fin m → F) (Q : FriIndependentQuerySchedule ι m qCount) : Prop :=
  (∀ i, i < m →
      (prover (chalOf r) i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) ∧
  (∀ i, i < m →
      (prover (chalOf r) i).eval 0 + (prover (chalOf r) i).eval 1 =
        scChain H (prover (chalOf r)) (chalOf r) i) ∧
  RawFriAdaptiveSampledAccepts S T (basefoldDegSched m) st qCount r Q ∧
  ∀ k : ι m,
    scChain H (prover (chalOf r)) (chalOf r) m =
      st.wordAt r m le_rfl k * eqMle z r

/-- The exact global commitment-failure event retained by the raw verifier:
one accepted batch contains a named three-symbol position equivocation. -/
def FriRawAdaptiveEquivocates
    (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (st : RawFriAdaptiveTranscript S)
    (r : Fin m → F) (qCount : ℕ)
    (Q : FriIndependentQuerySchedule ι m qCount) : Prop :=
  ∃ j : Fin m,
    FriRoundQueriesEquivocate (S j) (S (j + 1)) (T.data j j.isLt)
      (st.rootAt r j (Nat.le_of_lt j.isLt))
      (st.rootAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
      (st.wordAt r j (Nat.le_of_lt j.isLt))
      (st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
      (r j) (Q j)

private def idealFriQueryOpening
    {ι κ : Type} {dom : ι ↪ F} {domSq : κ ↪ F}
    (D : FoldingData F dom domSq) (w : ι → F) (w' : κ → F)
    (k : κ) : FriQueryOpening F Unit Unit where
  left := w (D.sec k)
  right := w (D.neg (D.sec k))
  next := w' k
  leftPath := ()
  rightPath := ()
  nextPath := ()

private theorem idealFriQueryOpening_accepts
    {ι κ : Type} {dom : ι ↪ F} {domSq : κ ↪ F}
    (D : FoldingData F dom domSq) (w : ι → F) (w' : κ → F)
    (alpha : F) (k : κ) (hpin : w' k = fold D w alpha k) :
    OpenedFriQuery (idealCommitment F ι) (idealCommitment F κ) D
      w w' alpha k (idealFriQueryOpening D w w' k) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  simpa [fold] using hpin

/-! ## Lossless verifier split: ideal event or concrete equivocation -/

/-- Every raw acceptance either becomes the already-priced ideal acceptance
on the same adaptive words or retains an exact authentication equivocation.
This is the top-level `[COMMIT-CR]` branch point. -/
theorem basefoldRawCommittedIor_toIdeal_or_equivocation
    (S : ∀ n, OpeningScheme (Root n) F (ι n) (Op n))
    (T : FoldingTower F ι m) (st : RawFriAdaptiveTranscript S)
    (z : Fin m → F) (H : F)
    (prover : (ℕ → F) → ℕ → Polynomial F) (qCount : ℕ)
    (r : Fin m → F) (Q : FriIndependentQuerySchedule ι m qCount)
    (hacc : BaseFoldRawCommittedIorAccepts S T st z H prover qCount r Q) :
    BaseFoldCommittedIorAccepts (fun n => idealCommitment F (ι n)) T
        st.toIdeal z H prover qCount r Q ∨
      FriRawAdaptiveEquivocates S T st r qCount Q := by
  classical
  by_cases hequiv : FriRawAdaptiveEquivocates S T st r qCount Q
  · exact Or.inr hequiv
  · left
    refine ⟨hacc.1, hacc.2.1, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro j
        have hround := hacc.2.2.1.1 j
        have hsplit := friRoundQueries_pin_or_equivocation
          (S j) (S (j + 1)) (T.data j j.isLt)
          (st.rootAt_eq_commit r j (Nat.le_of_lt j.isLt))
          (st.rootAt_eq_commit r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
          (r j) (Q j) hround
        rcases hsplit with hpins | hbad
        · refine ⟨fun a => idealFriQueryOpening (T.data j j.isLt)
              (st.wordAt r j (Nat.le_of_lt j.isLt))
              (st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
              (Q j a), ?_⟩
          intro a
          rw [RawFriAdaptiveTranscript.toIdeal_rootAt,
            RawFriAdaptiveTranscript.toIdeal_rootAt]
          exact idealFriQueryOpening_accepts (T.data j j.isLt)
            (st.wordAt r j (Nat.le_of_lt j.isLt))
            (st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
            (r j) (Q j a) (hpins a)
        · exact False.elim (hequiv ⟨j, hbad⟩)
      · simpa using hacc.2.2.1.2
    · intro k
      simpa using hacc.2.2.2 k

section CoherentSoundness

variable [Fintype F] [DecidableEq F]
variable {ell : ℕ} {RootP OpP : ℕ → Type}

/-- ⭐ **Raw sampled BaseFold soundness with the CR event exposed.**  The
algebraic and coherent-query terms are inherited without loss from the ideal
theorem; every use of short-root binding is isolated in the final probability
of a concrete `PositionEquivocation` carried by an accepted opening batch. -/
theorem basefoldRawCommittedIor_coherent_exact_sound
    (SP : ∀ n, OpeningScheme (RootP n) F
      (PowerTwoFriLevels ell n) (OpP n))
    (T : FoldingTower F (PowerTwoFriLevels ell) m)
    (st : RawFriAdaptiveTranscript SP) (hmell : m ≤ ell)
    (z : Fin m → F) (H : F)
    (word : PowerTwoFriLevels ell 0 → F)
    (prover : (ℕ → F) → ℕ → Polynomial F)
    (qCount : ℕ) {tau : ℝ} (htau1 : tau ≤ 1)
    (htau : ∀ j : Fin m,
      tau ≤ 1 / (Fintype.card (PowerTwoFriLevels ell (j + 1)) : ℝ))
    (hword0 : st.word 0 (fun i => i.elim0) = word)
    (hfalse : ¬ BaseFoldExactClaim T z H word)
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (chi : ℕ → F) (i : ℕ), i < m →
      (prover chi i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb
      ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => BaseFoldRawCommittedIorAccepts SP T st z H prover qCount x.1
        (powerTwoCoherentSchedule hmell x.2))
      ≤ (m : ℝ) * (3 / Fintype.card F) + (1 - tau) ^ qCount +
        uniformProb
          ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
          (fun x => FriRawAdaptiveEquivocates SP T st x.1 qCount
            (powerTwoCoherentSchedule hmell x.2)) := by
  let idealAccept :
      (Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1) → Prop :=
    fun x => BaseFoldCommittedIorAccepts
      (fun n => idealCommitment F (PowerTwoFriLevels ell n)) T st.toIdeal
      z H prover qCount x.1 (powerTwoCoherentSchedule hmell x.2)
  let equivocation :
      (Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1) → Prop :=
    fun x => FriRawAdaptiveEquivocates SP T st x.1 qCount
      (powerTwoCoherentSchedule hmell x.2)
  refine le_trans (uniformProb_mono fun x hacc =>
    basefoldRawCommittedIor_toIdeal_or_equivocation SP T st z H prover
      qCount x.1 (powerTwoCoherentSchedule hmell x.2) hacc) ?_
  refine le_trans (uniformProb_or_le idealAccept equivocation) ?_
  apply add_le_add_right
  exact basefoldCommittedIor_coherent_exact_sound
    (fun n => idealCommitment F (PowerTwoFriLevels ell n)) T st.toIdeal hmell
    z H word prover qCount htau1 htau hword0 hfalse hpm hdeg

end CoherentSoundness

end Minidregg.Selvage
