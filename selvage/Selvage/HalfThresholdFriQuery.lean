/-
# Selvage.HalfThresholdFriQuery -- adaptive committed FRI and sampled-query coupling

`HalfThresholdFriTranscript` proves exact binding for one opened fibre and the
fixed-round `(1-tau)^q` sampling bound.  This file closes the next layer:

* intermediate words and roots may depend on the preceding challenge prefix;
* a shrinking-radius induction says that an accepting final word either hit an
  adaptive bad challenge or contains a transition at distance at least `tau`
  from its literal fold; and
* independent uniform query batches at every round detect that transition
  except with probability `(1-tau)^q`.

The query factor has NO extra `m`: after the challenge transcript is fixed,
choose one far transition; all-round query acceptance implies acceptance at
that particular round.  Challenge and query errors therefore add as

  `m*b/|F| + (1-tau)^q`.

The query sampler here draws an independent uniform batch at every round.
Standard FRI draws coherent paths from the initial domain.  Replacing this
product sampler by coherent paths needs the still-separate uniform-pushforward
theorem for the iterated squaring maps.  Merkle collision resistance and
Fiat--Shamir remain separate deployment floors as well.
-/
import Selvage.HalfThresholdFriTranscript

namespace Minidregg.Selvage

/-! ## Prefix-indexed adaptive commitments -/

/-- Restrict a full challenge tuple to its first `n` coordinates. -/
def friPrefix {F : Type*} {m : ℕ} (r : Fin m → F) (n : ℕ) (hn : n ≤ m) :
    Fin n → F :=
  fun i => r ⟨i, lt_of_lt_of_le i.isLt hn⟩

/-- A prover strategy whose level-`n` word/root may depend on exactly the
first `n` challenges.  In particular, level zero is fixed before any
challenge, while level `n+1` may depend on challenge `n`. -/
structure FriAdaptiveTranscript
    {F : Type*} {ι : ℕ → Type*} {Root Op : ℕ → Type*}
    (S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n)) where
  word : ∀ n, (Fin n → F) → ι n → F
  root : ∀ n, (Fin n → F) → Root n
  root_eq_commit : ∀ n p, root n p = (S n).commit (word n p)

namespace FriAdaptiveTranscript

variable {F : Type*} {ι : ℕ → Type*} {Root Op : ℕ → Type*}
variable {S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n)}
variable {m : ℕ}

/-- The adaptive word selected by a full challenge tuple at level `n`. -/
def wordAt (st : FriAdaptiveTranscript S) (r : Fin m → F)
    (n : ℕ) (hn : n ≤ m) : ι n → F :=
  st.word n (friPrefix r n hn)

/-- The corresponding adaptive root. -/
def rootAt (st : FriAdaptiveTranscript S) (r : Fin m → F)
    (n : ℕ) (hn : n ≤ m) : Root n :=
  st.root n (friPrefix r n hn)

theorem rootAt_eq_commit (st : FriAdaptiveTranscript S) (r : Fin m → F)
    (n : ℕ) (hn : n ≤ m) :
    st.rootAt r n hn = (S n).commit (st.wordAt r n hn) :=
  st.root_eq_commit n (friPrefix r n hn)

/-- A level word depends only on challenges strictly before that level. -/
theorem wordAt_congr (st : FriAdaptiveTranscript S)
    {r r' : Fin m → F} {n : ℕ} {hn hn' : n ≤ m}
    (h : ∀ j : Fin m, (j : ℕ) < n → r j = r' j) :
    st.wordAt r n hn = st.wordAt r' n hn' := by
  unfold wordAt
  congr 1
  funext i
  exact h ⟨i, lt_of_lt_of_le i.isLt hn⟩ i.isLt

end FriAdaptiveTranscript

/-! ## Sampled all-round verifier -/

/-- Independent `qCount`-query batches at every FRI round.  This is a
dependent product because domains shrink with the round. -/
abbrev FriIndependentQuerySchedule (ι : ℕ → Type*) (m qCount : ℕ) :=
  ∀ j : Fin m, Fin qCount → ι (j + 1)

section AdaptiveVerifier

variable {F : Type*} [Field F]
variable {ι : ℕ → Type*} {Root Op : ℕ → Type*} {m : ℕ}
variable (S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n))
variable (T : FoldingTower F ι m)

/-- Exact opened consistency of one adaptive round on a selected batch. -/
def FriAdaptiveRoundQueriesAccept
    (st : FriAdaptiveTranscript S) (r : Fin m → F) (j : Fin m)
    {qCount : ℕ} (q : Fin qCount → ι (j + 1)) : Prop :=
  ∃ opening : ∀ _a : Fin qCount,
      FriQueryOpening F (Op j) (Op (j + 1)),
    ∀ a, OpenedFriQuery (S j) (S (j + 1)) (T.data j j.isLt)
      (st.rootAt r j (Nat.le_of_lt j.isLt))
      (st.rootAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
      (r j) (q a) (opening a)

/-- Every selected equation is pinned to the adaptive committed words. -/
theorem friAdaptiveRoundQueries_pins
    (st : FriAdaptiveTranscript S) (r : Fin m → F) (j : Fin m)
    {qCount : ℕ} {q : Fin qCount → ι (j + 1)}
    (hopen : FriAdaptiveRoundQueriesAccept S T st r j q) :
    ∀ a, st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt) (q a) =
      fold (T.data j j.isLt)
        (st.wordAt r j (Nat.le_of_lt j.isLt)) (r j) (q a) := by
  obtain ⟨opening, hopen⟩ := hopen
  intro a
  exact openedFriQuery_pins (S j) (S (j + 1)) (T.data j j.isLt)
    (st.rootAt_eq_commit r j (Nat.le_of_lt j.isLt))
    (st.rootAt_eq_commit r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
    (hopen a)

/-- All sampled fold equations pass and the final adaptive word passes the
base Reed--Solomon membership check. -/
def FriAdaptiveSampledAccepts (deg : ℕ → ℕ)
    (st : FriAdaptiveTranscript S) (qCount : ℕ)
    (r : Fin m → F) (Q : FriIndependentQuerySchedule ι m qCount) : Prop :=
  (∀ j, FriAdaptiveRoundQueriesAccept S T st r j (Q j)) ∧
    st.wordAt r m le_rfl ∈ reedSolomonCode (T.dom m) (deg m)

end AdaptiveVerifier

/-! ## Uniform-query transport -/

section UniformQueries

/-- A coordinate of an independent dependent-product sampler is uniform.
This is the exact counting bridge used to lift one-round query soundness to
the all-round query schedule. -/
theorem uniformProb_pi_coord_le
    {α : Type} [Fintype α] [DecidableEq α]
    {β : α → Type} [∀ i, Fintype (β i)]
    (i : α) {p : β i → Prop} {eps : ℝ} (heps : 0 ≤ eps)
    (h : uniformProb (β i) p ≤ eps) :
    uniformProb (∀ j, β j) (fun x => p (x i)) ≤ eps := by
  let e := (Equiv.piSplitAt i β).trans (Equiv.prodComm _ _)
  calc
    uniformProb (∀ j, β j) (fun x => p (x i)) =
        uniformProb (∀ j, β j) (fun x => p (e x).2) := by
          apply uniformProb_congr
          intro x
          simp [e]
    _ = uniformProb (((∀ j : {j // j ≠ i}, β j) × β i))
          (fun x => p x.2) := uniformProb_equiv e (fun x => p x.2)
    _ ≤ eps := by
      apply uniformProb_prod_le heps
      intro a
      simpa using h

variable {F : Type} [Field F] [DecidableEq F]
variable {ι κ RootBig RootSmall OpBig OpSmall : Type}
variable [Fintype κ] [Nonempty κ]
variable {dom : ι ↪ F} {domSq : κ ↪ F}

/-- `uniformProb` rendering of the landed fixed-round query-miss theorem. -/
theorem friRound_query_miss_uniform
    (Sbig : BindingCommitment RootBig F ι OpBig)
    (Ssmall : BindingCommitment RootSmall F κ OpSmall)
    (D : FoldingData F dom domSq)
    {w : ι → F} {w' : κ → F} {rt : RootBig} {rt' : RootSmall}
    (hrt : rt = Sbig.commit w) (hrt' : rt' = Ssmall.commit w')
    (alpha : F) (qCount : ℕ) {tau : ℝ}
    (hfar : tau ≤ relDist w' (fold D w alpha)) :
    uniformProb (Fin qCount → κ)
        (FriRoundQueriesAccept Sbig.toOpeningScheme Ssmall.toOpeningScheme
          D rt rt' alpha)
      ≤ (1 - tau) ^ qCount := by
  classical
  unfold uniformProb
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  simpa [friRoundQueryAcceptSet, Fintype.card_fun] using
    friRound_query_miss_pr Sbig Ssmall D hrt hrt' alpha qCount hfar

end UniformQueries

/-! ## Shrinking-radius earliest-deviation cover -/

section AdaptiveCover

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
variable [∀ n, DecidableEq (ι n)]
variable {Root Op : ℕ → Type} {m : ℕ}
variable (S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n))

omit [Fintype F] [∀ n, DecidableEq (ι n)] in
/-- **Adaptive first-crossing cover.**  `radius n` is the invariant radius
for the prover-committed level word.  A good challenge makes the literal fold
`foldRadius j`-far.  If the next commitment is less than `tau` from that fold,
the triangle inequality and

  `radius (j+1) + tau ≤ foldRadius j`

preserve the invariant.  Hence a final codeword forces either an adaptive bad
challenge or a `tau`-far committed transition.

The returned bad set is prefix-measurable even though intermediate
commitments are adaptive. -/
theorem friAdaptive_earliestDeviation_cover
    (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    (st : FriAdaptiveTranscript S)
    (radius : ℕ → ℝ) (foldRadius : Fin m → ℝ) (tau : ℝ) {b : ℕ}
    (hfinal : 0 ≤ radius m)
    (hnonempty : ∀ n, n ≤ m → Nonempty (ι n))
    (hgap : ∀ j : Fin m, radius (j + 1) + tau ≤ foldRadius j)
    (hfold : ∀ j : Fin m,
      FoldDistanceTransition (T.data j j.isLt) (deg j) (deg (j + 1))
        (radius j) (foldRadius j) b)
    (hfar0 : ¬ close (radius 0)
      (reedSolomonCode (T.dom 0) (deg 0))
      (st.word 0 (fun i => i.elim0))) :
    ∃ bad : (Fin m → F) → Fin m → Finset F,
      (∀ (j : Fin m) (r r' : Fin m → F),
        (∀ i : Fin m, (i : ℕ) < (j : ℕ) → r i = r' i) →
          bad r j = bad r' j)
      ∧ (∀ r j, (bad r j).card ≤ b)
      ∧ ∀ r : Fin m → F,
        st.wordAt r m le_rfl ∈ reedSolomonCode (T.dom m) (deg m) →
          (∃ j, r j ∈ bad r j) ∨
          ∃ j : Fin m, tau ≤ relDist
            (st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
            (fold (T.data j j.isLt)
              (st.wordAt r j (Nat.le_of_lt j.isLt)) (r j)) := by
  classical
  have hbadAt : ∀ (j : ℕ) (hj : j < m) (w : ι j → F),
      ∃ bad : Finset F, bad.card ≤ b ∧
        (¬ close (radius j) (reedSolomonCode (T.dom j) (deg j)) w →
          ∀ alpha, alpha ∉ bad →
            ¬ close (foldRadius ⟨j, hj⟩)
              (reedSolomonCode (T.dom (j + 1)) (deg (j + 1)))
              (fold (T.data j hj) w alpha)) := by
    intro j hj w
    by_cases hw : ¬ close (radius j) (reedSolomonCode (T.dom j) (deg j)) w
    · obtain ⟨bad, hcard, hspec⟩ := hfold ⟨j, hj⟩ w hw
      exact ⟨bad, hcard, fun _ => hspec⟩
    · exact ⟨∅, Nat.zero_le b, fun hw' => absurd (not_not.mp hw) hw'⟩
  choose badAt hbadCard hbadSpec using hbadAt
  let bad : (Fin m → F) → Fin m → Finset F := fun r j =>
    badAt j j.isLt (st.wordAt r j (Nat.le_of_lt j.isLt))
  refine ⟨bad, ?_, ?_, ?_⟩
  · intro j r r' hagree
    unfold bad
    congr 1
    exact st.wordAt_congr hagree
  · intro r j
    exact hbadCard j j.isLt _
  · intro r hmem
    by_contra hcover
    push Not at hcover
    obtain ⟨hnoBad, hnoDev⟩ := hcover
    have hfarAll : ∀ (n : ℕ) (hn : n ≤ m),
        ¬ close (radius n) (reedSolomonCode (T.dom n) (deg n))
          (st.wordAt r n hn) := by
      intro n
      induction n with
      | zero =>
          intro hn
          have hp : friPrefix r 0 hn = (fun i => i.elim0) :=
            Subsingleton.elim _ _
          rw [FriAdaptiveTranscript.wordAt, hp]
          exact hfar0
      | succ j ih =>
          intro hn
          have hj : j < m := hn
          let src := st.wordAt r j (Nat.le_of_succ_le hn)
          let folded := fold (T.data j hj) src (r ⟨j, hj⟩)
          let next := st.wordAt r (j + 1) hn
          have hsrc : ¬ close (radius j)
              (reedSolomonCode (T.dom j) (deg j)) src :=
            ih (Nat.le_of_succ_le hn)
          have halpha : r ⟨j, hj⟩ ∉ badAt j hj src := by
            exact hnoBad ⟨j, hj⟩
          have hfoldFar : ¬ close (foldRadius ⟨j, hj⟩)
              (reedSolomonCode (T.dom (j + 1)) (deg (j + 1))) folded :=
            hbadSpec j hj src hsrc _ halpha
          have hdist : relDist next folded < tau := by
            simpa [next, folded, src] using hnoDev ⟨j, hj⟩
          intro hnextClose
          obtain ⟨c, hc, hnextc⟩ := hnextClose
          apply hfoldFar
          refine ⟨c, hc, ?_⟩
          letI : Nonempty (ι (j + 1)) := hnonempty (j + 1) hn
          have htri := relDist_triangle folded next c
          have hcomm : relDist folded next = relDist next folded :=
            relDist_comm folded next
          exact (calc
              relDist folded c ≤ relDist folded next + relDist next c := htri
              _ = relDist next folded + relDist next c := by rw [hcomm]
              _ < tau + radius (j + 1) := add_lt_add_of_lt_of_le hdist hnextc
              _ = radius (j + 1) + tau := by ring
              _ ≤ foldRadius ⟨j, hj⟩ := hgap ⟨j, hj⟩).le
    exact hfarAll m le_rfl (close_of_mem hmem hfinal)

end AdaptiveCover

/-! ## Sharp all-round sampled-query soundness -/

section AdaptiveQuerySoundness

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : ℕ → Type} [∀ n, Fintype (ι n)]
variable [∀ n, DecidableEq (ι n)]
variable {Root Op : ℕ → Type} {m : ℕ}
variable (S : ∀ n, BindingCommitment (Root n) F (ι n) (Op n))

omit [Fintype F] [∀ n, DecidableEq (ι n)] in
/-- Once a fixed challenge transcript has any `tau`-far committed
transition, acceptance of independent query batches at ALL rounds has
probability at most `(1-tau)^qCount`.  There is no union over rounds: select
the supplied witness round. -/
theorem friAdaptive_allRound_query_miss
    (T : FoldingTower F ι m) (st : FriAdaptiveTranscript S)
    (r : Fin m → F) (qCount : ℕ) {tau : ℝ} (htau : tau ≤ 1)
    (hnonempty : ∀ n, n ≤ m → Nonempty (ι n))
    (hfar : ∃ j : Fin m, tau ≤ relDist
      (st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
      (fold (T.data j j.isLt)
        (st.wordAt r j (Nat.le_of_lt j.isLt)) (r j))) :
    uniformProb (FriIndependentQuerySchedule ι m qCount)
      (fun Q => ∀ j, FriAdaptiveRoundQueriesAccept S T st r j (Q j))
      ≤ (1 - tau) ^ qCount := by
  obtain ⟨j, hfarj⟩ := hfar
  apply le_trans (uniformProb_mono (fun Q hQ => hQ j))
  apply uniformProb_pi_coord_le j
  · exact pow_nonneg (sub_nonneg.mpr htau) _
  · -- The event is definitionally the fixed-round committed event.
    letI : Nonempty (ι (j + 1)) :=
      hnonempty (j + 1) (Nat.succ_le_iff.mpr j.isLt)
    change uniformProb (Fin qCount → ι (j + 1))
      (FriRoundQueriesAccept (S j).toOpeningScheme
        (S (j + 1)).toOpeningScheme (T.data j j.isLt)
        (st.rootAt r j (Nat.le_of_lt j.isLt))
        (st.rootAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt)) (r j))
        ≤ (1 - tau) ^ qCount
    exact @friRound_query_miss_uniform F inferInstance inferInstance
      (ι j) (ι (j + 1)) (Root j) (Root (j + 1)) (Op j) (Op (j + 1))
      inferInstance inferInstance (T.dom j) (T.dom (j + 1))
      (S j) (S (j + 1)) (T.data j j.isLt)
      (st.wordAt r j (Nat.le_of_lt j.isLt))
      (st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
      (st.rootAt r j (Nat.le_of_lt j.isLt))
      (st.rootAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
      (st.rootAt_eq_commit r j (Nat.le_of_lt j.isLt))
      (st.rootAt_eq_commit r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
      (r j) qCount tau hfarj

/-! ### Challenge and query composition -/

/-- Prefix-measurable challenge bad sets of size at most `b` are hit with
probability at most `m*b/|F|`.  This is the `uniformProb` wrapper around the
adaptive challenge counter used by the tower theorem. -/
theorem friAdaptive_badChallenge_pr_le {b : ℕ}
    (bad : (Fin m → F) → Fin m → Finset F)
    (hmeas : ∀ (i : Fin m) (r r' : Fin m → F),
      (∀ j : Fin m, (j : ℕ) < (i : ℕ) → r j = r' j) →
        bad r i = bad r' i)
    (hcard : ∀ r i, (bad r i).card ≤ b) :
    uniformProb (Fin m → F) (fun r => ∃ i, r i ∈ bad r i)
      ≤ (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ) := by
  classical
  have hcount := card_filter_exists_coord_mem_le bad hmeas hcard
  unfold uniformProb
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.card_fun,
    Fintype.card_fin]
  have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 :=
      ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
    have hP : (0 : ℝ) < (Fintype.card F : ℝ) ^ k := by positivity
    have hcast :
        (((Finset.univ.filter fun r : Fin (k + 1) → F =>
          ∃ i, r i ∈ bad r i).card : ℝ))
          ≤ ((k + 1 : ℕ) : ℝ) * (b : ℝ) *
            (Fintype.card F : ℝ) ^ k := by
      calc
        (((Finset.univ.filter fun r : Fin (k + 1) → F =>
            ∃ i, r i ∈ bad r i).card : ℝ))
            ≤ ((((k + 1) * (b * Fintype.card F ^ k)) : ℕ) : ℝ) := by
              exact_mod_cast (by simpa using hcount)
        _ = ((k + 1 : ℕ) : ℝ) * (b : ℝ) *
            (Fintype.card F : ℝ) ^ k := by push_cast; ring
    rw [pow_succ]
    push_cast
    calc
      (((Finset.univ.filter fun r : Fin (k + 1) → F =>
          ∃ i, r i ∈ bad r i).card : ℝ)) /
          ((Fintype.card F : ℝ) ^ k * (Fintype.card F : ℝ))
          ≤ (((k + 1 : ℕ) : ℝ) * (b : ℝ) *
              (Fintype.card F : ℝ) ^ k) /
            ((Fintype.card F : ℝ) ^ k * (Fintype.card F : ℝ)) := by
              gcongr
      _ = ((k : ℝ) + 1) * (b : ℝ) /
          (Fintype.card F : ℝ) := by
            field_simp
            push_cast
            ring

omit [∀ n, DecidableEq (ι n)] in
/-- **Adaptive sampled multi-round FRI soundness.**  This is the global
challenge/query join, still in the ideal-binding and independent-per-round
query model.

The radius-gap cover supplies prefix-measurable challenge bad sets.  Off
those challenges, final-code membership forces one `tau`-far transition, and
all-round sampled acceptance is contained in that single round's miss event.
Thus the two independent sources of error add with no round factor on the
query term. -/
theorem friAdaptive_sampled_sound
    (T : FoldingTower F ι m) (deg : ℕ → ℕ)
    (st : FriAdaptiveTranscript S)
    (radius : ℕ → ℝ) (foldRadius : Fin m → ℝ)
    (qCount : ℕ) {tau : ℝ} {b : ℕ}
    (htau : tau ≤ 1)
    (hfinal : 0 ≤ radius m)
    (hnonempty : ∀ n, n ≤ m → Nonempty (ι n))
    (hgap : ∀ j : Fin m, radius (j + 1) + tau ≤ foldRadius j)
    (hfold : ∀ j : Fin m,
      FoldDistanceTransition (T.data j j.isLt) (deg j) (deg (j + 1))
        (radius j) (foldRadius j) b)
    (hfar0 : ¬ close (radius 0)
      (reedSolomonCode (T.dom 0) (deg 0))
      (st.word 0 (fun i => i.elim0))) :
    uniformProb ((Fin m → F) × FriIndependentQuerySchedule ι m qCount)
      (fun x => FriAdaptiveSampledAccepts S T deg st qCount x.1 x.2)
      ≤ (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ)
        + (1 - tau) ^ qCount := by
  classical
  obtain ⟨bad, hmeas, hcard, hcover⟩ :=
    friAdaptive_earliestDeviation_cover S T deg st radius foldRadius tau
      hfinal hnonempty hgap hfold hfar0
  let badHit : (Fin m → F) → Prop := fun r => ∃ j, r j ∈ bad r j
  let eps : ℝ := (1 - tau) ^ qCount
  have heps : 0 ≤ eps := pow_nonneg (sub_nonneg.mpr htau) _
  have hsplit : uniformProb
      ((Fin m → F) × FriIndependentQuerySchedule ι m qCount)
      (fun x => FriAdaptiveSampledAccepts S T deg st qCount x.1 x.2)
      ≤ uniformProb
          ((Fin m → F) × FriIndependentQuerySchedule ι m qCount)
          (fun x => badHit x.1) +
        uniformProb
          ((Fin m → F) × FriIndependentQuerySchedule ι m qCount)
          (fun x => ¬ badHit x.1 ∧
            FriAdaptiveSampledAccepts S T deg st qCount x.1 x.2) := by
    refine le_trans (uniformProb_mono fun x hx => ?_)
      (uniformProb_or_le _ _)
    by_cases hb : badHit x.1
    · exact Or.inl hb
    · exact Or.inr ⟨hb, hx⟩
  have hbadPr : uniformProb
      ((Fin m → F) × FriIndependentQuerySchedule ι m qCount)
      (fun x => badHit x.1)
      ≤ (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ) := by
    let e := Equiv.prodComm (Fin m → F)
      (FriIndependentQuerySchedule ι m qCount)
    calc
      uniformProb ((Fin m → F) × FriIndependentQuerySchedule ι m qCount)
          (fun x => badHit x.1) =
          uniformProb
            (FriIndependentQuerySchedule ι m qCount × (Fin m → F))
            (fun x => badHit x.2) := by
              simpa [e] using
                (uniformProb_equiv e (fun x => badHit x.2))
      _ ≤ (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ) := by
        apply uniformProb_prod_le
        · positivity
        · intro Q
          exact friAdaptive_badChallenge_pr_le bad hmeas hcard
  have hqueryPr : uniformProb
      ((Fin m → F) × FriIndependentQuerySchedule ι m qCount)
      (fun x => ¬ badHit x.1 ∧
        FriAdaptiveSampledAccepts S T deg st qCount x.1 x.2)
      ≤ eps := by
    apply uniformProb_prod_le heps
    intro r
    by_cases hb : badHit r
    · rw [uniformProb_false]
      · exact heps
      · intro Q hQ
        exact hQ.1 hb
    · by_cases hmem : st.wordAt r m le_rfl ∈
          reedSolomonCode (T.dom m) (deg m)
      · have hdev : ∃ j : Fin m, tau ≤ relDist
            (st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
            (fold (T.data j j.isLt)
              (st.wordAt r j (Nat.le_of_lt j.isLt)) (r j)) := by
          rcases hcover r hmem with hbad | hdev
          · exact False.elim (hb hbad)
          · exact hdev
        refine le_trans (uniformProb_mono fun Q hQ => hQ.2.1) ?_
        exact friAdaptive_allRound_query_miss S T st r qCount htau
          hnonempty hdev
      · rw [uniformProb_false]
        · exact heps
        · intro Q hQ
          exact hmem hQ.2.2
  exact le_trans hsplit (add_le_add hbadPr hqueryPr)

end AdaptiveQuerySoundness

/-! ## Boundary

Closed here: prefix-adaptive committed words and roots; exact binding of
sampled equations; a radius-gap first-crossing cover; the sharp
independent-per-round sampled-query term `(1-tau)^q`; and the global ideal
binding soundness head `m*b/|F| + (1-tau)^q`.

Still separate:

* instantiate the generic cover with a concrete decreasing radius schedule
  and `HalfThresholdFriTower`'s first/tail transitions;
* replace independent per-round batches by q coherent FRI paths, proving the
  iterated squaring map has the required uniform marginals;
* deployed Merkle collision resistance and Fiat--Shamir composition.
-/

/-- info: 'Minidregg.Selvage.FriAdaptiveTranscript.wordAt_congr' depends on axioms: [Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms FriAdaptiveTranscript.wordAt_congr
/-- info: 'Minidregg.Selvage.friAdaptiveRoundQueries_pins' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms friAdaptiveRoundQueries_pins
/-- info: 'Minidregg.Selvage.uniformProb_pi_coord_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms uniformProb_pi_coord_le
/-- info: 'Minidregg.Selvage.friRound_query_miss_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms friRound_query_miss_uniform
/-- info: 'Minidregg.Selvage.friAdaptive_earliestDeviation_cover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms friAdaptive_earliestDeviation_cover
/-- info: 'Minidregg.Selvage.friAdaptive_allRound_query_miss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms friAdaptive_allRound_query_miss
/-- info: 'Minidregg.Selvage.friAdaptive_sampled_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms friAdaptive_sampled_sound

end Minidregg.Selvage
