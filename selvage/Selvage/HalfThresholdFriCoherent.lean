/-
# Selvage.HalfThresholdFriCoherent -- coherent power-of-two FRI query paths

This file replaces `HalfThresholdFriQuery`'s independent batch at every round
by the sampler used by the runtime experiment.  A seed consists of `q`
independent uniform indices in the first folded (pair-index) domain.  At round
`j`, the verifier reads each seed index modulo the current half-domain size.

For a power-of-two domain, quotient/remainder is an equivalence between the
initial pair index and discarded high bits times the current index.  Applied
coordinatewise, this proves that every round batch has an EXACT uniform
marginal.  The batches remain correlated across rounds, but the adaptive
first-crossing proof only needs one far witness round, so the query term stays
`(1-tau)^q` and the global bound stays

  `m*b/|F| + (1-tau)^q`.

Perfect binding is inherited from the preceding module.  Concrete
Merkle/collision-resistance and Fiat--Shamir composition remain separate.
-/
import Selvage.HalfThresholdFriQuery

namespace Minidregg.Selvage

/-! ## Runtime-shaped power-of-two index paths -/

/-- A power-of-two FRI level: level `n` has `2^(ell-n)` positions. -/
abbrev PowerTwoFriLevels (ell n : ℕ) : Type := Fin (2 ^ (ell - n))

/-- The initial pair-index domain factors into the discarded high bits at
round `j` and that round's current half-domain. -/
theorem powerTwoPairSize_factor {ell m : ℕ} (hmell : m ≤ ell) (j : Fin m) :
    2 ^ (ell - 1) = 2 ^ (j : ℕ) * 2 ^ (ell - ((j : ℕ) + 1)) := by
  have hjell : (j : ℕ) + 1 ≤ ell :=
    le_trans (Nat.succ_le_iff.mpr j.isLt) hmell
  have hexp : ell - 1 = (j : ℕ) + (ell - ((j : ℕ) + 1)) := by omega
  rw [hexp, pow_add]

/-- Quotient/remainder splitting of one runtime query index. -/
def powerTwoRoundSplitEquiv {ell m : ℕ} (hmell : m ≤ ell) (j : Fin m) :
    PowerTwoFriLevels ell 1 ≃
      Fin (2 ^ (j : ℕ)) × PowerTwoFriLevels ell ((j : ℕ) + 1) :=
  (finCongr (powerTwoPairSize_factor hmell j)).trans finProdFinEquiv.symm

/-- Runtime rule: at round `j`, read the initial pair index modulo the
current half-domain size. -/
def powerTwoRoundIndex {ell m : ℕ} (_hmell : m ≤ ell) (j : Fin m)
    (x : PowerTwoFriLevels ell 1) :
    PowerTwoFriLevels ell ((j : ℕ) + 1) :=
  ⟨(x : ℕ) % 2 ^ (ell - ((j : ℕ) + 1)), Nat.mod_lt _ (by positivity)⟩

/-- The second component of quotient/remainder splitting is literally the
runtime modulo index. -/
theorem powerTwoRoundSplitEquiv_snd {ell m : ℕ} (hmell : m ≤ ell)
    (j : Fin m) (x : PowerTwoFriLevels ell 1) :
    (powerTwoRoundSplitEquiv hmell j x).2 = powerTwoRoundIndex hmell j x := by
  apply Fin.ext
  simp [powerTwoRoundSplitEquiv, powerTwoRoundIndex, finProdFinEquiv]

/-- Distribute a batch of pairs into a pair of batches. -/
def friBatchProdEquiv (q : ℕ) (A B : Type) :
    (Fin q → A × B) ≃ (Fin q → A) × (Fin q → B) where
  toFun f := ⟨fun a => (f a).1, fun a => (f a).2⟩
  invFun f a := ⟨f.1 a, f.2 a⟩
  left_inv f := by funext a; exact Prod.eta (f a)
  right_inv f := by rcases f with ⟨f, g⟩; rfl

/-- Coordinatewise quotient/remainder splitting of a `q`-query seed. -/
def powerTwoBatchSplitEquiv {ell m qCount : ℕ} (hmell : m ≤ ell)
    (j : Fin m) :
    (Fin qCount → PowerTwoFriLevels ell 1) ≃
      (Fin qCount → Fin (2 ^ (j : ℕ))) ×
        (Fin qCount → PowerTwoFriLevels ell ((j : ℕ) + 1)) :=
  (Equiv.piCongrRight fun _ => powerTwoRoundSplitEquiv hmell j).trans
    (friBatchProdEquiv qCount _ _)

/-- Coherent round batch obtained from the one initial query seed. -/
def powerTwoCoherentRound {ell m qCount : ℕ} (hmell : m ≤ ell)
    (j : Fin m) (seed : Fin qCount → PowerTwoFriLevels ell 1) :
    Fin qCount → PowerTwoFriLevels ell ((j : ℕ) + 1) :=
  fun a => powerTwoRoundIndex hmell j (seed a)

/-- All coherent round batches supplied as the schedule expected by the
adaptive transcript verifier. -/
def powerTwoCoherentSchedule {ell m qCount : ℕ} (hmell : m ≤ ell)
    (seed : Fin qCount → PowerTwoFriLevels ell 1) :
    FriIndependentQuerySchedule (PowerTwoFriLevels ell) m qCount :=
  fun j => powerTwoCoherentRound hmell j seed

theorem powerTwoBatchSplitEquiv_snd {ell m qCount : ℕ} (hmell : m ≤ ell)
    (j : Fin m) (seed : Fin qCount → PowerTwoFriLevels ell 1) :
    (powerTwoBatchSplitEquiv hmell j seed).2 =
      powerTwoCoherentRound hmell j seed := by
  funext a
  exact powerTwoRoundSplitEquiv_snd hmell j (seed a)

/-! ## Exact uniform marginal -/

/-- An event depending only on the second coordinate of a uniform product has
exactly its marginal probability. -/
theorem uniformProb_prod_snd {A B : Type} [Fintype A] [Fintype B]
    [Nonempty A] (p : B → Prop) :
    uniformProb (A × B) (fun x => p x.2) = uniformProb B p := by
  let e : {x : A × B // p x.2} ≃ A × {b : B // p b} := {
    toFun x := ⟨x.1.1, ⟨x.1.2, x.2⟩⟩
    invFun x := ⟨⟨x.1, x.2.1⟩, x.2.2⟩
    left_inv x := rfl
    right_inv x := rfl }
  unfold uniformProb
  rw [Nat.card_congr e, Nat.card_prod, Fintype.card_prod]
  simp only [Nat.card_eq_fintype_card]
  push_cast
  have hA : (Fintype.card A : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- **Every coherent round batch is exactly uniform as a pushforward.**
The discarded quotient bits are independent of the remainder batch. -/
theorem powerTwoCoherentRound_uniform {ell m qCount : ℕ}
    (hmell : m ≤ ell) (j : Fin m)
    (p : (Fin qCount → PowerTwoFriLevels ell ((j : ℕ) + 1)) → Prop) :
    uniformProb (Fin qCount → PowerTwoFriLevels ell 1)
        (fun seed => p (powerTwoCoherentRound hmell j seed))
      = uniformProb (Fin qCount → PowerTwoFriLevels ell ((j : ℕ) + 1)) p := by
  let e := powerTwoBatchSplitEquiv (qCount := qCount) hmell j
  calc
    uniformProb (Fin qCount → PowerTwoFriLevels ell 1)
        (fun seed => p (powerTwoCoherentRound hmell j seed)) =
      uniformProb
        ((Fin qCount → Fin (2 ^ (j : ℕ))) ×
          (Fin qCount → PowerTwoFriLevels ell ((j : ℕ) + 1)))
        (fun x => p x.2) := by
          calc
            _ = uniformProb (Fin qCount → PowerTwoFriLevels ell 1)
                (fun seed => p (e seed).2) := by
                  apply uniformProb_congr
                  intro seed
                  rw [powerTwoBatchSplitEquiv_snd]
            _ = _ := uniformProb_equiv e (fun x => p x.2)
    _ = uniformProb (Fin qCount → PowerTwoFriLevels ell ((j : ℕ) + 1)) p :=
      uniformProb_prod_snd p

/-- One-sided form consumed by soundness. -/
theorem powerTwoCoherentRound_uniform_le {ell m qCount : ℕ}
    (hmell : m ≤ ell) (j : Fin m)
    (p : (Fin qCount → PowerTwoFriLevels ell ((j : ℕ) + 1)) → Prop) :
    uniformProb (Fin qCount → PowerTwoFriLevels ell 1)
        (fun seed => p (powerTwoCoherentRound hmell j seed))
      ≤ uniformProb (Fin qCount → PowerTwoFriLevels ell ((j : ℕ) + 1)) p :=
  (powerTwoCoherentRound_uniform hmell j p).le

/-! ## Coherent-path adaptive soundness -/

section CoherentSoundness

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {Root Op : ℕ → Type} {ell m : ℕ}
variable (S : ∀ n, BindingCommitment (Root n) F
  (PowerTwoFriLevels ell n) (Op n))

omit [Fintype F] in
/-- A fixed challenge transcript with one `tau`-far transition passes all
coherent path checks with probability at most `(1-tau)^qCount`.  Correlation
between rounds costs nothing because the proof selects the witness round. -/
theorem friAdaptive_coherent_query_miss
    (T : FoldingTower F (PowerTwoFriLevels ell) m)
    (st : FriAdaptiveTranscript S) (hmell : m ≤ ell)
    (r : Fin m → F) (qCount : ℕ) {tau : ℝ}
    (hfar : ∃ j : Fin m, tau ≤ relDist
      (st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
      (fold (T.data j j.isLt)
        (st.wordAt r j (Nat.le_of_lt j.isLt)) (r j))) :
    uniformProb (Fin qCount → PowerTwoFriLevels ell 1)
      (fun seed => ∀ j, FriAdaptiveRoundQueriesAccept S T st r j
        (powerTwoCoherentSchedule hmell seed j))
      ≤ (1 - tau) ^ qCount := by
  obtain ⟨j, hfarj⟩ := hfar
  refine le_trans (uniformProb_mono fun seed hseed => hseed j) ?_
  refine le_trans (powerTwoCoherentRound_uniform_le hmell j
    (FriAdaptiveRoundQueriesAccept S T st r j)) ?_
  letI : Nonempty (PowerTwoFriLevels ell (j + 1)) :=
    ⟨⟨0, by positivity⟩⟩
  change uniformProb (Fin qCount → PowerTwoFriLevels ell (j + 1))
    (FriRoundQueriesAccept (S j).toOpeningScheme
      (S (j + 1)).toOpeningScheme (T.data j j.isLt)
      (st.rootAt r j (Nat.le_of_lt j.isLt))
      (st.rootAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt)) (r j))
      ≤ (1 - tau) ^ qCount
  exact @friRound_query_miss_uniform F inferInstance inferInstance
    (PowerTwoFriLevels ell j) (PowerTwoFriLevels ell (j + 1))
    (Root j) (Root (j + 1)) (Op j) (Op (j + 1))
    inferInstance inferInstance (T.dom j) (T.dom (j + 1))
    (S j) (S (j + 1)) (T.data j j.isLt)
    (st.wordAt r j (Nat.le_of_lt j.isLt))
    (st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
    (st.rootAt r j (Nat.le_of_lt j.isLt))
    (st.rootAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
    (st.rootAt_eq_commit r j (Nat.le_of_lt j.isLt))
    (st.rootAt_eq_commit r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
    (r j) qCount tau hfarj

/-- Runtime-shaped coherent verifier acceptance. -/
def FriAdaptiveCoherentAccepts
    (T : FoldingTower F (PowerTwoFriLevels ell) m) (deg : ℕ → ℕ)
    (st : FriAdaptiveTranscript S) (hmell : m ≤ ell) (qCount : ℕ)
    (r : Fin m → F) (seed : Fin qCount → PowerTwoFriLevels ell 1) : Prop :=
  FriAdaptiveSampledAccepts S T deg st qCount r
    (powerTwoCoherentSchedule hmell seed)

/-- **Global coherent-path soundness.**  For q independent uniform initial
pair indices with replacement and round-`j` modulo projection, adaptive
committed FRI acceptance obeys the same bound as the independent-round model:

  `Pr[accept] ≤ m*b/|F| + (1-tau)^qCount`.

No Merkle collision-resistance or Fiat--Shamir term is hidden here. -/
theorem friAdaptive_coherent_sampled_sound
    (T : FoldingTower F (PowerTwoFriLevels ell) m) (deg : ℕ → ℕ)
    (st : FriAdaptiveTranscript S) (hmell : m ≤ ell)
    (radius : ℕ → ℝ) (foldRadius : Fin m → ℝ)
    (qCount : ℕ) {tau : ℝ} {b : ℕ}
    (htau : tau ≤ 1)
    (hfinal : 0 ≤ radius m)
    (hgap : ∀ j : Fin m, radius (j + 1) + tau ≤ foldRadius j)
    (hfold : ∀ j : Fin m,
      FoldDistanceTransition (T.data j j.isLt) (deg j) (deg (j + 1))
        (radius j) (foldRadius j) b)
    (hfar0 : ¬ close (radius 0)
      (reedSolomonCode (T.dom 0) (deg 0))
      (st.word 0 (fun i => i.elim0))) :
    uniformProb
      ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => FriAdaptiveCoherentAccepts S T deg st hmell qCount x.1 x.2)
      ≤ (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ)
        + (1 - tau) ^ qCount := by
  classical
  have hnonempty : ∀ n, n ≤ m → Nonempty (PowerTwoFriLevels ell n) :=
    fun n hn => ⟨⟨0, by positivity⟩⟩
  obtain ⟨bad, hmeas, hcard, hcover⟩ :=
    friAdaptive_earliestDeviation_cover S T deg st radius foldRadius tau
      hfinal hnonempty hgap hfold hfar0
  let badHit : (Fin m → F) → Prop := fun r => ∃ j, r j ∈ bad r j
  let eps : ℝ := (1 - tau) ^ qCount
  have heps : 0 ≤ eps := pow_nonneg (sub_nonneg.mpr htau) _
  have hsplit : uniformProb
      ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => FriAdaptiveCoherentAccepts S T deg st hmell qCount x.1 x.2)
      ≤ uniformProb
          ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
          (fun x => badHit x.1) +
        uniformProb
          ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
          (fun x => ¬ badHit x.1 ∧
            FriAdaptiveCoherentAccepts S T deg st hmell qCount x.1 x.2) := by
    refine le_trans (uniformProb_mono fun x hx => ?_)
      (uniformProb_or_le _ _)
    by_cases hb : badHit x.1
    · exact Or.inl hb
    · exact Or.inr ⟨hb, hx⟩
  have hbadPr : uniformProb
      ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => badHit x.1)
      ≤ (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ) := by
    let e := Equiv.prodComm (Fin m → F)
      (Fin qCount → PowerTwoFriLevels ell 1)
    calc
      uniformProb ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
          (fun x => badHit x.1) =
          uniformProb ((Fin qCount → PowerTwoFriLevels ell 1) × (Fin m → F))
            (fun x => badHit x.2) := by
              simpa [e] using uniformProb_equiv e (fun x => badHit x.2)
      _ ≤ (m : ℝ) * (b : ℝ) / (Fintype.card F : ℝ) := by
        apply uniformProb_prod_le
        · positivity
        · intro seed
          exact friAdaptive_badChallenge_pr_le bad hmeas hcard
  have hqueryPr : uniformProb
      ((Fin m → F) × (Fin qCount → PowerTwoFriLevels ell 1))
      (fun x => ¬ badHit x.1 ∧
        FriAdaptiveCoherentAccepts S T deg st hmell qCount x.1 x.2)
      ≤ eps := by
    apply uniformProb_prod_le heps
    intro r
    by_cases hb : badHit r
    · rw [uniformProb_false]
      · exact heps
      · intro seed hseed
        exact hseed.1 hb
    · by_cases hmem : st.wordAt r m le_rfl ∈
          reedSolomonCode (T.dom m) (deg m)
      · have hdev : ∃ j : Fin m, tau ≤ relDist
            (st.wordAt r (j + 1) (Nat.succ_le_iff.mpr j.isLt))
            (fold (T.data j j.isLt)
              (st.wordAt r j (Nat.le_of_lt j.isLt)) (r j)) := by
          rcases hcover r hmem with hbad | hdev
          · exact False.elim (hb hbad)
          · exact hdev
        refine le_trans (uniformProb_mono fun seed hseed => hseed.2.1) ?_
        exact friAdaptive_coherent_query_miss S T st hmell r qCount hdev
      · rw [uniformProb_false]
        · exact heps
        · intro seed hseed
          exact hmem hseed.2.2
  exact le_trans hsplit (add_le_add hbadPr hqueryPr)

end CoherentSoundness

/-- info: 'Minidregg.Selvage.powerTwoCoherentRound_uniform' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms powerTwoCoherentRound_uniform
/-- info: 'Minidregg.Selvage.friAdaptive_coherent_query_miss' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms friAdaptive_coherent_query_miss
/-- info: 'Minidregg.Selvage.friAdaptive_coherent_sampled_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms friAdaptive_coherent_sampled_sound

end Minidregg.Selvage
