/-
# Selvage.BaseFoldIor — an operational full-word BaseFold opening

This file assembles the algebraic braid into the verifier event that the IOR
resolution actually checks.  For one challenge vector it checks:

* every prover sumcheck polynomial has degree at most two;
* every Boolean sum recurrence is valid;
* the supplied top word passes the derived RS fold descent; and
* the final sumcheck claim equals the folded terminal symbol times `eq(z,r)`.

For the exact word encoding a table, the landed braid identifies that terminal
with the honest product-sumcheck terminal.  Therefore a wrong claimed value is
accepted with probability at most `m * 2 / |F|`, by the adaptive sumcheck/RBR
leg.  Perfect completeness holds for every challenge vector.

This is deliberately the full-word IOR resolution: `proximityTest` derives and
reads whole level words.  Statement-first committed intermediate words and
sampled Merkle openings live in `HalfThresholdFriTranscript`; their query-miss
and binding costs are not hidden in the bound proved here.
-/
import Selvage.BaseFoldRbr
import Selvage.OutOfDomain

namespace Minidregg.Selvage

open Polynomial

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : ℕ → Type*} {m : ℕ}

/-- The exact full-word IOR acceptance predicate for one BaseFold evaluation
opening.  `prover` is adaptive through the challenge prefix. -/
def BaseFoldIorAccepts (T : FoldingTower F ι m) (z : Fin m → F) (H : F)
    (word : ι 0 → F) (prover : (ℕ → F) → ℕ → Polynomial F)
    (r : Fin m → F) : Prop :=
  (∀ i, i < m →
      (prover (chalOf r) i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) ∧
  (∀ i, i < m →
      (prover (chalOf r) i).eval 0 + (prover (chalOf r) i).eval 1 =
        scChain H (prover (chalOf r)) (chalOf r) i) ∧
  proximityTest T (basefoldDegSched m) word (chalExt r) ∧
  ∀ k : ι m,
    scChain H (prover (chalOf r)) (chalOf r) m =
      T.word word (chalExt r) m le_rfl k * eqMle z r

omit [Fintype F] [DecidableEq F] in
/-- ⭐ Perfect completeness of the assembled IOR verifier, for every challenge
vector.  Both legs use the same `r`. -/
theorem basefoldIor_complete (T : FoldingTower F ι m)
    (table : (Fin m → Bool) → F) (z r : Fin m → F) :
    BaseFoldIorAccepts T z (mle table z)
      (fun i => (booleanMobiusPolynomial m table).eval (T.dom 0 i))
      (basefoldHonest table z) r := by
  refine ⟨?_, ?_, basefold_proximityTest T table (chalExt r), ?_⟩
  · exact fun i hi => basefoldHonest_degree table z (chalOf r) i hi
  · exact basefoldHonest_boolean_sum table z r
  · intro k
    exact basefold_braid_terminal T table z r k

omit [Fintype F] [DecidableEq F] in
/-- Operational acceptance of a wrong value for an exact BaseFold codeword is
contained in the adaptive false-sumcheck event for that codeword's table. -/
theorem basefoldIor_wrong_value_implies_acceptsFalse
    [Nonempty (ι m)] (T : FoldingTower F ι m)
    (table : (Fin m → Bool) → F) (z : Fin m → F) (H : F)
    (prover : (ℕ → F) → ℕ → Polynomial F) (r : Fin m → F)
    (hwrong : H ≠ mle table z)
    (hacc : BaseFoldIorAccepts T z H
      (fun i => (booleanMobiusPolynomial m table).eval (T.dom 0 i)) prover r) :
    AdaptiveAcceptsFalse prover (basefoldHonest table z) H (mle table z) r := by
  refine ⟨hacc.2.1, ?_, hwrong⟩
  let k : ι m := Classical.choice inferInstance
  have hp := hacc.2.2.2 k
  have hh := basefold_braid_terminal T table z r k
  exact hp.trans hh.symm

/-- ⭐ **Exact-codeword BaseFold IOR soundness.**  For any adaptive prover with
degree-two messages, an incorrect claimed evaluation of the exact committed
table word is accepted with probability at most `m * 2 / |F|`.  This is the
new native RBR leg's per-round price composed across `m` rounds; it contains no
unpriced Merkle/query term. -/
theorem basefoldIor_wrong_value_sound [Nonempty (ι m)]
    (T : FoldingTower F ι m) (table : (Fin m → Bool) → F)
    (z : Fin m → F) (H : F)
    (prover : (ℕ → F) → ℕ → Polynomial F)
    (hwrong : H ≠ mle table z)
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (χ : ℕ → F) (i : ℕ), i < m →
      (prover χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin m → F) (fun r =>
      BaseFoldIorAccepts T z H
        (fun i => (booleanMobiusPolynomial m table).eval (T.dom 0 i)) prover r)
      ≤ (m : ℝ) * (2 / Fintype.card F) := by
  refine le_trans (uniformProb_mono fun r hacc =>
    basefoldIor_wrong_value_implies_acceptsFalse T table z H prover r hwrong hacc) ?_
  exact basefold_sumcheck_soundness hpm hdeg

/-! ## Arbitrary top words: the exact-membership `3/|F|` cone -/

/-- The strict source relation for the full-word IOR: the top word is the
BaseFold encoding of one table and the claimed value is that table's MLE at
the public point. -/
def BaseFoldExactClaim (T : FoldingTower F ι m) (z : Fin m → F) (H : F)
    (word : ι 0 → F) : Prop :=
  ∃ table : (Fin m → Bool) → F,
    word = (fun i => (booleanMobiusPolynomial m table).eval (T.dom 0 i)) ∧
    H = mle table z

omit [Fintype F] [DecidableEq F] in
/-- Every degree-window RS codeword has a definite BaseFold table.  This is
the codeword-level extraction bridge used by the arbitrary-word theorem. -/
theorem exists_basefoldTable_of_mem_code (T : FoldingTower F ι m)
    {word : ι 0 → F}
    (hmem : word ∈ reedSolomonCode (T.dom 0) (basefoldDegSched m 0)) :
    ∃ table : (Fin m → Bool) → F,
      word = fun i => (booleanMobiusPolynomial m table).eval (T.dom 0 i) := by
  obtain ⟨p, hp, hword⟩ := mem_reedSolomonCode_iff.mp hmem
  have hp' : p.degree < ((2 ^ m : ℕ) : WithBot ℕ) := by
    simpa using hp
  refine ⟨tableOfPoly m p, funext fun i => ?_⟩
  rw [hword i, booleanMobiusPolynomial_tableOfPoly m p hp']

omit [Fintype F] in
/-- ⭐ **The committed word pins the value.**  Two strict BaseFold claims over the
SAME top word and the same point carry the SAME value, as soon as the commitment
domain holds the degree window.  This is the exact statement
`BaseFoldCompleteness`'s teeth left open: `raw_commit_terminal_differs_f5` shows
that passing the descent does not pin the value, because the two words there are
DIFFERENT words.  At one fixed word there is no ambiguity at all, and the proof
consumes nothing probabilistic — interpolant uniqueness on the domain plus Möbius
injectivity.  Its companion at the commitment layer is
`MleEvalClaim.value_unique`, which pins the word from the root. -/
theorem basefoldExactClaim_value_unique [Fintype (ι 0)] (T : FoldingTower F ι m)
    (hcard : 2 ^ m ≤ Fintype.card (ι 0)) (z : Fin m → F) {H H' : F}
    {word : ι 0 → F} (h : BaseFoldExactClaim T z H word)
    (h' : BaseFoldExactClaim T z H' word) : H = H' := by
  obtain ⟨f, hwf, hHf⟩ := h
  obtain ⟨g, hwg, hHg⟩ := h'
  have hpoly : booleanMobiusPolynomial m f = booleanMobiusPolynomial m g :=
    eq_of_degreeLT_of_agree (T.dom 0) hcard
      (degree_booleanMobiusPolynomial_lt m f)
      (degree_booleanMobiusPolynomial_lt m g)
      (fun i => congrFun (hwf.symm.trans hwg) i)
  rw [hHf, booleanMobiusPolynomial_injective m hpoly, hHg]

/-- The finite set of challenge tuples accepted by the full-word IOR for fixed
statement, word, and adaptive prover. -/
noncomputable def basefoldIorAcceptSet (T : FoldingTower F ι m)
    (z : Fin m → F) (H : F) (word : ι 0 → F)
    (prover : (ℕ → F) → ℕ → Polynomial F) : Finset (Fin m → F) :=
  @Finset.filter (Fin m → F)
    (fun r => BaseFoldIorAccepts T z H word prover r)
    (Classical.decPred _) Finset.univ

omit [DecidableEq F] in
theorem mem_basefoldIorAcceptSet {T : FoldingTower F ι m}
    {z : Fin m → F} {H : F} {word : ι 0 → F}
    {prover : (ℕ → F) → ℕ → Polynomial F} {r : Fin m → F} :
    r ∈ basefoldIorAcceptSet T z H word prover ↔
      BaseFoldIorAccepts T z H word prover r := by
  simp [basefoldIorAcceptSet]

omit [DecidableEq F] in
/-- IOR acceptance is contained in the underlying proximity-test event. -/
theorem basefoldIorAcceptSet_subset (T : FoldingTower F ι m)
    (z : Fin m → F) (H : F) (word : ι 0 → F)
    (prover : (ℕ → F) → ℕ → Polynomial F) :
    basefoldIorAcceptSet T z H word prover ⊆
      acceptSet T (basefoldDegSched m) word := by
  intro r hr
  exact mem_acceptSet.mpr (mem_basefoldIorAcceptSet.mp hr).2.2.1

private theorem uniformProb_eq_card_filter (C : Type) [Fintype C]
    (p : C → Prop) [DecidablePred p] :
    uniformProb C p =
      ((Finset.univ.filter p).card : ℝ) / (Fintype.card C : ℝ) := by
  unfold uniformProb
  congr 2
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- A top word outside the BaseFold RS window can pass the full-word IOR only
through the unconditional exact-membership fold-distance event, at
`m/|F|`. -/
theorem basefoldIor_noncodeword_sound [∀ n, Fintype (ι n)]
    (T : FoldingTower F ι m) (z : Fin m → F) (H : F) (word : ι 0 → F)
    (prover : (ℕ → F) → ℕ → Polynomial F)
    (hne : ∀ n, n ≤ m → Nonempty (ι n))
    (hnotmem : word ∉ reedSolomonCode (T.dom 0) (basefoldDegSched m 0)) :
    uniformProb (Fin m → F) (fun r =>
      BaseFoldIorAccepts T z H word prover r) ≤
      (m : ℝ) / Fintype.card F := by
  classical
  letI : Nonempty (ι 0) := hne 0 (Nat.zero_le _)
  have hfar : ¬ close 0
      (reedSolomonCode (T.dom 0) (basefoldDegSched m 0)) word := by
    rintro ⟨u, hu, hdist⟩
    by_cases heq : word = u
    · exact hnotmem (heq ▸ hu)
    · have hfloor := one_div_card_le_relDist (ι := ι 0) heq
      have hpos : (0 : ℝ) < 1 / (Fintype.card (ι 0) : ℝ) := by positivity
      linarith
  have hfold : ∀ j (hj : j < m),
      FoldDistancePreserving (T.data j hj)
        (basefoldDegSched m j) (basefoldDegSched m (j + 1)) 0 1 := by
    intro j hj
    letI : Nonempty (ι (j + 1)) := hne (j + 1) (Nat.succ_le_iff.mpr hj)
    have h := foldDistancePreserving_of_lt_inv_card (T.data j hj)
      (basefoldDegSched m (j + 1)) (by norm_num : (0 : ℝ) ≤ 0)
      (by positivity : (0 : ℝ) < 1 / (Fintype.card (ι (j + 1)) : ℝ))
    rwa [← basefoldDegSched_halving m j hj] at h
  have hcard : (basefoldIorAcceptSet T z H word prover).card ≤
      (acceptSet T (basefoldDegSched m) word).card :=
    Finset.card_le_card (basefoldIorAcceptSet_subset T z H word prover)
  have hprox := proximity_sound_prob T (basefoldDegSched m)
    (by norm_num : (0 : ℝ) ≤ 0) hfold hfar
  have hprox' :
      ((acceptSet T (basefoldDegSched m) word).card : ℝ) /
          (Fintype.card F : ℝ) ^ m ≤
        (m : ℝ) / Fintype.card F := by
    simpa using hprox
  rw [show uniformProb (Fin m → F) (fun r =>
      BaseFoldIorAccepts T z H word prover r) =
      ((basefoldIorAcceptSet T z H word prover).card : ℝ) /
        (Fintype.card F : ℝ) ^ m by
    rw [uniformProb_eq_card_filter]
    simp only [basefoldIorAcceptSet, Fintype.card_fun, Fintype.card_fin,
      Nat.cast_pow]]
  refine le_trans ?_ hprox'
  have hden : (0 : ℝ) < (Fintype.card F : ℝ) ^ m := by positivity
  exact (div_le_div_iff_of_pos_right hden).mpr (by exact_mod_cast hcard)

/-- ⭐ **Arbitrary-word exact-membership BaseFold soundness.**  If a fixed top
word and claimed value do not form a strict BaseFold claim, the full-word IOR
accepts with probability at most `m·3/|F|`: one fold-distance root plus two
sumcheck roots per round.  This is the theorem behind the `3/|F|` per-opening
term used by the linear-layer ledger. -/
theorem basefoldIor_exact_sound [∀ n, Fintype (ι n)]
    (T : FoldingTower F ι m) (z : Fin m → F) (H : F) (word : ι 0 → F)
    (prover : (ℕ → F) → ℕ → Polynomial F)
    (hne : ∀ n, n ≤ m → Nonempty (ι n))
    (hfalse : ¬ BaseFoldExactClaim T z H word)
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (χ : ℕ → F) (i : ℕ), i < m →
      (prover χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin m → F) (fun r =>
      BaseFoldIorAccepts T z H word prover r) ≤
      (m : ℝ) * (3 / Fintype.card F) := by
  classical
  by_cases hmem : word ∈ reedSolomonCode (T.dom 0) (basefoldDegSched m 0)
  · obtain ⟨table, hword⟩ := exists_basefoldTable_of_mem_code T hmem
    have hwrong : H ≠ mle table z := by
      intro heq
      exact hfalse ⟨table, hword, heq⟩
    letI : Nonempty (ι m) := hne m le_rfl
    have h := basefoldIor_wrong_value_sound T table z H prover hwrong hpm hdeg
    rw [hword]
    refine le_trans h ?_
    have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by positivity
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
    gcongr
    norm_num
  · have h := basefoldIor_noncodeword_sound T z H word prover hne hmem
    refine le_trans h ?_
    have hF : (0 : ℝ) < (Fintype.card F : ℝ) := by positivity
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
    rw [div_eq_mul_inv, div_eq_mul_inv]
    nlinarith [inv_pos.mpr hF]

namespace BaseFoldIorExample

open BaseFoldExample ProximityExample

/-- The assembled verifier accepts the landed F5 opening (`table(3) = 4`) at
every challenge. -/
theorem honest_accepts_f5 (r : Fin 1 → ZMod 5) :
    BaseFoldIorAccepts ldtTower ![3] (mle table ![3])
      (fun i => (booleanMobiusPolynomial 1 table).eval (ldtTower.dom 0 i))
      (basefoldHonest table ![3]) r :=
  basefoldIor_complete ldtTower table ![3] r

/-- The wrong-value theorem specializes to a concrete `2/5` bound. -/
theorem wrong_value_bound_f5
    (H : ZMod 5) (hwrong : H ≠ mle table ![3])
    (prover : (ℕ → ZMod 5) → ℕ → Polynomial (ZMod 5))
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (χ : ℕ → ZMod 5) (i : ℕ), i < 1 →
      (prover χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin 1 → ZMod 5) (fun r =>
      BaseFoldIorAccepts ldtTower ![3] H
        (fun i => (booleanMobiusPolynomial 1 table).eval (ldtTower.dom 0 i))
        prover r) ≤ 2 / 5 := by
  letI : Nonempty (levels 1) := ⟨(⟨0, by decide⟩ : Fin 2)⟩
  have h := basefoldIor_wrong_value_sound ldtTower table ![3] H prover
    hwrong hpm hdeg
  rw [ZMod.card] at h
  norm_num at h ⊢
  exact h

/-- The F5 spike cannot form a strict BaseFold claim at any value: it is not
in the degree-two RS window. -/
theorem spike_not_exact_claim_f5 (H : ZMod 5) :
    ¬ BaseFoldExactClaim ldtTower ![3] H spikeWord := by
  rintro ⟨t, hword, hval⟩
  apply spikeWord_notMem
  rw [hword]
  simpa using evalOnDomain_mem_reedSolomonCode (ldtTower.dom 0)
    (booleanMobiusPolynomial 1 t) (degree_booleanMobiusPolynomial_lt 1 t)

/-- **Arbitrary-word premise inhabitation:** the strict theorem fires on the
landed non-codeword spike and reports the concrete one-round `3/5` bound. -/
theorem arbitrary_word_bound_f5
    (H : ZMod 5)
    (prover : (ℕ → ZMod 5) → ℕ → Polynomial (ZMod 5))
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (χ : ℕ → ZMod 5) (i : ℕ), i < 1 →
      (prover χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin 1 → ZMod 5) (fun r =>
      BaseFoldIorAccepts ldtTower ![3] H spikeWord prover r) ≤ 3 / 5 := by
  have hne : ∀ n, n ≤ 1 → Nonempty (levels n) := by
    intro n hn
    interval_cases n
    · exact ⟨(⟨0, by decide⟩ : Fin 4)⟩
    · exact ⟨(⟨0, by decide⟩ : Fin 2)⟩
  have h := basefoldIor_exact_sound ldtTower ![3] H spikeWord prover hne
    (spike_not_exact_claim_f5 H) hpm hdeg
  rw [ZMod.card] at h
  norm_num at h ⊢
  exact h

/-! ### The completeness lane's two-commitment ambiguity, closed

`BaseFoldCompleteness.raw_commit_terminal_differs_f5` exhibits two commitments of
the "same" one-variable data — the honest Möbius packing of `table` and the raw
coefficient reading `rawPoly` — that BOTH pass the whole low-degree descent at
every challenge and terminate at `4` and `2` respectively.  Read as a soundness
worry it says: does acceptance pin the value?  These three theorems answer it.

The raw word is not junk and not a forgery: it is an honest commitment to a
DIFFERENT table (`tableOfPoly 1 rawPoly = [1, 3]`), whose MLE at `3` really is
`2`.  So the two descents are two statements, not two answers to one.  What the
soundness leg must forbid — and does — is selling the raw commitment as an
opening to the honest value `4`. -/

/-- The raw-coefficient commitment IS a strict BaseFold claim: at `2`, the MLE of
the table it actually encodes. -/
theorem mle_tableOfPoly_rawPoly : mle (tableOfPoly 1 rawPoly) ![3] = 2 := by
  rw [mle]
  simp only [tableOfPoly_rawPoly]
  decide

theorem raw_commit_exact_claim_f5 :
    BaseFoldExactClaim ldtTower ![3] 2
      (fun i => rawPoly.eval (ldtTower.dom 0 i)) := by
  refine ⟨tableOfPoly 1 rawPoly, ?_, mle_tableOfPoly_rawPoly.symm⟩
  rw [booleanMobiusPolynomial_tableOfPoly 1 rawPoly rawPoly_degree]

/-- ⭐ **The ambiguity is excluded, deterministically.**  The raw commitment is not
a claim at the honest value `4` at all: one word admits one value, by
`basefoldExactClaim_value_unique`.  No challenge, no probability. -/
theorem raw_commit_not_exact_claim_at_honest_f5 :
    ¬ BaseFoldExactClaim ldtTower ![3] (mle table ![3])
        (fun i => rawPoly.eval (ldtTower.dom 0 i)) := by
  intro h
  have hval := basefoldExactClaim_value_unique ldtTower
    (by norm_num [levels] : 2 ^ 1 ≤ Fintype.card (levels 0)) ![3] h
    raw_commit_exact_claim_f5
  have h4 : mle table (![3] : Fin 1 → ZMod 5) = 4 := by decide
  rw [h4] at hval
  exact absurd hval (by decide)

/-- ⭐ **And probabilistically, against an adaptive prover.**  Completeness accepts
the raw commitment's descent at EVERY challenge; the assembled IOR accepts it as an
opening to the honest value `4` on at most `2` challenges in `5`.  This is the
`raw_commit_terminal_differs_f5` boundary crossed: acceptance of the descent alone
did not pin the value, acceptance of the braided verifier does. -/
theorem raw_commit_wrong_value_bound_f5
    (prover : (ℕ → ZMod 5) → ℕ → Polynomial (ZMod 5))
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (χ : ℕ → ZMod 5) (i : ℕ), i < 1 →
      (prover χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin 1 → ZMod 5) (fun r =>
      BaseFoldIorAccepts ldtTower ![3] (mle table ![3])
        (fun i => rawPoly.eval (ldtTower.dom 0 i)) prover r) ≤ 2 / 5 := by
  letI : Nonempty (levels 1) := ⟨(⟨0, by decide⟩ : Fin 2)⟩
  have hwrong : mle table (![3] : Fin 1 → ZMod 5) ≠ mle (tableOfPoly 1 rawPoly) ![3] := by
    rw [mle_tableOfPoly_rawPoly]
    decide
  have h := basefoldIor_wrong_value_sound ldtTower (tableOfPoly 1 rawPoly) ![3]
    (mle table ![3]) prover hwrong hpm hdeg
  rw [booleanMobiusPolynomial_tableOfPoly 1 rawPoly rawPoly_degree, ZMod.card] at h
  norm_num at h ⊢
  exact h

end BaseFoldIorExample

/-- info: 'Minidregg.Selvage.basefoldIor_wrong_value_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldIor_wrong_value_sound
/-- info: 'Minidregg.Selvage.basefoldIor_exact_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldIor_exact_sound
/-- info: 'Minidregg.Selvage.basefoldExactClaim_value_unique' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldExactClaim_value_unique
/-- info: 'Minidregg.Selvage.BaseFoldIorExample.raw_commit_not_exact_claim_at_honest_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms BaseFoldIorExample.raw_commit_not_exact_claim_at_honest_f5
/-- info: 'Minidregg.Selvage.BaseFoldIorExample.raw_commit_wrong_value_bound_f5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
  #print axioms BaseFoldIorExample.raw_commit_wrong_value_bound_f5

end Minidregg.Selvage
