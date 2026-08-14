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
  letI : Nonempty (levels 1) := ⟨0⟩
  have h := basefoldIor_wrong_value_sound ldtTower table ![3] H prover
    hwrong hpm hdeg
  rw [ZMod.card] at h
  norm_num at h ⊢
  exact h

end BaseFoldIorExample

/-- info: 'Minidregg.Selvage.basefoldIor_wrong_value_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefoldIor_wrong_value_sound

end Minidregg.Selvage
