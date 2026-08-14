/-
# Selvage.BaseFoldBraid — one challenge stream, two load-bearing legs

BaseFold opens the RS encoding of a multilinear table by running two checks on
the SAME challenges:

* a degree-two sumcheck for `table(b) * chi_b(z)`, whose Boolean total is the
  claimed evaluation `mle table z`; and
* the BaseFold RS descent, whose terminal symbol is `mle table r`.

The sumcheck terminal is `mle table r * eqMle z r`, so the folded codeword
supplies its first factor.  This file packages that exact braid from the landed
generic quadratic engine and the landed BaseFold completeness theorem.  It is
the algebra consumed by the round-by-round knowledge state; it is not yet the
`Reduction`/`RbrKnowledgeSoundness` instance or the BCS query layer.
-/
import Selvage.BaseFoldCompleteness
import Selvage.EqPolynomial
import Selvage.QuadraticSumcheck

namespace Minidregg.Selvage

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

/-- The second table in BaseFold's product sumcheck: the equality basis at the
public evaluation point. -/
def basefoldEqTable (z : Fin m → F) : (Fin m → Bool) → F :=
  fun b => chiEval b z

/-- The honest degree-two sumcheck messages for a BaseFold evaluation claim. -/
noncomputable def basefoldHonest (table : (Fin m → Bool) → F)
    (z : Fin m → F) (χ : ℕ → F) (i : ℕ) : Polynomial F :=
  quadHonest table (basefoldEqTable z) (fun _ => 0) χ i

/-- The public evaluation claim is exactly the Boolean total walked by the
BaseFold sumcheck. -/
omit [Fintype F] [DecidableEq F] in
theorem basefold_claim_eq_sum (table : (Fin m → Bool) → F) (z : Fin m → F) :
    ∑ b, (table b * basefoldEqTable z b - 0) = mle table z := by
  rw [mle]
  exact Finset.sum_congr rfl fun b _ => by
    simp only [basefoldEqTable, sub_zero]

/-- The BaseFold honest family is prefix-measurable. -/
omit [Fintype F] [DecidableEq F] in
theorem basefoldHonest_prefixMeasurable (table : (Fin m → Bool) → F)
    (z : Fin m → F) : PrefixMeasurable (basefoldHonest table z) :=
  quadHonest_prefixMeasurable table (basefoldEqTable z) (fun _ => 0)

/-- Every BaseFold sumcheck message has degree at most two. -/
omit [Fintype F] [DecidableEq F] in
theorem basefoldHonest_degree (table : (Fin m → Bool) → F) (z : Fin m → F)
    (χ : ℕ → F) (i : ℕ) (hi : i < m) :
    (basefoldHonest table z χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ) :=
  quadHonest_degree table (basefoldEqTable z) (fun _ => 0) χ i hi

/-- Boolean-sum consistency, anchored at the claimed evaluation rather than at
an unrelated table total. -/
theorem basefoldHonest_boolean_sum (table : (Fin m → Bool) → F)
    (z r : Fin m → F) : ∀ i, i < m →
      (basefoldHonest table z (chalOf r) i).eval 0
          + (basefoldHonest table z (chalOf r) i).eval 1
        = scChain (mle table z) (basefoldHonest table z (chalOf r))
            (chalOf r) i := by
  intro i hi
  have h := quadHonest_boolean_sum table (basefoldEqTable z) (fun _ => 0) r i hi
  rw [basefold_claim_eq_sum table z] at h
  exact h

/-- The terminal sumcheck claim is the product of the encoded polynomial's
random evaluation and the public equality polynomial. -/
theorem basefold_sumcheck_terminal (table : (Fin m → Bool) → F)
    (z r : Fin m → F) :
    scChain (mle table z) (basefoldHonest table z (chalOf r)) (chalOf r) m
      = mle table r * eqMle z r := by
  have h := scChain_quadHonest_final table (basefoldEqTable z) (fun _ => 0) r
  rw [basefold_claim_eq_sum table z] at h
  have heq : mle (basefoldEqTable z) r = eqMle z r := by
    rw [eqMle_eq_mle z]
    rfl
  have hzero : mle (fun _ : Fin m → Bool => (0 : F)) r = 0 := by
    simp [mle]
  simpa only [basefoldHonest, heq, hzero, sub_zero] using h

/-- Perfect completeness of the sumcheck leg, for every challenge vector. -/
theorem basefold_sumcheck_complete (table : (Fin m → Bool) → F)
    (z r : Fin m → F) :
    SumcheckAccepts (v := m) (basefoldHonest table z (chalOf r))
      (basefoldHonest table z (chalOf r)) (mle table z) (mle table z) r :=
  ⟨fun i hi => basefoldHonest_boolean_sum table z r i hi, rfl⟩

/-- The adaptive degree-two soundness bound specialized to the BaseFold claim.
Only the adversarial prover's prefix/degree obligations remain. -/
theorem basefold_sumcheck_soundness {table : (Fin m → Bool) → F}
    {z : Fin m → F} {prover : (ℕ → F) → ℕ → Polynomial F} {H : F}
    (hpm : PrefixMeasurable prover)
    (hdeg : ∀ (χ : ℕ → F) (i : ℕ), i < m →
      (prover χ i).degree < ((2 + 1 : ℕ) : WithBot ℕ)) :
    uniformProb (Fin m → F)
      (AdaptiveAcceptsFalse prover (basefoldHonest table z) H (mle table z))
      ≤ (m : ℝ) * (2 / Fintype.card F) := by
  have h := quad_sumcheck_soundness
    (A := table) (B := basefoldEqTable z) (C := fun _ => 0)
    (H := H) hpm hdeg
  rw [basefold_claim_eq_sum table z] at h
  exact h

/-- `chalOf` (sumcheck) and `chalExt` (folding tower) are the same padded
challenge stream.  The braid does not silently sample twice. -/
omit [Fintype F] [DecidableEq F] in
theorem chalOf_eq_chalExt (r : Fin m → F) : chalOf r = chalExt r := rfl

/-- ⭐ The algebraic braid: the sumcheck terminal and the RS descent terminal
are one value under one challenge stream. -/
theorem basefold_braid_terminal {ι : ℕ → Type*} (T : FoldingTower F ι m)
    (table : (Fin m → Bool) → F) (z r : Fin m → F) (k : ι m) :
    scChain (mle table z) (basefoldHonest table z (chalOf r)) (chalOf r) m
      = T.word (fun i => (booleanMobiusPolynomial m table).eval (T.dom 0 i))
          (chalExt r) m le_rfl k * eqMle z r := by
  rw [basefold_sumcheck_terminal, basefold_terminal_is_mle]

namespace BaseFoldBraidExample

open BaseFoldExample ProximityExample

/-- Both legs fire on the landed F5 tower: opening the table at `z = 3` starts
from value `4`, and the shared challenge `r = 2` terminates at the same braided
product on the sumcheck and codeword sides. -/
theorem braid_fires_f5 (k : levels 1) :
    scChain (mle table ![3]) (basefoldHonest table ![3] (chalOf ![2]))
        (chalOf ![2]) 1
      = ldtTower.word
          (fun i => (booleanMobiusPolynomial 1 table).eval (ldtTower.dom 0 i))
          (chalExt ![2]) 1 le_rfl k * eqMle ![3] ![2] :=
  basefold_braid_terminal ldtTower table ![3] ![2] k

end BaseFoldBraidExample

/-- info: 'Minidregg.Selvage.basefold_sumcheck_soundness' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefold_sumcheck_soundness
/-- info: 'Minidregg.Selvage.basefold_braid_terminal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms basefold_braid_terminal

end Minidregg.Selvage
