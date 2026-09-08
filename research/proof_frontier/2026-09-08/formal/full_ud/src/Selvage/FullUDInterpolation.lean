/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/ArkLib-Apache-2.0.txt.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen

Error-locator argument adapted from ArkLib GoodCoeffs.lean:72 at
22dbd4e836c15a21f68889afa69b7130da04abbb. Uses Selvage's existing
reedSolomonCode and Mathlib hammingDist, with no parallel coding definitions.
-/
import Selvage.FullUDStatement
import Theory.RSInterpolationKernel

namespace Minidregg.Selvage
open Polynomial Matrix Finset RSInterpolation
open scoped BigOperators
variable {F : Type*} [Field F] [DecidableEq F] {ι : Type*} [Fintype ι]

/-- Each actual nearby codeword supplies an evaluated BW kernel whose
error-locator block is nonzero. -/
theorem bw_specialization_of_close
    {deg e : ℕ} (hdegpos : 0 < deg) {domain : ι ↪ F}
    (u : Fin 2 → ι → F) (z : F)
    (hclose : ∃ w ∈ reedSolomonCode domain deg,
      hammingDist (u 0 + z • u 1) w ≤ e) :
    ∃ a : Fin (e+1) → F, ∃ b : Fin (e+deg) → F,
      a ≠ 0 ∧ (BW_homMatrix e deg domain (fun i => u 0 i + z * u 1 i)).mulVec
        (Fin.append a b) = 0 := by
  classical
  obtain ⟨w,hw,hdist⟩ := hclose
  obtain ⟨Pz,hPzdegree,heval⟩ := mem_reedSolomonCode_iff.mp hw
  have hPzdeg : Pz.natDegree < deg := by
    by_cases hPz0 : Pz = 0
    · simpa [hPz0] using hdegpos
    · exact (Polynomial.natDegree_lt_iff_degree_lt hPz0).mpr hPzdegree
  let D : Finset ι := Finset.univ.filter fun i => (u 0 + z • u 1) i ≠ w i
  have hDcard : D.card ≤ e := by
    simpa [D, hammingDist] using hdist
  have hAgree : ∀ i, i ∉ D → (u 0 + z • u 1) i = Pz.eval (domain i) := by
    intro i hi
    have hw' : (u 0 + z • u 1) i = w i := by
      simpa [D] using hi
    exact hw'.trans (heval i)
  -- Error-locator polynomial and the corresponding `Q`
  set E : F[X] := ∏ i ∈ D, (Polynomial.X - Polynomial.C (domain i)) with hE
  set Q : F[X] := E * Pz with hQ
  -- Coefficient vectors (truncated to the required degrees)
  let a : Fin (e + 1) → F := fun t => E.coeff t.1
  let b : Fin (e + deg) → F := fun s => Q.coeff s.1
  have hE_monic : E.Monic := by
    -- `E` is a product of monic linear factors
    simpa [hE] using (Polynomial.monic_prod_X_sub_C (b := fun i : ι => domain i) (s := D))
  have hE_natDegree : E.natDegree = D.card := by
    -- degree of product of monic polynomials is sum of degrees
    have hdeg :=
      Polynomial.natDegree_prod_of_monic (s := D)
        (f := fun i : ι => (Polynomial.X - Polynomial.C (domain i) : F[X]))
        (by
          intro i hi
          simpa using (Polynomial.monic_X_sub_C (domain i)))
    -- simplify the RHS
    convert hdeg using 1
    simp
  have hE_deg_lt : E.natDegree < e + 1 := by
    have : D.card < e + 1 := Nat.lt_succ_of_le hDcard
    simpa [hE_natDegree] using this
  have hQ_deg_lt : Q.natDegree < e + deg := by
    -- `natDegree (E*Pz) ≤ natDegree E + natDegree Pz`
    have hmul : Q.natDegree ≤ E.natDegree + Pz.natDegree := by
      simpa [hQ] using (Polynomial.natDegree_mul_le (p := E) (q := Pz))
    have hPz_le : Pz.natDegree ≤ deg - 1 := Nat.le_pred_of_lt hPzdeg
    have hE_le : E.natDegree ≤ e := by
      simpa [hE_natDegree] using hDcard
    have hsum_le : E.natDegree + Pz.natDegree ≤ e + (deg - 1) := Nat.add_le_add hE_le hPz_le
    have hle : Q.natDegree ≤ e + (deg - 1) := le_trans hmul (by simpa [Nat.add_assoc] using hsum_le)
    -- turn into a strict inequality
    have hdegpos : 0 < deg := hdegpos
    have : e + (deg - 1) < e + deg :=
      Nat.add_lt_add_left (Nat.pred_lt (Nat.ne_of_gt hdegpos)) e
    exact lt_of_le_of_lt hle this
  -- `a` is nonzero because the leading coefficient of `E` is 1
  have ha_ne : a ≠ 0 := by
    have hcard_lt : D.card < e + 1 := Nat.lt_succ_of_le hDcard
    let t0 : Fin (e + 1) := ⟨D.card, hcard_lt⟩
    have hcoeff : E.coeff D.card = 1 := by
      have hlead : E.leadingCoeff = 1 := hE_monic.leadingCoeff
      simpa [Polynomial.leadingCoeff, hE_natDegree] using hlead
    have ht0 : a t0 = 1 := by
      simpa [a, t0] using hcoeff
    intro hzero
    have hz0 : a t0 = 0 := by
      simpa using congrArg (fun f => f t0) hzero
    have h1 : (1 : F) = 0 := by
      rwa [ht0] at hz0
    exact one_ne_zero h1
  refine ⟨a, b, ha_ne, ?_⟩
  -- Show the vector is in the kernel via the characterization lemma
  apply (BW_homMatrix_mulVec_eq_zero_iff (ι := ι) (e := e) (k := deg)
      (ωs := fun i => domain i)
      (f := fun i => u 0 i + z * u 1 i)
      (a := a) (b := b)).2
  intro i
  -- Convert the coefficient sums into polynomial evaluations
  have hsum_a : (∑ t : Fin (e + 1), a t * (domain i) ^ t.1) = E.eval (domain i) := by
    have hfin : (∑ t : Fin (e + 1), a t * (domain i) ^ t.1)
        = ∑ n ∈ Finset.range (e + 1), E.coeff n * (domain i) ^ n := by
      simpa [a] using
        (Fin.sum_univ_eq_sum_range (f := fun n : ℕ => E.coeff n * (domain i) ^ n) (n := e + 1))
    have heval : E.eval (domain i) = ∑ n ∈ Finset.range (e + 1), E.coeff n * (domain i) ^ n :=
      Polynomial.eval_eq_sum_range' (p := E) (n := e + 1) hE_deg_lt (domain i)
    simpa [hfin] using heval.symm
  have hsum_b : (∑ s : Fin (e + deg), b s * (domain i) ^ s.1) = Q.eval (domain i) := by
    have hfin : (∑ s : Fin (e + deg), b s * (domain i) ^ s.1)
        = ∑ n ∈ Finset.range (e + deg), Q.coeff n * (domain i) ^ n := by
      simpa [b] using
        (Fin.sum_univ_eq_sum_range (f := fun n : ℕ => Q.coeff n * (domain i) ^ n) (n := e + deg))
    have heval : Q.eval (domain i) = ∑ n ∈ Finset.range (e + deg), Q.coeff n * (domain i) ^ n :=
      Polynomial.eval_eq_sum_range' (p := Q) (n := e + deg) hQ_deg_lt (domain i)
    simpa [hfin] using heval.symm
  -- Reduce to showing `E.eval ω * f = Q.eval ω` and discharge by cases
  by_cases hiD : i ∈ D
  · -- On error positions, `E(ω_i)=0`
    have hE0 : E.eval (domain i) = 0 := by
      -- expand `E` and use that evaluation commutes with products
      rw [hE]
      rw [Polynomial.eval_prod (s := D)
        (p := fun j : ι => (Polynomial.X - Polynomial.C (domain j) : F[X]))
        (x := domain i)]
      refine Finset.prod_eq_zero hiD ?_
      simp
    calc
      (∑ t : Fin (e + 1), a t * (domain i) ^ t.1) * (u 0 i + z * u 1 i)
          = (E.eval (domain i)) * (u 0 i + z * u 1 i) := by rw [hsum_a]
      _ = 0 := by simp [hE0]
      _ = Q.eval (domain i) := by
            have hmul_eval : Q.eval (domain i) = (E.eval (domain i)) * (Pz.eval (domain i)) := by
              rw [hQ, Polynomial.eval_mul]
            simp [hmul_eval, hE0]
      _ = ∑ s : Fin (e + deg), b s * (domain i) ^ s.1 := by rw [hsum_b]
  · -- On agreement positions, `f_i = Pz(ω_i)`
    have hf_eq : (u 0 i + z * u 1 i) = Pz.eval (domain i) := by
      have := hAgree i hiD
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using this
    calc
      (∑ t : Fin (e + 1), a t * (domain i) ^ t.1) * (u 0 i + z * u 1 i)
          = (E.eval (domain i)) * (u 0 i + z * u 1 i) := by rw [hsum_a]
      _ = (E.eval (domain i)) * (Pz.eval (domain i)) := by simp [hf_eq]
      _ = Q.eval (domain i) := by
            rw [hQ, Polynomial.eval_mul]
      _ = ∑ s : Fin (e + deg), b s * (domain i) ^ s.1 := by rw [hsum_b]

/-- The complete bounded BW certificate is now derived from the real RS
proximity premise, not assumed as an abstract certificate. -/
theorem bw_bounded_kernel_of_many_close
    (e d : ℕ) (dom : ι ↪ F) (u : Fin 2 → ι → F) (A : Finset F)
    (hd : 1 ≤ d) (hradius : 2*e+d ≤ Fintype.card ι)
    (hcard : Fintype.card ι < A.card)
    (hclose : ∀ z ∈ A, ∃ w ∈ reedSolomonCode dom d,
      hammingDist (u 0 + z • u 1) w ≤ e) :
    ∃ a : Fin (e+1) → F[X], ∃ b : Fin (e+d) → F[X],
      a ≠ 0 ∧ (∀ t, (a t).natDegree ≤ e) ∧
      (∀ s, (b s).natDegree ≤ e+1) ∧
      (BW_homMatrix e d (fun i => (Polynomial.C (dom i) : F[X]))
        (fun i => Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))).mulVec
        (Fin.append a b) = 0 := by
  apply bounded_kernel_of_specializations e d dom u A hd hradius (by omega)
  intro z hz
  exact bw_specialization_of_close hd u z (hclose z hz)

/-- info: 'Minidregg.Selvage.bw_specialization_of_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bw_specialization_of_close

/-- info: 'Minidregg.Selvage.bw_bounded_kernel_of_many_close' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms bw_bounded_kernel_of_many_close

end Minidregg.Selvage
