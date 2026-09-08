/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/ArkLib-Apache-2.0.txt.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen

Adapted from ArkLib JointAgreement.lean:442–733 at
22dbd4e836c15a21f68889afa69b7130da04abbb. Positive-degree full-UD branch,
with integer-radius inputs and Selvage's existing RS/AgreesOn definitions.
-/
import Selvage.FullUDBivariate
import Theory.PolynomialGluing

namespace Minidregg.Selvage
open Polynomial Polynomial.Bivariate Finset
open scoped BigOperators Polynomial.Bivariate
variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι]

private theorem rs_nearby_polynomial
    {d e : ℕ} {dom : ι ↪ F} {f : ι → F} (hd : 1 ≤ d)
    (hclose : ∃ w ∈ reedSolomonCode dom d, hammingDist f w ≤ e) :
    ∃ p : F[X], p.natDegree < d ∧ hammingDist f (p.eval ∘ dom) ≤ e := by
  obtain ⟨w,hw,hclose⟩ := hclose
  obtain ⟨p,hp,heval⟩ := mem_reedSolomonCode_iff.mp hw
  have hnat : p.natDegree < d := by
    by_cases hp0 : p = 0
    · simpa [hp0] using hd
    · exact (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hp
  refine ⟨p,hnat,?_⟩
  have hw : w = p.eval ∘ dom := funext heval
  simpa [hw] using hclose

set_option maxHeartbeats 500000 in
/-- Full conservative unique-decoding cardinality core. More than `n`
good scalar folds force a common set of at least `n-e` positions, provided
`2e+d≤n`. All premises use the existing code and Hamming distance. -/
theorem fullUDCardCore (domain : ι ↪ F) (deg e : ℕ)
    (hd : 1 ≤ deg) (hradius : 2*e+deg ≤ Fintype.card ι) :
    FullUDCardCore domain deg e := by
  classical
  intro u good hclose hgood_card
  let n := Fintype.card ι
  have hn_pos : 0 < n := by dsimp [n]; omega
  letI : Nonempty ι := Fintype.card_pos_iff.mp hn_pos
  have hBW : 2*e < n-deg+1 := by dsimp [n]; omega
  have hgood_pos : 0 < good.card := lt_trans hn_pos hgood_card
  let P_x : Finset F := Finset.univ.map domain
  let P_y : Finset F := good
  have : Nonempty P_x := by
    apply Finset.Nonempty.to_subtype
    simp [P_x]
  have : Nonempty P_y := by
    apply Finset.Nonempty.to_subtype
    exact Finset.card_pos.mp hgood_pos
  have evalY_natDegree_le_degreeX (z : F) (f : F[X][Y]) :
      (Polynomial.Bivariate.evalY z f).natDegree ≤ Polynomial.Bivariate.degreeX f := by
    have heval :
        Polynomial.Bivariate.evalY z f =
          ∑ j ∈ f.support, f.coeff j * (Polynomial.C z : F[X]) ^ j := by
      simp [Polynomial.Bivariate.evalY, Polynomial.eval_eq_sum, Polynomial.sum_def]
    rw [heval]
    refine
      Polynomial.natDegree_sum_le_of_forall_le
        (s := f.support)
        (f := fun j => f.coeff j * (Polynomial.C z : F[X]) ^ j)
        (n := Polynomial.Bivariate.degreeX f)
        ?_
    intro j hj
    have hj_le :
        (f.coeff j).natDegree ≤ Polynomial.Bivariate.degreeX f :=
      Polynomial.Bivariate.coeff_natDegree_le_degreeX f j
    have hmul :
        (f.coeff j * (Polynomial.C z : F[X]) ^ j).natDegree ≤ (f.coeff j).natDegree := by
      simpa [Polynomial.C_pow] using
        (Polynomial.natDegree_mul_C_le (f := f.coeff j) (a := z ^ j))
    exact le_trans hmul hj_le
  have evalX_eval_eq_evalY_eval (x z : F) (f : F[X][Y]) :
      (Polynomial.Bivariate.evalX x f).eval z = (Polynomial.Bivariate.evalY z f).eval x := by
    calc
      (Polynomial.Bivariate.evalX x f).eval z
          = (f.map (Polynomial.evalRingHom x)).eval z := by
              exact congrArg (fun p : F[X] => p.eval z)
                (Polynomial.Bivariate.evalX_eq_map x f)
      _ = f.eval₂ (Polynomial.evalRingHom x) z := by
            simpa using
              (Polynomial.eval_map (f := Polynomial.evalRingHom x) (p := f) (x := z))
      _ = (Polynomial.eval (Polynomial.C z) f).eval x := by
            simpa [Polynomial.Bivariate.evalY] using
              (Polynomial.eval₂_at_apply
                (p := f) (f := Polynomial.evalRingHom x) (r := Polynomial.C z))
      _ = (Polynomial.Bivariate.evalY z f).eval x := by
            simp [Polynomial.Bivariate.evalY]
  obtain ⟨A, B, hA0, hA_degX, hA_degY, hB_degX, hB_degY, hAB⟩ :=
    bw_bivariate_of_many_close e deg domain u good hd hradius hgood_card hclose
  let quot_x : F → F[X] := fun z =>
    if hz : z ∈ good then
      Classical.choose (rs_nearby_polynomial hd (hclose z hz))
    else 0
  let quot_y : F → F[X] := fun x =>
    Polynomial.C (u 0 (Function.invFun domain x)) +
      Polynomial.X * Polynomial.C (u 1 (Function.invFun domain x))
  have h_card_Px : (⟨n, hn_pos⟩ : ℕ+) ≤ P_x.card := by
    simp [P_x, n]
  have h_card_Py : (⟨good.card, hgood_pos⟩ : ℕ+) ≤ P_y.card := by
    simp [P_y]
  have h_quot_x :
      ∀ z ∈ P_y,
        (quot_x z).natDegree ≤ (e + deg - 1) - e ∧
          Polynomial.Bivariate.evalY z B = (quot_x z) * (Polynomial.Bivariate.evalY z A) := by
    intro z hz
    have hz_good : z ∈ good := by simpa [P_y] using hz
    let Pz : F[X] := Classical.choose
      (rs_nearby_polynomial hd (hclose z hz_good))
    have hPz :
        Pz.natDegree < deg ∧
          hammingDist (u 0 + z • u 1) (Pz.eval ∘ domain) ≤ e := by
      simpa [Pz] using
        (Classical.choose_spec
          (rs_nearby_polynomial hd (hclose z hz_good)))
    have hquot_def : quot_x z = Pz := by
      simp [quot_x, hz_good, Pz]
    refine ⟨?_, ?_⟩
    · have hPz_le : Pz.natDegree ≤ deg - 1 := Nat.le_pred_of_lt hPz.1
      have harith : deg - 1 ≤ (e + deg - 1) - e := by omega
      exact le_trans (by simpa [hquot_def] using hPz_le) harith
    · let Dz : F[X] := Polynomial.Bivariate.evalY z B - Pz * Polynomial.Bivariate.evalY z A
      let Tz : Finset ι := Finset.univ.filter fun i =>
        (u 0 + z • u 1) i = Pz.eval (domain i)
      have hTz_card : n-e ≤ Tz.card := by
        have hpartition := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset ι))
          (p := fun i => (u 0 + z • u 1) i = Pz.eval (domain i))
        have hh : hammingDist (u 0 + z • u 1) (Pz.eval ∘ domain) =
            (Finset.univ.filter fun i => ¬ (u 0 + z • u 1) i = Pz.eval (domain i)).card := by
          simp [hammingDist]
        simp only [Finset.card_univ] at hpartition
        have hdist := hPz.2
        rw [hh] at hdist
        change Fintype.card ι-e ≤ (Finset.univ.filter fun i =>
          (u 0 + z • u 1) i = Pz.eval (domain i)).card
        omega
      have hTz_agree : ∀ i, i ∈ Tz ↔ (u 0 + z • u 1) i = Pz.eval (domain i) := by
        intro i
        simp [Tz]
      have hDz_eval :
          ∀ x ∈ Tz.image domain, Dz.eval x = 0 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, hiTz, rfl⟩
        have hi_eq : u 0 i + z * u 1 i = Pz.eval (domain i) := by
          simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using (hTz_agree i).1 hiTz
        have hEq_eval :
            (Polynomial.Bivariate.evalY z B).eval (domain i) =
              (Pz * Polynomial.Bivariate.evalY z A).eval (domain i) := by
          calc
            (Polynomial.Bivariate.evalY z B).eval (domain i)
                = (Polynomial.Bivariate.evalX (domain i) B).eval z := by
                    symm
                    exact evalX_eval_eq_evalY_eval (domain i) z B
            _ = (((Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)) *
                  Polynomial.Bivariate.evalX (domain i) A)).eval z := by
                  simpa using congrArg (fun p : F[X] => p.eval z) (hAB i)
            _ = (Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i)).eval z *
                  (Polynomial.Bivariate.evalX (domain i) A).eval z := by
                    rw [Polynomial.eval_mul]
            _ = ((Polynomial.C (u 0 i)).eval z + (Polynomial.X * Polynomial.C (u 1 i)).eval z) *
                  (Polynomial.Bivariate.evalX (domain i) A).eval z := by
                    rw [Polynomial.eval_add]
            _ = (u 0 i + (Polynomial.X * Polynomial.C (u 1 i)).eval z) *
                  (Polynomial.Bivariate.evalX (domain i) A).eval z := by
                    simp
            _ = (u 0 i + z * u 1 i) * (Polynomial.Bivariate.evalX (domain i) A).eval z := by
                  rw [Polynomial.eval_mul]
                  simp
            _ = Pz.eval (domain i) * (Polynomial.Bivariate.evalX (domain i) A).eval z := by
                  rw [hi_eq]
            _ = Pz.eval (domain i) * (Polynomial.Bivariate.evalY z A).eval (domain i) := by
                  rw [evalX_eval_eq_evalY_eval]
            _ = (Pz * Polynomial.Bivariate.evalY z A).eval (domain i) := by
                  simp [Polynomial.eval_mul, mul_comm]
        simpa [Dz, sub_eq_zero] using hEq_eval
      have hDz_deg :
          Dz.natDegree ≤ e + deg - 1 := by
        have hB_eval_deg : (Polynomial.Bivariate.evalY z B).natDegree ≤ e + deg - 1 :=
          le_trans (evalY_natDegree_le_degreeX z B) hB_degX
        have hA_eval_deg : (Polynomial.Bivariate.evalY z A).natDegree ≤ e := by
          exact le_trans (evalY_natDegree_le_degreeX z A) hA_degX
        have hprod_deg :
            (Pz * Polynomial.Bivariate.evalY z A).natDegree ≤ e + deg - 1 := by
          have hmul :
              (Pz * Polynomial.Bivariate.evalY z A).natDegree ≤
                Pz.natDegree + (Polynomial.Bivariate.evalY z A).natDegree := by
            exact Polynomial.natDegree_mul_le
              (p := Pz) (q := Polynomial.Bivariate.evalY z A)
          have hsum :
              Pz.natDegree + (Polynomial.Bivariate.evalY z A).natDegree ≤
                (deg - 1) + e := Nat.add_le_add (Nat.le_pred_of_lt hPz.1) hA_eval_deg
          have hsum' :
              Pz.natDegree + (Polynomial.Bivariate.evalY z A).natDegree ≤ e + deg - 1 := by
            omega
          exact le_trans hmul hsum'
        exact le_trans (Polynomial.natDegree_sub_le _ _) (max_le hB_eval_deg hprod_deg)
      have hdeg_lt :
          Dz.natDegree < (Tz.image domain).card := by
        have hlt : e + deg - 1 < n - e := by
          omega
        have hcard_lt : e + deg - 1 < Tz.card := lt_of_lt_of_le hlt hTz_card
        have himg :
            (Tz.image domain).card = Tz.card :=
          Finset.card_image_of_injective _ domain.injective
        exact lt_of_le_of_lt hDz_deg (by simpa [himg] using hcard_lt)
      have hDz_zero : Dz = 0 := by
        exact
          Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
            (p := Dz) (s := Tz.image domain) hDz_eval hdeg_lt
      simpa [Dz, hquot_def, sub_eq_zero] using hDz_zero
  have h_quot_y :
      ∀ x ∈ P_x,
        (quot_y x).natDegree ≤ (e + 1) - e ∧
          Polynomial.Bivariate.evalX x B = (quot_y x) * (Polynomial.Bivariate.evalX x A) := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, -, rfl⟩
    refine ⟨?_, ?_⟩
    · have hconst : (Polynomial.C (u 0 i) : F[X]).natDegree ≤ 1 := by
        simp
      have hlin' : (Polynomial.X * Polynomial.C (u 1 i) : F[X]).natDegree ≤
          (Polynomial.X : F[X]).natDegree := by
        simpa using
          (Polynomial.natDegree_mul_C_le (f := (Polynomial.X : F[X])) (a := u 1 i))
      have hlin : (Polynomial.X * Polynomial.C (u 1 i) : F[X]).natDegree ≤ 1 := by
        simpa using hlin'
      simpa [quot_y, Function.leftInverse_invFun domain.injective i] using
        (le_trans (Polynomial.natDegree_add_le _ _) (max_le hconst hlin))
    · simpa [quot_y, Function.leftInverse_invFun domain.injective i] using hAB i
  have h_le_1 :
      1 >
        ((((e + deg - 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) +
          (((e + 1 : ℕ) : ℚ) / ((⟨good.card, hgood_pos⟩ : ℕ+) : ℚ))) := by
    have h2e_deg_le_n : 2 * e + deg ≤ n := by
      omega
    have hnq_pos : (0 : ℚ) < ((⟨n, hn_pos⟩ : ℕ+) : ℚ) := by positivity
    have hfrac_lt :
        (((e + 1 : ℕ) : ℚ) / ((⟨good.card, hgood_pos⟩ : ℕ+) : ℚ)) <
          (((e + 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) := by
      have hnum_pos : (0 : ℚ) < (((e + 1 : ℕ) : ℚ)) := by positivity
      have hng :
          (((⟨n, hn_pos⟩ : ℕ+) : ℚ)) <
            (((⟨good.card, hgood_pos⟩ : ℕ+) : ℚ)) := by
        change (n : ℚ) < (good.card : ℚ)
        exact_mod_cast hgood_card
      exact div_lt_div_of_pos_left hnum_pos hnq_pos hng
    have hsum_lt :
        ((((e + deg - 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) +
          (((e + 1 : ℕ) : ℚ) / ((⟨good.card, hgood_pos⟩ : ℕ+) : ℚ)))
          <
        (((2 * e + deg : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) := by
      have hsum_lt' :
          ((((e + deg - 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) +
            (((e + 1 : ℕ) : ℚ) / ((⟨good.card, hgood_pos⟩ : ℕ+) : ℚ)))
            <
          ((((e + deg - 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) +
            (((e + 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ))) := by
        simpa [add_comm, add_left_comm, add_assoc] using
          add_lt_add_left hfrac_lt
            ((((e + deg - 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)))
      have hsum_eq :
          ((((e + deg - 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) +
            (((e + 1 : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ))) =
          (((2 * e + deg : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) := by
        rw [← add_div]
        congr 1
        exact_mod_cast (by omega : (e + deg - 1) + (e + 1) = 2 * e + deg)
      exact hsum_lt'.trans_eq hsum_eq
    have hle_one : (((2 * e + deg : ℕ) : ℚ) / ((⟨n, hn_pos⟩ : ℕ+) : ℚ)) ≤ 1 := by
      rw [div_le_iff₀ hnq_pos]
      simpa using
        (show (((2 * e + deg : ℕ) : ℚ)) ≤ ((⟨n, hn_pos⟩ : ℕ+) : ℚ) by
          exact_mod_cast h2e_deg_le_n)
    exact lt_of_lt_of_le hsum_lt hle_one
  obtain ⟨P, hBA, hP_degX, hP_degY, ⟨Q_x, hQx_card, hQx_sub, hQx_eval⟩, _⟩ :=
    polishchuk_spielman
      (a_x := e) (a_y := e) (b_x := e + deg - 1) (b_y := e + 1)
      (n_x := ⟨n, hn_pos⟩) (n_y := ⟨good.card, hgood_pos⟩)
      (h_bx_ge_ax := by omega) (h_by_ge_ay := by omega)
      (A := A) (B := B) hA0 hA_degX hB_degX hA_degY hB_degY
      P_x P_y quot_x quot_y h_card_Px h_card_Py h_quot_x h_quot_y h_le_1
  have hP_degX' : Polynomial.Bivariate.degreeX P ≤ deg - 1 := by
    omega
  let S0 : Finset ι := Q_x.preimage domain domain.injective.injOn
  have hS0_card_nat : n - e ≤ S0.card := by
    have himg : S0.map domain = Q_x := by
      ext x
      constructor
      · intro hx
        rcases Finset.mem_map.mp hx with ⟨i, hi, rfl⟩
        exact Finset.mem_preimage.mp hi
      · intro hx
        rcases Finset.mem_map.mp (hQx_sub hx) with ⟨i, -, rfl⟩
        exact Finset.mem_map.mpr ⟨i, Finset.mem_preimage.mpr hx, rfl⟩
    have hcard_eq : S0.card = Q_x.card := by
      calc
        S0.card = (S0.map domain).card := by symm; simp
        _ = Q_x.card := by simp [himg]
    exact by simpa [S0, hcard_eq, n] using hQx_card
  have hv_mem (j : ℕ) : ((P.coeff j).eval ∘ domain) ∈ reedSolomonCode domain deg := by
    have hcoeff_deg_nat : (P.coeff j).natDegree ≤ deg-1 :=
      (Polynomial.Bivariate.coeff_natDegree_le_degreeX P j).trans hP_degX'
    have hcoeff_deg : (P.coeff j).degree < (deg : WithBot ℕ) := by
      have hlt_nat : (P.coeff j).natDegree < deg := by omega
      exact lt_of_le_of_lt (Polynomial.degree_le_natDegree (p := P.coeff j))
        (by exact_mod_cast hlt_nat)
    exact mem_reedSolomonCode_iff.mpr ⟨P.coeff j,hcoeff_deg,fun _ => rfl⟩
  refine ⟨S0,hS0_card_nat,?_⟩
  intro j
  fin_cases j
  · refine ⟨(P.coeff 0).eval ∘ domain,hv_mem 0,?_⟩
    intro i hi
    have hiQ : domain i ∈ Q_x := Finset.mem_preimage.mp hi
    have hEval := hQx_eval _ hiQ
    have hcoeff := congrArg (fun p : F[X] => p.coeff 0) hEval
    have heq : (P.coeff 0).eval (domain i) = u 0 i := by
      simpa [Polynomial.Bivariate.evalX_eq_map, quot_y,
        Function.leftInverse_invFun domain.injective i] using hcoeff
    exact heq.symm
  · refine ⟨(P.coeff 1).eval ∘ domain,hv_mem 1,?_⟩
    intro i hi
    have hiQ : domain i ∈ Q_x := Finset.mem_preimage.mp hi
    have hEval := hQx_eval _ hiQ
    have hcoeff := congrArg (fun p : F[X] => p.coeff 1) hEval
    have heq : (P.coeff 1).eval (domain i) = u 1 i := by
      simpa [Polynomial.Bivariate.evalX_eq_map, quot_y,
        Function.leftInverse_invFun domain.injective i] using hcoeff
    exact heq.symm

/-- info: 'Minidregg.Selvage.fullUDCardCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms fullUDCardCore

/-- info: '_private.Selvage.FullUDCore.0.Minidregg.Selvage.rs_nearby_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms rs_nearby_polynomial

end Minidregg.Selvage
