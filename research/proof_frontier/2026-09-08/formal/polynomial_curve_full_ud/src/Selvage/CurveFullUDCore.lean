/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in LICENSES/ArkLib-Apache-2.0.txt.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen

Adapted from ArkLib JointAgreement.lean:442–733 at
22dbd4e836c15a21f68889afa69b7130da04abbb. Positive-degree full-UD branch,
generalized to degree-M challenge curves following BCIKS20 §6.1,
with integer-radius inputs and Selvage's existing RS/AgreesOn definitions.
-/
import Selvage.CurveFullUDBivariate
import Theory.PolynomialGluing

namespace Minidregg.Selvage
open Polynomial Polynomial.Bivariate Finset
open scoped BigOperators Polynomial.Bivariate
variable {F : Type*} [Field F] [DecidableEq F]
variable {ι : Type*} [Fintype ι]

private theorem curve_rs_nearby_polynomial
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
/-- Full conservative unique-decoding cardinality core. More than `M*n`
good scalar curve points force a common set of at least `n-e` positions, provided
`2e+d≤n`. All premises use the existing code and Hamming distance. -/
theorem curveFullUDCardCore (M : ℕ) (domain : ι ↪ F) (deg e : ℕ)
    (hM : 1 ≤ M)
    (hd : 1 ≤ deg) (hradius : 2*e+deg ≤ Fintype.card ι) :
    CurveFullUDCardCore M domain deg e := by
  classical
  intro u good hclose hgood_card
  let n := Fintype.card ι
  have hn_pos : 0 < n := by dsimp [n]; omega
  letI : Nonempty ι := Fintype.card_pos_iff.mp hn_pos
  have hBW : 2*e < n-deg+1 := by dsimp [n]; omega
  have hgood_pos : 0 < good.card := lt_of_le_of_lt (Nat.zero_le _) hgood_card
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
    curve_bw_bivariate_of_many_close M e deg domain u good hM hd hradius hgood_card hclose
  let quot_x : F → F[X] := fun z =>
    if hz : z ∈ good then
      Classical.choose (curve_rs_nearby_polynomial hd (hclose z hz))
    else 0
  let quot_y : F → F[X] := fun x =>
    curvePolynomial u (Function.invFun domain x)
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
      (curve_rs_nearby_polynomial hd (hclose z hz_good))
    have hPz :
        Pz.natDegree < deg ∧
          hammingDist (curveWord u z) (Pz.eval ∘ domain) ≤ e := by
      simpa [Pz] using
        (Classical.choose_spec
          (curve_rs_nearby_polynomial hd (hclose z hz_good)))
    have hquot_def : quot_x z = Pz := by
      simp [quot_x, hz_good, Pz]
    refine ⟨?_, ?_⟩
    · have hPz_le : Pz.natDegree ≤ deg - 1 := Nat.le_pred_of_lt hPz.1
      have harith : deg - 1 ≤ (e + deg - 1) - e := by omega
      exact le_trans (by simpa [hquot_def] using hPz_le) harith
    · let Dz : F[X] := Polynomial.Bivariate.evalY z B - Pz * Polynomial.Bivariate.evalY z A
      let Tz : Finset ι := Finset.univ.filter fun i =>
        (curveWord u z) i = Pz.eval (domain i)
      have hTz_card : n-e ≤ Tz.card := by
        have hpartition := Finset.card_filter_add_card_filter_not
          (s := (Finset.univ : Finset ι))
          (p := fun i => (curveWord u z) i = Pz.eval (domain i))
        have hh : hammingDist (curveWord u z) (Pz.eval ∘ domain) =
            (Finset.univ.filter fun i => ¬ (curveWord u z) i = Pz.eval (domain i)).card := by
          simp [hammingDist]
        simp only [Finset.card_univ] at hpartition
        have hdist := hPz.2
        rw [hh] at hdist
        change Fintype.card ι-e ≤ (Finset.univ.filter fun i =>
          (curveWord u z) i = Pz.eval (domain i)).card
        omega
      have hTz_agree : ∀ i, i ∈ Tz ↔ (curveWord u z) i = Pz.eval (domain i) := by
        intro i
        simp [Tz]
      have hDz_eval :
          ∀ x ∈ Tz.image domain, Dz.eval x = 0 := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, hiTz, rfl⟩
        have hi_eq : curveWord u z i = Pz.eval (domain i) := by
          simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using (hTz_agree i).1 hiTz
        have hEq_eval :
            (Polynomial.Bivariate.evalY z B).eval (domain i) =
              (Pz * Polynomial.Bivariate.evalY z A).eval (domain i) := by
          calc
            (Polynomial.Bivariate.evalY z B).eval (domain i)
                = (Polynomial.Bivariate.evalX (domain i) B).eval z := by
                    symm
                    exact evalX_eval_eq_evalY_eval (domain i) z B
            _ = (((curvePolynomial u i) *
                  Polynomial.Bivariate.evalX (domain i) A)).eval z := by
                  simpa using congrArg (fun p : F[X] => p.eval z) (hAB i)
            _ = (curvePolynomial u i).eval z *
                  (Polynomial.Bivariate.evalX (domain i) A).eval z := by
                    rw [Polynomial.eval_mul]
            _ = (curveWord u z i) * (Polynomial.Bivariate.evalX (domain i) A).eval z := by
                  rw [curvePolynomial_eval]
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
        (quot_y x).natDegree ≤ M*(e + 1) - M*e ∧
          Polynomial.Bivariate.evalX x B = (quot_y x) * (Polynomial.Bivariate.evalX x A) := by
    intro x hx
    rcases Finset.mem_map.mp hx with ⟨i, -, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [quot_y, Function.leftInverse_invFun domain.injective i, Nat.mul_add] using
        curvePolynomial_natDegree u i
    · simpa [quot_y, Function.leftInverse_invFun domain.injective i] using hAB i
  have h_le_1 :
      1 > (((e+deg-1 : ℕ) : ℚ) / (n : ℚ) +
        ((M*(e+1) : ℕ) : ℚ) / (good.card : ℚ)) := by
    have hnq : (0 : ℚ) < n := by exact_mod_cast hn_pos
    have hgq : (0 : ℚ) < good.card := by exact_mod_cast hgood_pos
    have hng : (M : ℚ) * (n : ℚ) < (good.card : ℚ) := by
      exact_mod_cast hgood_card
    have hfrac : ((M*(e+1) : ℕ) : ℚ) / (good.card : ℚ) <
        ((e+1 : ℕ) : ℚ) / (n : ℚ) := by
      apply (div_lt_div_iff₀ hgq hnq).2
      have hmul := mul_lt_mul_of_pos_right hng (show (0 : ℚ) < (e+1 : ℕ) by positivity)
      push_cast at hmul ⊢
      nlinarith
    have hsum : (((e+deg-1 : ℕ) : ℚ) / (n : ℚ) +
        ((e+1 : ℕ) : ℚ) / (n : ℚ)) = ((2*e+deg : ℕ) : ℚ) / (n : ℚ) := by
      rw [← add_div]
      congr 1
      exact_mod_cast (show (e+deg-1)+(e+1)=2*e+deg by omega)
    have hle : ((2*e+deg : ℕ) : ℚ) / (n : ℚ) ≤ 1 := by
      apply (div_le_one hnq).2
      exact_mod_cast hradius
    have hstrict : (((e+deg-1 : ℕ) : ℚ) / (n : ℚ) +
        ((M*(e+1) : ℕ) : ℚ) / (good.card : ℚ)) <
        (((e+deg-1 : ℕ) : ℚ) / (n : ℚ) + ((e+1 : ℕ) : ℚ) / (n : ℚ)) := by linarith
    exact lt_of_lt_of_le hstrict (hsum.symm ▸ hle)
  obtain ⟨P, hBA, hP_degX, hP_degY, ⟨Q_x, hQx_card, hQx_sub, hQx_eval⟩, _⟩ :=
    polishchuk_spielman
      (a_x := e) (a_y := M*e) (b_x := e + deg - 1) (b_y := M*(e + 1))
      (n_x := ⟨n, hn_pos⟩) (n_y := ⟨good.card, hgood_pos⟩)
      (h_bx_ge_ax := by omega) (h_by_ge_ay := Nat.mul_le_mul_left M (by omega))
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
  refine ⟨(P.coeff j.val).eval ∘ domain, hv_mem j.val, ?_⟩
  intro i hi
  have hiQ : domain i ∈ Q_x := Finset.mem_preimage.mp hi
  have hEval := hQx_eval _ hiQ
  have hcoeff := congrArg (fun p : F[X] => p.coeff j.val) hEval
  have heq : (P.coeff j.val).eval (domain i) = u j i := by
    simpa [Polynomial.Bivariate.evalX_eq_map, quot_y,
      Function.leftInverse_invFun domain.injective i, curvePolynomial_coeff] using hcoeff
  exact heq.symm

end Minidregg.Selvage


/-- info: '_private.Selvage.CurveFullUDCore.0.Minidregg.Selvage.curve_rs_nearby_polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.curve_rs_nearby_polynomial

/-- info: 'Minidregg.Selvage.curveFullUDCardCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Minidregg.Selvage.curveFullUDCardCore

