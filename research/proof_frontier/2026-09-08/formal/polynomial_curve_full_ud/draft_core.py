from pathlib import Path
s=Path('research/proof_frontier/2026-09-08/formal/full_ud/src/Selvage/FullUDCore.lean').read_text().split('/-- info:')[0]
s=s.replace('import Selvage.FullUDBivariate','import Selvage.CurveFullUDBivariate').replace('rs_nearby_polynomial','curve_rs_nearby_polynomial')
s=s.replace('theorem fullUDCardCore (domain : ι ↪ F) (deg e : ℕ)', 'theorem curveFullUDCardCore (M : ℕ) (domain : ι ↪ F) (deg e : ℕ)\n    (hM : 1 ≤ M)').replace('    FullUDCardCore domain deg e := by', '    CurveFullUDCardCore M domain deg e := by')
s=s.replace('have hgood_pos : 0 < good.card := lt_trans hn_pos hgood_card', 'have hgood_pos : 0 < good.card := lt_of_le_of_lt (Nat.zero_le _) hgood_card')
s=s.replace('bw_bivariate_of_many_close e deg domain u good hd','curve_bw_bivariate_of_many_close M e deg domain u good hM hd')
s=s.replace('    Polynomial.C (u 0 (Function.invFun domain x)) +\n      Polynomial.X * Polynomial.C (u 1 (Function.invFun domain x))', '    curvePolynomial u (Function.invFun domain x)')
s=s.replace('(u 0 + z • u 1)', '(curveWord u z)').replace('u 0 i + z * u 1 i', 'curveWord u z i')
s=s.replace('(Polynomial.C (u 0 i) + Polynomial.X * Polynomial.C (u 1 i))','(curvePolynomial u i)')
start=s.index('            _ = ((Polynomial.C (u 0 i)).eval z')
end=s.index('            _ = Pz.eval (domain i)',start)
s=s[:start]+'''            _ = (curveWord u z i) * (Polynomial.Bivariate.evalX (domain i) A).eval z := by
                  rw [curvePolynomial_eval]
'''+s[end:]
s=s.replace('(quot_y x).natDegree ≤ (e + 1) - e','(quot_y x).natDegree ≤ M*(e + 1) - M*e')
start=s.index('    · have hconst :')
end=s.index('    · simpa [quot_y, Function.leftInverse_invFun',start)
s=s[:start]+'''    · simpa [quot_y, Function.leftInverse_invFun domain.injective i, Nat.mul_add] using
        curvePolynomial_natDegree u i
'''+s[end:]
start=s.index('  have h_le_1 :')
end=s.index('  obtain ⟨P, hBA',start)
s=s[:start]+'''  have h_le_1 :
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
    exact lt_of_lt_of_le (add_lt_add_left hfrac _)
      (hsum.symm ▸ hle)
'''+s[end:]
s=s.replace('(a_x := e) (a_y := e) (b_x := e + deg - 1) (b_y := e + 1)', '(a_x := e) (a_y := M*e) (b_x := e + deg - 1) (b_y := M*(e + 1))').replace('(h_by_ge_ay := by omega)', '(h_by_ge_ay := Nat.mul_le_mul_left M (by omega))')
start=s.index('  intro j\n  fin_cases j')
s=s[:start]+'''  intro j
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
'''
Path('/tmp/minidregg-polynomial-curve-full-ud-20260908/Selvage/CurveFullUDCore.lean').write_text(s)
