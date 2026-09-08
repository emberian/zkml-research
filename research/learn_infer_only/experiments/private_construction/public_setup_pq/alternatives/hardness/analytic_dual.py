"""Arithmetic on dual norm/cost formulas, no lattice generation or reduction."""
import json
import math
from pathlib import Path

out=[]
for qb in [288,289]:
    n,m,sigma_bits=1024,16384,10
    delta=1.0219
    k=min(range(n+1,m+1),key=lambda k:k*math.log2(delta)+n*qb/k)
    lognorm=k*math.log2(delta)+n*qb/k
    kw=min(range(n+1,m+1),key=lambda k:(k-1)/4+n*qb/k)
    worst=(kw-1)/4+n*qb/kw
    out.append({'log2q_endpoint':qb,'n':n,'m':m,'sigma_width_exponent':sigma_bits,
                'empirical_LLL_delta':delta,'heuristic_optimal_k':k,
                'heuristic_log2_dual_norm':lognorm,
                'sufficient_norm_log2_upper':qb-sigma_bits-6,
                'margin_bits_below_sufficient_norm':qb-sigma_bits-6-lognorm,
                'modeled_log2_LLL_d3':3*math.log2(k),
                'modeled_log2_LLL_d3_B2':3*math.log2(k)+2*math.log2(qb),
                'worst_case_LLL_optimal_k':kw,'worst_case_LLL_log2_norm_bound':worst,
                'worst_case_bound_proves_sufficient_condition':worst<=qb-sigma_bits-6})
text=json.dumps({'scope':'Formula arithmetic; empirical shape is unproved, no LLL execution.',
                 'endpoint_formula_evaluations':out},indent=2)+'\n'
Path(__file__).with_name('analytic_dual.json').write_text(text)
print(text,end='')
