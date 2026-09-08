#!/usr/bin/env python3
"""Independent exact finite controls; no prover, sampler or cryptographic execution."""
from collections import Counter
from fractions import Fraction
from itertools import product, combinations
from pathlib import Path
import hashlib, json, time

OUT = Path(__file__).resolve().parent

def ev(c, x, p):
    y = 0
    for a in reversed(c):
        y = (y*x+a) % p
    return y

def interpolate(xs, ys, x, p):
    total = 0
    for k, y in enumerate(ys):
        num, den = y, 1
        for j, v in enumerate(xs):
            if j != k:
                num = num*(x-v) % p
                den = den*(xs[k]-v) % p
        total = (total + num*pow(den, -1, p)) % p
    return total

def code_dist(word, xs, d, p):
    # Every nearest degree<d word agreeing at >=d sites is represented here.
    # The zero codeword additionally handles cases with fewer such agreements.
    best = sum(v != 0 for v in word)
    for ids in combinations(range(len(xs)), d):
        px, py = [xs[i] for i in ids], [word[i] for i in ids]
        best = min(best, sum(interpolate(px, py, x, p) != v for x,v in zip(xs,word)))
    return best

def exhaustive_constant_code(p, M, n, e):
    # Normalize the first row polynomial to zero. Subtracting it from every
    # row adds a constant codeword at every challenge and every coefficient,
    # so both distances and common agreement sets are invariant.
    coeffs = list(product(range(p), repeat=M+1))
    vals = {c: [ev(c,z,p) for z in range(p)] for c in coeffs}
    zero = (0,)*(M+1)
    stats = Counter()
    sharp = None
    max_bad = -1
    for rest in product(coeffs, repeat=n-1):
        rows = (zero,)+rest
        common = max(Counter(rows).values())
        good = [z for z in range(p) if n-max(Counter(vals[c][z] for c in rows).values()) <= e]
        stats['families'] += 1
        if len(good)>M*n:
            stats['core_premise_satisfied'] += 1
            assert common >= n-e
        if common<n-e:
            stats['not_jointly_close'] += 1
            assert len(good)<=M*n
            max_bad = max(max_bad,len(good))
            if len(good)==M*n and sharp is None:
                sharp = {'rows':rows, 'good':good, 'largest_common_set':common}
    return {'p':p,'M':M,'n':n,'d':1,'e':e, **stats,
            'max_good_without_common_agreement':max_bad,
            'strict_threshold_counterexample':sharp}

def degree_arithmetic():
    count = boundary = zero_error = 0
    for M in range(1,9):
      for n in range(1,65):
       for d in range(1,n+1):
        for e in range((n-d)//2+1):
            good = M*n+1
            ratio = Fraction(e+d-1,n)+Fraction(M*(e+1),good)
            assert M*(e+1) < good
            assert ratio < 1
            assert e+d-1 < n-e
            assert (e+d-1)-e == d-1
            assert M*(e+1)-M*e == M
            count+=1
            if e==0: zero_error+=1
            if 2*e+d==n:
                boundary+=1
                assert Fraction(e+d-1,n)+Fraction(M*(e+1),M*n)==1
    return {'cases':count,'integer_radius_boundary_cases':boundary,
            'e_zero_cases':zero_error,'M_range':[1,8],'n_range':[1,64],
            'good_challenges_tested':'M*n+1, the largest PS ratio among admissible integer cardinalities',
            'at_Mn_boundary_PS_ratio':'exactly 1 when 2e+d=n; strict PS premise fails'}

def multiply(a,b,p):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]=(c[i+j]+x*y)%p
    return c

def higher_degree_controls():
    result=[]
    for M in (7,8):
        p=101
        coeff=[1]
        for r in range(M): coeff=multiply(coeff,[-r%p,1],p)
        rows=[tuple(0 for _ in coeff),tuple(coeff)]
        good=[z for z in range(p) if ev(coeff,z,p)==0]
        assert good==list(range(M))
        assert len(set(rows))==2 # n2,d1,e0: joint agreement would require equal rows.
        assert Fraction(M,p)>Fraction(2,p)
        assert Fraction(M,p)<=Fraction(2*M,p)
        result.append({'p':p,'M':M,'n':2,'d':1,'delta':'1/5','integer_error':0,
          'row_polynomial':coeff,'good':good,'probability':str(Fraction(M,p)),
          'curve_bound':str(Fraction(2*M,p)), 'false_affine_bound':str(Fraction(2,p))})
    # A post-challenge injected row can cancel every nonzero challenge.
    p=101
    dynamic_good=[]
    for z in range(p):
        injected = 0 if z==0 else -pow(pow(z,8,p),-1,p)%p
        if (1+pow(z,8,p)*injected)%p == 0: dynamic_good.append(z)
    assert len(dynamic_good)==100 and Fraction(100,101)>Fraction(16,101)
    return {'M7_M8':result,'post_challenge_g_refusal':{
      'p':101,'n':2,'M':8,'u':'u_0=(0,1); u_1..u_7=0',
      'g_beta':'(0,-beta^-8) for beta!=0; (0,0) otherwise',
      'good_count':100,'forbidden_claim_bound':'16/101',
      'actual_probability':'100/101'}}

def witness_controls():
    p=101; xs=list(range(5)); results=[]
    for M in range(1,9):
        legal=[[ (j+x)%p for x in xs] for j in range(M+1)]
        corrupted=[[ (v+(i==0))%p for i,v in enumerate(w)] for w in legal]
        assert all(code_dist(w,xs,2,p)==1 for w in corrupted)
        assert all(code_dist(w,xs,2,p)==0 for w in legal)
        distances=[]
        for z in range(p):
            w=[sum(pow(z,j,p)*corrupted[j][i] for j in range(M+1))%p for i in range(5)]
            distances.append(code_dist(w,xs,2,p))
        assert max(distances)==1
        assert all(v<=1 for v in distances)
        assert M*5<101
        # Four unchanged positions simultaneously work for every coefficient.
        assert all(w[1:]==v[1:] for w,v in zip(corrupted,legal))
        # Explicit legal e0 application uses same actual coefficients/domain.
        zero_error_good=sum(all(code_dist([sum(pow(z,j,p)*legal[j][i] for j in range(M+1))%p
                  for i in range(5)],xs,2,p)==0 for _ in [0]) for z in range(p))
        assert zero_error_good==101
        results.append({'M':M,'positive_radius_good':101,
          'corrupted_coefficient_distances':[1]*(M+1),
          'curve_distance_histogram':dict(sorted(Counter(distances).items())),
          'common_agreement_size':4,'e_zero_good':zero_error_good})
    return results

def main():
    start=time.monotonic()
    results={'scope':'Exact public finite field and integer/Fraction mathematics only; not Lean kernel evidence or Rust execution.',
       'degree_arithmetic':degree_arithmetic(),
       'exhaustive_curves':[exhaustive_constant_code(5,1,3,1),
                            exhaustive_constant_code(7,2,3,1),
                            exhaustive_constant_code(7,2,2,0)],
       'higher_degree_controls':higher_degree_controls(),
       'source_witness_controls':witness_controls()}
    assert results['exhaustive_curves'][0]['strict_threshold_counterexample'] is not None
    results['script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    results['elapsed_seconds']=time.monotonic()-start
    results['status']='PASS'
    (OUT/'FINITE_RESULTS.json').write_text(json.dumps(results,indent=2)+'\n')
    print(json.dumps({'status':'PASS','degree_cases':results['degree_arithmetic']['cases'],
          'exhaustive_families':sum(x['families'] for x in results['exhaustive_curves']),
          'elapsed_seconds':results['elapsed_seconds']},sort_keys=True))
if __name__=='__main__': main()
