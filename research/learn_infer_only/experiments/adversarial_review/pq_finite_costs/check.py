#!/usr/bin/env python3
"""Independent public arithmetic checks; no author-module/estimator imports."""
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import hashlib
import json
import math

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[4]
COST = ROOT / 'research/learn_infer_only/experiments/private_construction/public_setup_pq/costs'
BOUND = ROOT / 'research/learn_infer_only/experiments/adversarial_review/public_setup_pq/quantitative_regularity'
hashes = {}


def read(path):
    path = Path(path)
    assert '.private' not in path.parts
    data = path.read_bytes()
    hashes[str(path)] = hashlib.sha256(data).hexdigest()
    return data


def doc(path):
    return json.loads(read(path))


def bits(x):
    return (x-1).bit_length()


def ceiling_sqrt(x):
    assert x > 0
    guess = 1 << ((x.bit_length()+1)//2)
    while True:
        next_guess = (guess+x//guess)//2
        if next_guess >= guess:
            return guess + (guess*guess < x)
        guess = next_guess


def divisor(x):
    if x < 2:
        return 1
    for d in range(2, math.isqrt(x)+1):
        if x % d == 0:
            return d
    return None


def determinant(matrix):
    a = [[Fraction(x) for x in row] for row in matrix]
    result = Fraction(1)
    for i in range(len(a)):
        pivot_row = next(j for j in range(i, len(a)) if a[j][i])
        if pivot_row != i:
            a[i], a[pivot_row] = a[pivot_row], a[i]
            result = -result
        pivot = a[i][i]
        result *= pivot
        for j in range(i+1, len(a)):
            factor = a[j][i]/pivot
            for k in range(i, len(a)):
                a[j][k] -= factor*a[i][k]
    assert result.denominator == 1
    return int(result)


def choose_t(count, width_exponent=0, prefactor=3):
    need = bits(prefactor*count)+66+width_exponent
    t = 1
    while 4*t*t < need:
        t += 1
    return t


def norms(M, s1, s2, t):
    l1 = M*t*(s1+s2)+1
    l2 = ceiling_sqrt(M*(t*s1)**2+M*(t*s2)**2+2*t*s2+1)
    return l1, l2


def profile_check(row):
    n,d,r,W,T,p,m,M = (row[k] for k in ['n','d','r','W','T','p','m','M'])
    q = p**row['k']; qb = bits(q)
    s1,s2,xi,se = (1 << row[k] for k in ['sigma1_pow2','sigma2_pow2','xi_pow2','encryption_error_width_pow2'])
    assert m == 2*M and row['source_LWE_secret_dimension'] == n-d and qb == row['q_bits']
    assert row['base_LWE_error_width_pow2'] == row['encryption_error_width_pow2']-1-row['xi_pow2']
    assert se == 2*xi*(1 << row['base_LWE_error_width_pow2'])
    assert m >= 4*(n+1)*qb
    assert s1*s1 >= M*n*bits(M) and M >= n*bits(s1*n)
    assert s2*s2 >= n**5*M*s1**4*bits(M*s1)**3
    assert xi*xi >= n*M*s2*s2 and se*se >= 4*xi*xi*n
    tz, te = choose_t(d*m,row['sigma2_pow2']), choose_t(T*(m+d),row['encryption_error_width_pow2'])
    assert (tz,te) == (row['key_tail_t'],row['error_tail_t'])
    l1,l2 = norms(M,s1,s2,tz); error = te*se*(1+l1)
    assert q > 2*p*W*error
    if row['label'].startswith('full_source'):
        K2 = d**d*p**(2*d)
        need_s1_sq = n*bits(m)*max(m,K2)
        assert (s1//2)**2 < need_s1_sq <= s1*s1
        source_s2_sq = n**7*m*max(m,K2)**2*bits(m)**5
        gadget_s2_sq = n**5*M*s1**4*bits(M*s1)**3
        for name, need in [('displayed_source_sigma2_rounded_pow2',source_s2_sq),('Lemma4_sigma2_floor_rounded_pow2',gadget_s2_sq)]:
            width = 1 << row[name]
            assert (width//2)**2 < need <= width*width
        assert (s2//2)**2 < max(source_s2_sq,gadget_s2_sq) <= s2*s2
        minimum_q = max(2*p*W*error+1, se*d*d*p**3*l2*bits(n)+1)
        assert q//p < minimum_q <= q
    else:
        assert q//p < n**30 <= q and s1 == n*n
        assert se*n**15 >= q and (se//2)*n**15 < q
    for N in [n,n+1]:
        assert M >= N*qb+161 and s1*s1 >= bits(M)+162
    costs = row['costs']; ct = ((m+d)*qb+7)//8
    left_bits, right_bits = bits(2*tz*s1+1), bits(2*(tz*s2+1)+1)
    key = (M*(left_bits+right_bits)+7)//8
    expected = {
        'ciphertext_residues':m+d, 'ciphertext_bitpacked_bytes':ct,
        'ciphertext_byte_aligned_coefficient_bytes':(m+d)*((qb+7)//8),
        'public_AU_bitpacked_bytes':(n*(m+d)*qb+7)//8,
        'A_only_bitpacked_bytes':(n*m*qb+7)//8, 'U_only_bitpacked_bytes':(n*d*qb+7)//8,
        'recipient_key_high_probability_bitpacked_bytes_each':key,
        'all_recipient_keys_high_probability_bitpacked_bytes':r*key,
        'recipient_key_left_bits':left_bits, 'recipient_key_right_bits':right_bits,
        'live_two_routes_W_plus_acc_ciphertexts':2*(W+1),
        'live_two_routes_W_plus_acc_bytes':2*(W+1)*ct,
        'all_T_fresh_ciphertexts_bytes':T*ct,
        'encode_dense_modq_multiplications':n*(m+d),
        'encode_dense_modq_additions_before_noise':(n-1)*(m+d),
        'encode_Gaussian_samples':m+d,
        'recipient_setup_modq_multiplications_each':n*m,
        'all_recipients_setup_modq_multiplications':r*n*m,
        'read_one_coordinate_modq_multiplications':m,
        'read_one_coordinate_modq_additions':m,
        'learn_with_expiry_modq_add_subtractions':2*(m+d),
        'all_T_encodes_dense_modq_multiplications':T*n*(m+d),
        'public_uniform_residue_draws':n*m+(d-r)*n,
    }
    assert costs == expected
    # Source-backed optional improvements; original parameters remain fixed.
    tnew = choose_t(d*m, prefactor=2)
    tphase = choose_t(T*r, prefactor=2)
    _,l2new = norms(M,s1,s2,tnew)
    improved_error = se*ceiling_sqrt(1+l2new*l2new)*tphase
    assert improved_error < error and q > 2*p*W*improved_error
    reduced_m = 4*(n+1)*qb; reduced_M = reduced_m//2
    assert reduced_M >= n*bits(s1*n) and reduced_M >= (n+1)*qb+161
    assert s1*s1 >= reduced_M*n*bits(reduced_M)
    assert s2*s2 >= n**5*reduced_M*s1**4*bits(reduced_M*s1)**3
    assert xi*xi >= n*reduced_M*s2*s2
    return {'label':row['label'],'n':n,'cost_fields_verified':len(expected),
            'original_tz_te':[tz,te], 'new_tz_tphase':[tnew,tphase],
            'improved_E_is_at_least_this_factor_smaller':error//improved_error,
            'old_E_log2':math.log2(error),'improved_E_log2':math.log2(improved_error),
            'old_m':m,'unrounded_even_m':reduced_m,
            'm_reduction_fraction':str(Fraction(m-reduced_m,m)),
            'unrounded_ciphertext_bytes':((reduced_m+d)*qb+7)//8,
            'regularity_numerators_j0_jr':[8*(d-r)+8*T*d,8*(d-r)+8*T*(d-r)]}


def rank_control():
    results = []
    for p in [2,3]:
        for M in [2,3]:
            vectors = list(product(range(p),repeat=M)); bad = 0
            for a,b in product(vectors,repeat=2):
                span = {tuple(x*v % p for v in a) for x in range(p)}
                bad += (not any(a) or b in span)
            actual = Fraction(bad,p**(2*M))
            formula = 1-(1-Fraction(1,p**M))*(1-Fraction(p,p**M))
            assert actual == formula
            results.append({'p':p,'M':M,'N':2,'matrices':p**(2*M),'rank_failure':str(actual)})
    return results


def main():
    expected = {'FEASIBILITY.md':'037b1b7995dbaec14cc983c7aea639496d1aeeed164f2a207ce3207c3a70372c',
                'BOUND.md':'b07d7714ca6078a63bf1281ad8edbd07dc39094d91f6808e1c3868a3503dc2e5'}
    for directory,name in [(COST,'FEASIBILITY.md'),(BOUND,'BOUND.md')]:
        assert hashlib.sha256(read(directory/name)).hexdigest() == expected[name]
    cost_manifest, bound_manifest = doc(COST/'COST_MANIFEST.json'), doc(BOUND/'MANIFEST.json')
    for name,h in cost_manifest['artifact_sha256'].items():
        assert hashlib.sha256(read(COST/name)).hexdigest() == h
    for entry in bound_manifest['artifacts']:
        raw = read(BOUND/entry['path'])
        assert len(raw) == entry['bytes'] and hashlib.sha256(raw).hexdigest() == entry['sha256']
    for path,h in cost_manifest['additional_sources_sha256'].items():
        assert hashlib.sha256(read(path)).hexdigest() == h
    for entry in bound_manifest['source_pins']:
        assert hashlib.sha256(read(entry['path'])).hexdigest() == entry['sha256']
    data = doc(COST/'results.json'); inputs = doc(BOUND/'INPUTS.json')
    bounded = doc(BOUND/'RESULTS.json')
    assert inputs['kappa'] == 160
    for path,h in data['read_source_sha256'].items():
        assert hashlib.sha256(read(path)).hexdigest() == h
    assert hashes[inputs['source']] == inputs['source_sha256']
    for small,full in zip(inputs['profiles'],data['profiles']):
        assert all(full[k] == v for k,v in small.items())
    rows = doc(COST.parent.parent/'designated_span/crypto/rows.json')
    assert len(rows) == 16 and all(len(row) == 577 for row in rows)
    norms_l1 = [sum(abs(x) for x in row) for row in rows]
    fixture = data['fixture']; bound = 32*127*max(norms_l1); p = fixture['smallest_prime_gt_2_bound']
    assert norms_l1 == fixture['row_L1_norms'] and bound == fixture['max_abs_score']
    assert fixture['score_bounds'] == [32*127*v for v in norms_l1]
    assert divisor(p) is None and all(divisor(x) for x in range(2*bound+1,p))
    det = determinant([row[:16] for row in rows])
    assert det == fixture['pivot_determinant'] and det % p == fixture['pivot_determinant_mod_p']
    assert fixture['basis_nonzero_products'] == sum(x != 0 for row in rows for x in row)
    assert fixture['basis_nonunit_products'] == sum(abs(x)>1 for row in rows for x in row)
    assert fixture['basis_additions_skipping_zeros'] == sum(sum(x!=0 for x in row)-1 for row in rows)
    profiles = [profile_check(row) for row in data['profiles']]
    for saved,source in zip(bounded['profiles'],data['profiles']):
        for label,N in [('setup_certificate',source['n']),('augmented_certificate',source['n']+1)]:
            certificate = saved[label]; required = N*source['q_bits']+161
            assert certificate['columns'] == N and certificate['matrix_rows_required'] == required
            assert certificate['matrix_row_margin'] == source['M']-required
            assert certificate['sigma_squared_required'] == bits(source['M'])+162
    assert all(row['regularity_numerators_j0_jr'] == [1777032,1727880] for row in profiles)
    assert Fraction(1777032,2**160) < Fraction(1,2**139)
    result = {'claim_kind':'EXECUTED','scope':'Independent exact public arithmetic and source hashes; no estimator, cryptographic implementation, private files or Gaussian sampling',
              'fixture':{'p':p,'determinant':det,'max_score':bound},
              'profiles':profiles,'rank_failure_controls':rank_control(),
              'source_and_author_hashes':hashes,
              'improvement_scope':'Conditional finite correctness bounds and arithmetic sizing only; source constants and total QPT security remain uncertified'}
    (BASE/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['fixture','profiles','rank_failure_controls']},indent=2))


if __name__ == '__main__':
    main()
