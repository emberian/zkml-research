#!/usr/bin/env python3
"""Public integer accounting only. No keys, ciphertexts, Gaussian samples or attacks."""
import hashlib
import json
import math
from pathlib import Path

HERE = Path(__file__).resolve().parent
PRIVATE = HERE.parent.parent
ROWS = PRIVATE / 'designated_span/crypto/rows.json'
REPORT = PRIVATE / 'designated_span/full_utility/reports/full_003/report.json'
PAPER = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror/2015/608.pdf')
TAIL_BITS = 66
REG_BITS = 160

def cl2(x):
    assert x > 0
    return (x - 1).bit_length()

def csqrt(x):
    s = math.isqrt(x)
    return s + (s*s < x)

def pow2up(x):
    return 1 << cl2(x)

def prime(x):
    if x < 2:
        return False
    if x % 2 == 0:
        return x == 2
    return all(x % t for t in range(3, math.isqrt(x) + 1, 2))

def nextprime(x):
    x += 1
    while not prime(x):
        x += 1
    return x

def determinant(a):
    a = [r[:] for r in a]
    prev = sign = 1
    for k in range(len(a)-1):
        if a[k][k] == 0:
            j = next(j for j in range(k+1, len(a)) if a[j][k])
            a[k], a[j] = a[j], a[k]
            sign *= -1
        pivot = a[k][k]
        for i in range(k+1, len(a)):
            for j in range(k+1, len(a)):
                num = a[i][j]*pivot - a[i][k]*a[k][j]
                assert num % prev == 0
                a[i][j] = num // prev
        for i in range(k+1, len(a)):
            a[i][k] = 0
        prev = pivot
    return sign * a[-1][-1]

def primepower_atleast(p, target):
    k = max(1, math.ceil(math.log2(target)/math.log2(p)))
    q = p**k
    while q < target:
        k += 1
        q *= p
    while k > 1 and q//p >= target:
        k -= 1
        q //= p
    return k, q

def tail_t(sigma, count):
    # sigma is a power of two. 3*N*sigma*exp(-pi*t*t) <= 2^-TAIL_BITS
    # follows from pi > 4 ln 2 and the integer inequality checked here.
    a = cl2(sigma) + cl2(3*count) + TAIL_BITS
    t = max(1, csqrt((a+3)//4))
    assert 4*t*t >= a
    return t

def tail_bounds(m, d, T, s1, s2, se):
    M = m//2
    tz = tail_t(s2, d*m)
    te = tail_t(se, T*(m+d))
    L1 = M*tz*(s1+s2)+1
    L2 = csqrt(M*(tz*s1)**2 + M*(tz*s2)**2 + 2*tz*s2+1)
    E = te*se*(1+L1)
    return tz, te, L1, L2, E

def regularity_checks(n, M, q, p, s1):
    checks = []
    for N in [n, n+1]:
        items = {
            'lemma6_first_sufficient': M >= N+2*REG_BITS+3,
            'lemma6_second_sufficient': M >= N*cl2(q)+2*REG_BITS+2,
            'full_rank_sufficient': M >= 2*N*cl2(p),
            'smoothing_width_sufficient': s1*s1 >= cl2(M)+2*REG_BITS+3,
            'rank_error_at_most_2_minus_kappa': N >= REG_BITS,
        }
        checks.append({'columns':N, **items})
        assert all(items.values())
    return checks

def details(label, n, d, r, W, T, p, m, q, k, s1, s2, xi, se, extra):
    M = m//2
    tz, te, L1, L2, E = tail_bounds(m,d,T,s1,s2,se)
    good = q > 2*p*W*E
    assert good
    normalized_checks = {
        'sigma1_Lemma4_C1_equals_1': s1*s1 >= M*n*cl2(M),
        'M_Lemma4_C2_equals_1': M >= n*cl2(s1*n),
        'sigma2_Lemma4_C3_equals_1': s2*s2 >= n**5*M*s1**4*cl2(M*s1)**3,
        'xi_Lemma5_C4_equals_1': xi*xi >= n*M*s2*s2,
        'base_error_C5_equals_1': se*se >= 4*xi*xi*n,
    }
    assert all(normalized_checks.values()), normalized_checks
    qb = cl2(q)
    coord = m+d
    packed = lambda count,bits: (count*bits+7)//8
    key_left_bits = cl2(2*tz*s1+1)
    key_right_bits = cl2(2*(tz*s2+1)+1)
    ct = packed(coord,qb)
    rkey = (M*(key_left_bits+key_right_bits)+7)//8
    cost = {
        'ciphertext_residues':coord,
        'ciphertext_bitpacked_bytes':ct,
        'ciphertext_byte_aligned_coefficient_bytes':coord*((qb+7)//8),
        'public_AU_bitpacked_bytes':packed(n*coord,qb),
        'A_only_bitpacked_bytes':packed(n*m,qb),
        'U_only_bitpacked_bytes':packed(n*d,qb),
        'recipient_key_high_probability_bitpacked_bytes_each':rkey,
        'all_recipient_keys_high_probability_bitpacked_bytes':r*rkey,
        'recipient_key_left_bits':key_left_bits,
        'recipient_key_right_bits':key_right_bits,
        'live_two_routes_W_plus_acc_ciphertexts':2*(W+1),
        'live_two_routes_W_plus_acc_bytes':2*(W+1)*ct,
        'all_T_fresh_ciphertexts_bytes':T*ct,
        'encode_dense_modq_multiplications':n*coord,
        'encode_dense_modq_additions_before_noise':(n-1)*coord,
        'encode_Gaussian_samples':coord,
        'recipient_setup_modq_multiplications_each':n*m,
        'all_recipients_setup_modq_multiplications':r*n*m,
        'read_one_coordinate_modq_multiplications':m,
        'read_one_coordinate_modq_additions':m,
        'learn_with_expiry_modq_add_subtractions':2*coord,
        'all_T_encodes_dense_modq_multiplications':T*n*coord,
        'public_uniform_residue_draws':n*m+(d-r)*n,
    }
    factor = 2*(d-r)+2*T*d  # Worst static coalition j=0 in direct proof.
    return {
        'label':label,
        'classification':'explicit arithmetic normalization; hidden source constants uncertified; no security claim',
        'n':n,'source_LWE_secret_dimension':n-d,'d':d,'r':r,'W':W,'T':T,
        'p':p,'q_representation':f'{p}^{k}','k':k,'q_bits':qb,'m':m,'M':M,
        'sigma1_pow2':cl2(s1),'sigma2_pow2':cl2(s2),'xi_pow2':cl2(xi),
        'encryption_error_width_pow2':cl2(se),
        'base_LWE_error_width_pow2':cl2(se)-1-cl2(xi),
        'alpha_representation':f'2^{cl2(se)}/{p}^{k}',
        'beta_representation':f'2^{cl2(se)-1-cl2(xi)}/{p}^{k}',
        'tail_budget_each_2_minus':TAIL_BITS,'key_tail_t':tz,'error_tail_t':te,
        'row_L1_bound_log2_approx':math.log2(L1),
        'row_L2_bound_log2_approx':math.log2(L2),
        'single_input_E_log2_approx':math.log2(E),
        'strict_correctness_q_gt_2pWE':good,
        'correctness_slack_log2_approx':math.log2(q)-math.log2(2*p*W*E),
        'normalized_source_checks':normalized_checks,
        'finite_regularity_checks':regularity_checks(n,M,q,p,s1),
        'regularity_error_bound_each':f'3*2^-{REG_BITS}+{p}^-N <= 4*2^-{REG_BITS}',
        'setup_plus_T_augmented_error_numerator_over_2_pow160':4*factor,
        'correctness_bad_event_union_bound':'2^-66 + 2^-66 = 2^-65',
        'costs':cost, **extra,
    }

def full_source(n,d,r,W,T,p):
    K2 = d**d*p**(2*d)
    m = pow2up(4*n)
    steps = []
    for _ in range(40):
        M = m//2
        logm = cl2(m)
        s1 = pow2up(csqrt(n*logm*max(m,K2)))
        source_s2 = csqrt(n**7*m*max(m,K2)**2*logm**5)
        lemma_s2 = csqrt(n**5*M*s1**4*cl2(M*s1)**3)
        s2 = pow2up(max(source_s2,lemma_s2))
        xi = pow2up(csqrt(n*M*s2*s2))
        se = 2*xi*pow2up(csqrt(n))
        tz, te, L1, L2, E = tail_bounds(m,d,T,s1,s2,se)
        qmin = max(2*p*W*E+1,se*d*d*p**3*L2*cl2(n)+1)
        k,q = primepower_atleast(p,qmin)
        next_m = pow2up(max(m,4*(n+1)*cl2(q),2*n*cl2(s1*n)))
        steps.append({'m':m,'q_bits':cl2(q),'next_m':next_m})
        if next_m == m:
            break
        m = next_m
    else:
        raise AssertionError('fixed-point iteration failed')
    assert q > se*d*d*p**3*L2*cl2(n)
    assert se >= cl2(n)
    return details('full_source_prescription_normalized',n,d,r,W,T,p,m,q,k,s1,s2,xi,se,{
        'K_prime_log2_approx':math.log2(K2)/2,
        'K_prime_squared_bits':cl2(K2),
        'extra_source_correctness_factor':'d^2*p^3*Btau*ceil_log2(n)',
        'source_sigma2_and_Lemma4_max_used':True,
        'displayed_source_sigma2_rounded_pow2':cl2(pow2up(source_s2)),
        'Lemma4_sigma2_floor_rounded_pow2':cl2(pow2up(lemma_s2)),
        'iteration_trace':steps,
    })

def polynomial_family(n,d,r,W,T,p):
    k,q = primepower_atleast(p,n**30)
    m = pow2up(4*(n+1)*cl2(q))
    M = m//2
    s1 = n**2
    s2 = pow2up(max(n**8,csqrt(n**5*M*s1**4*cl2(M*s1)**3)))
    xi = pow2up(max(n**10,csqrt(n*M*s2*s2)))
    se = pow2up((q+n**15-1)//n**15)
    return details('fixed_coordinate_polynomial_family',n,d,r,W,T,p,m,q,k,s1,s2,xi,se,{
        'family':'q=smallest p-power >= n^30; sigma1=n^2; sigma2>=n^8 and xi>=n^10 rounded up to normalized Lemma4/5 floors; alpha in [n^-15,2n^-15)',
    })

rows = json.loads(ROWS.read_text())
report = json.loads(REPORT.read_text())
d,r,W,T = len(rows[0]),len(rows),32,report['learns']
assert (d,r,W,T)==(577,16,32,384)
assert all(len(y)==d and all(type(x) is int and -127<=x<=127 for x in y) for y in rows)
norms = [sum(map(abs,y)) for y in rows]
bound = W*127*max(norms)
p = nextprime(2*bound)
det = determinant([y[:r] for y in rows])
assert det == -812032080 and det % p != 0
results = {
    'scope':'public arithmetic/size accounting only; no crypto or estimator execution',
    'fixture':{'d':d,'r':r,'W':W,'T':T,'row_L1_norms':norms,'score_bounds':[W*127*x for x in norms],
        'max_abs_score':bound,'smallest_prime_gt_2_bound':p,'primality_method':'trial division through integer square root',
        'pivot_determinant':det,'pivot_determinant_mod_p':det%p,
        'public_basis_implicit':'first16 rows Y, remaining standard rows e17 through e577',
        'basis_dense_products':d*r,'basis_nonzero_products':sum(v!=0 for y in rows for v in y),
        'basis_nonunit_products':sum(abs(v)>1 for y in rows for v in y),
        'basis_additions_skipping_zeros':sum(sum(v!=0 for v in y)-1 for y in rows),
        'basis_bottom_coordinate_copies':d-r,
        'Y_signed_8bit_bytes':d*r},
    'profiles':[full_source(1024,d,r,W,T,p),polynomial_family(1024,d,r,W,T,p),polynomial_family(4096,d,r,W,T,p)],
    'read_source_sha256':{},
}
for f in [ROWS,REPORT,PAPER,HERE.parent/'notes/AUDIT.md',Path(__file__)]:
    results['read_source_sha256'][str(f)] = hashlib.sha256(f.read_bytes()).hexdigest()
(HERE/'results.json').write_text(json.dumps(results,indent=2)+'\n')
def human_bytes(value):
    for suffix in ['B','kB','MB','GB','TB','PB','EB']:
        if value < 1000 or suffix == 'EB':
            return f'{value:.2f} {suffix}'
        value /= 1000

table = ['| Arithmetic normalization | n | q bits | m | Ciphertext | Public A,U | Recipient key* | Products/Encode |',
         '| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |']
for row in results['profiles']:
    c = row['costs']
    table.append('| '+ ' | '.join([
        row['label'],str(row['n']),str(row['q_bits']),str(row['m']),
        human_bytes(c['ciphertext_bitpacked_bytes']),human_bytes(c['public_AU_bitpacked_bytes']),
        human_bytes(c['recipient_key_high_probability_bitpacked_bytes_each']),
        f"{c['encode_dense_modq_multiplications']:,}",
    ])+' |')
(HERE/'table.md').write_text('\n'.join(table)+'\n\n*High-probability packed integer size under the stated tail event. SI decimal units.\n')
print(json.dumps(results,indent=2))
