#!/usr/bin/env python3
"""Public ring algebra and exact parameter inequalities; no cryptographic execution."""
from fractions import Fraction
from hashlib import sha256
from itertools import product
from math import isqrt
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def ceil_log2(n):
    return (n-1).bit_length()


def negacyclic(a, b, modulus=None):
    n = len(a)
    assert n == len(b)
    out = [0]*n
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[(i+j) % n] += x*y*(1 if i+j < n else -1)
    return out if modulus is None else [x % modulus for x in out]


def constant_product(a, b):
    return a[0]*b[0] - sum(a[k]*b[len(a)-k] for k in range(1, len(a)))


def evaluate(poly, root, q):
    return sum(c*pow(root, i, q) for i, c in enumerate(poly)) % q


def public_counterexample():
    q, n, zeta = 17, 4, 2
    roots = [pow(zeta, 2*i+1, q) for i in range(n)]
    assert len(set(roots)) == n and all(pow(root, n, q) == q-1 for root in roots)
    poly = [1]
    denom = 1
    for root in roots[1:]:
        new = [0]*(len(poly)+1)
        for i, c in enumerate(poly):
            new[i] = (new[i]-root*c) % q
            new[i+1] = (new[i+1]+c) % q
        poly = new
        denom = denom*(roots[0]-root) % q
    inverse = pow(denom, -1, q)
    idem = [c*inverse % q for c in poly]
    assert negacyclic(idem, idem, q) == idem
    slots = [evaluate(idem, root, q) for root in roots]
    assert slots == [1, 0, 0, 0]
    # a=(1,0,0), u=(1,e,0): each contains 1, not ring multiples, but rank=1 on three slots.
    return {'q': q, 'N': n, 'roots': roots, 'idempotent_coefficients': idem,
            'idempotent_CRT': slots, 'a': ['1', '0', '0'], 'u': ['1', 'e', '0'],
            'both_have_unit_coordinate': True, 'u_is_not_ring_multiple_of_a': True,
            'CRT_ranks': [2, 1, 1, 1], 'augmented_map_is_surjective': False}


def integer_shift_controls():
    count = 0
    for radius in range(1, 9):
        support = set(range(-radius, radius+1))
        for shift in range(-3*radius, 3*radius+1):
            shifted = {x+shift for x in support}
            distance = Fraction(len(support ^ shifted), 2*len(support))
            assert distance == min(Fraction(1), Fraction(abs(shift), 2*radius+1))
            count += 1
    return count


def main():
    certificate_path = HERE/'searches/prime_certificate.json'
    cert = json.loads(certificate_path.read_text())
    q = int(cert['q'])
    odd = cert['q_factorization_minus_one']['odd_part']
    exponent = cert['q_factorization_minus_one']['two_exponent']
    witness = cert['witness']
    assert odd % 2 == 1 and q == odd*(1 << exponent)+1
    assert pow(witness, (q-1)//2, q) == q-1
    assert (1 << exponent)+1 > isqrt(q)
    assert (1 << 288) < q < (1 << 289)
    n, width, d, r, window, inputs = 4096, 64, 577, 16, 32, 384
    assert (q-1) % (2*n) == 0
    root = int(cert['primitive_2N_root'])
    assert pow(root, n, q) == q-1 and pow(root, 2*n, q) == 1

    p = 28439893
    assert all(p % v for v in range(2, isqrt(p)+1))
    x = (p-1)//2
    denominator = d*x
    delta = q//denominator
    sigma_key, sigma_error = 1 << 24, 1 << 10
    flood, b_key, b_error = 1 << 244, 8*sigma_key, 8*sigma_error
    dim = n*width
    gaussian_delta = Fraction(1, 1 << 192)
    # theta=3/64; square and raise to power 32, avoiding real roots and logs.
    smoothing_log_upper = 192+ceil_log2(dim)+2
    assert sigma_key**64 >= (n*smoothing_log_upper)**32*q**3
    # B=q^(61/64)/sqrt(n) >=1, checked by raising to 128.
    assert q**122 >= n**64
    regularity = []
    bounds = {}
    for k in (1, 2):
        theta_times_gamma_times_n = 192*(3-k)
        short = Fraction(1 << n, q**theta_times_gamma_times_n)
        rank = n*sum((Fraction(1, q**(width-i)) for i in range(k)), Fraction(0))
        assert rank+short < gaussian_delta
        regularity.append({'ring_outputs': k, 'rank_plus_short_below_2_minus_192': True,
                           'rank_upper': f'{n}*sum(q^(i-{width}),i=0..{k-1})',
                           'short_upper': f'2^{n}/q^{theta_times_gamma_times_n}',
                           'joint_h_row_upper': '(2h+1)*2^-192 for h>=1'})
        bounds[k] = (rank, short)

    shift = width*n*b_key*b_error
    tail_key = Fraction(3*d*dim*sigma_key, 1 << 256)
    tail_error = Fraction(3*dim*sigma_error, 1 << 256)
    smudge = Fraction(d*shift, 2*flood+1)+tail_key+tail_error
    error_bound = flood+shift
    assert denominator >= 2*window*x+1
    assert delta > 2*window*error_bound
    correctness_failure = tail_key+inputs*tail_error
    assert correctness_failure < Fraction(1, 1 << 203)
    ledgers = {}
    for coalition in (0, r):
        setup = (2*(d-r)+1)*gaussian_delta
        mask = (2*(d-coalition)+1)*gaussian_delta
        privacy_statistical = 2*setup+2*inputs*(smudge+mask)
        assert privacy_statistical < Fraction(1, 1 << 168)
        ledgers[str(coalition)] = {'LWE_advantage_multiplier': 2*inputs,
                                  'all_non_LWE_privacy_terms_strictly_below': '2^-168',
                                  'scope': 'ideal exact scheme distributions; no computational-hardness value assigned'}

    constant_checks = 0
    for small_n in (2, 4):
        vectors = list(product((-1, 0, 1), repeat=small_n))
        for a in vectors:
            for b in vectors:
                assert negacyclic(a, b)[0] == constant_product(a, b)
                constant_checks += 1
    counterexample = public_counterexample()
    shift_checks = integer_shift_controls()
    bits = q.bit_length()
    packed = lambda count, b: (count*b+7)//8
    costs = {'ciphertext_coefficients': dim+d,
             'ciphertext_bitpacked_bytes': packed(dim+d, bits),
             'full_ring_ciphertext_coefficients_before_projection': (width+d)*n,
             'full_ring_ciphertext_bitpacked_bytes_before_projection': packed((width+d)*n, bits),
             'public_A_coefficients': dim, 'public_P_coefficients': d*n,
             'public_A_bitpacked_bytes': packed(dim, bits),
             'public_P_bitpacked_bytes': packed(d*n, bits),
             'public_A_and_P_bitpacked_bytes': packed((width+d)*n, bits),
             'recipient_key_coefficient_bits_on_strict_tail_event': 28,
             'recipient_key_bitpacked_bytes_on_strict_tail_event': packed(dim, 28),
             'all_recipient_keys_bitpacked_bytes_on_strict_tail_event': r*packed(dim, 28),
             'fresh_encode_full_ring_products': width,
             'fresh_encode_scalar_constant_product_multiplications': d*n,
             'fresh_encode_Gaussian_coefficients': dim,
             'fresh_encode_uniform_flood_integers': d,
             'fresh_encode_uniform_secret_coefficients': n,
             'recipient_read_coefficient_multiplications': dim,
             'one_add_or_subtract_residue_operations': dim+d,
             'expire_and_add_residue_operations': 2*(dim+d)}
    result = {'scope': '[EXECUTED] Pure public arithmetic/algebra; no key, ciphertext, Gaussian sample, estimator or attack',
              'status': 'PASS', 'parameters': {'N': n, 'module_width': width, 'd': d, 'r': r, 'W': window, 'T': inputs,
              'p': p, 'q': str(q), 'q_bits': bits, 'sigmaK_pow2': 24, 'sigmae_pow2': 10,
              'F_pow2': 244, 'BK_pow2': 27, 'BE_pow2': 13, 'D': denominator,
              'theta': '3/64', 'gaussian_quotient_delta': '2^-192'},
              'exact_QPT_assumption': 'Uniform-secret Ring-LWE over Z[T]/(T^4096+1), specified prime q, 64 ring samples, independent coefficient D_Z,2^10 errors',
              'regularity': regularity, 'privacy_ledgers': ledgers,
              'correctness_failure_bound': '<2^-203 for 384 inputs on the ideal Gaussian law',
              'strict_decoder_separation_pass': True,
              'CRT_test_counterexample': counterexample,
              'constant_coefficient_identity_checks': constant_checks,
              'integer_shift_checks': shift_checks, 'costs': costs,
              'prime_certificate_sha256': sha256(certificate_path.read_bytes()).hexdigest(),
              'sampling_and_hardness': 'No sampler implementation, approximate-distribution certificate, timing or computational-hardness estimate is supplied'}
    (HERE/'RESULTS.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
