"""Circuit-privacy falsifiers and exact count ledger; no deployment security claim.

Run: python3 research/dark_learning_2026_11_06/scholar_privacy.py
Only N=2/8 polynomial operations; N=8192/16384 rows are integer formulas.
"""
from collections import Counter
from fractions import Fraction
from itertools import product
from pathlib import Path
import hashlib
import json
import math
import random

import bfv_ref as bfv
import he_matvec as hm


def tv(a, b):
    sa, sb = sum(a.values()), sum(b.values())
    return sum(abs(Fraction(a[x], sa) - Fraction(b[x], sb)) for x in a.keys() | b.keys()) / 2


def cube_tv(F, shift):
    return 1 - math.prod(Fraction(max(0, 2 * F + 1 - abs(x)), 2 * F + 1) for x in shift)


def cube_control():
    F, shift = 3, (1, 2)
    a = Counter(product(range(-F, F + 1), repeat=2))
    b = Counter(tuple(x + y for x, y in zip(v, shift)) for v in a)
    actual, formula = tv(a, b), cube_tv(F, shift)
    assert actual == formula == Fraction(19, 49)
    assert actual > Fraction(max(shift), 2 * F + 1)
    assert actual <= Fraction(sum(shift), 2 * F + 1)
    return dict(exact_tv=str(actual), scalar_bound_refuted=str(Fraction(2, 7)), ring_union_bound=str(Fraction(3, 7)))


def c1_support_control():
    N, q, a_pk = 2, 65537, [1009, 73]
    dist = Counter()
    for u in product((-1, 0, 1), repeat=N):
        au, _ = bfv.negacyclic_mul(a_pk, list(u))
        for e in product(range(-8, 9), repeat=N):
            dist[tuple((x + y) % q for x, y in zip(au, e))] += 1
    shift = [5000, 0]
    translated = Counter({tuple((x + y) % q for x, y in zip(v, shift)): n for v, n in dist.items()})
    actual = tv(dist, translated)
    assert actual == 1
    return dict(N=N, q=q, support=len(dist), random_coin_vectors=51**N,
                shift=shift, exact_c1_tv=str(actual), unaffected_by_c0_flood=True)


def malicious_key_control():
    """Bounded equations but attacker-chosen public a: recover chosen P exactly."""
    N, t, Q = 8, 65537, (1 << 127) - 1
    key = hm.OwnKey(N, Q, t, 100)
    s = key.sch.s
    key.pk = ([(-v) % Q for v in s], [1] + [0] * (N - 1))
    assert key.pk[0] == [(-v) % Q for v in s]  # key error zero, s ternary
    assert all(v in (-1, 0, 1) for v in s)
    variants = [
        ("symmetric_input", 32, [-32768, -20123, -7, 0, 1, 19, 9001, 32768], 1),
        ("public_key_openable_input", 1, [-32768, -20128, -32, 0, 32, 608, 8992, 32768], 32),
    ]
    results = {}
    for name, K, P, grid in variants:
        sent = ([(-K * v) % Q for v in s], [K] + [0] * (N - 1))
        assert key.sch.decrypt(sent) == [0] * N
        if K == 1:
            assert sent == key.pk  # public opening m=0,u=1,e0=e1=0
        prod = hm.ptxct(P, sent, Q)
        rng = random.Random(712)
        for _ in range(25):
            zero = key.enc_zero_pk(rng)
            M = [rng.randrange(t) for _ in range(N)]
            F = 1 << 80
            c0 = [(x + z + (2 * Q * bfv.centered(m, t) + t) // (2 * t) + rng.randint(-F, F)) % Q
                  for x, z, m in zip(prod[0], zero[0], M)]
            c1 = [(x + z) % Q for x, z in zip(prod[1], zero[1])]
            recovered = [((bfv.centered(v, Q) + K * grid // 2) // (K * grid)) * grid for v in c1]
            assert recovered == P
            assert key.sch.decrypt((c0, c1)) == M
        results[name] = dict(trials=25, every_coefficient_recovered=True, masked_decryption_correct=True,
                            input_plaintext_zero=True, public_key_opening_available=K == 1,
                            matrix_coefficient_grid=grid)
    return dict(variants=results, key_and_ciphertext_bounded_equations_hold=True,
                caveat="attacker-chosen public key polynomial; honest-key generation is not attacked")


def bound(d, N, t):
    dc, dr = hm.layout(d, N)
    # One sent coefficient's exact-scaling error <= 8 + 1/2;
    # polynomial P has at most dr*dc nonzero coefficients, each <= floor(t/2).
    # Enc_pk(0) phase <= 16*N+8; two encoding roundings cost <=1.
    Bf = ((d // dc) * dr * dc * (t // 2) * 17 + 1) // 2 + 16 * N + 9
    Bb = ((d // dr) * dr * dc * (t // 2) * 17 + 1) // 2 + 16 * N + 9
    forward_returns, backward_returns = 12 * (d // dr), 6 * (d // dc)
    weighted = N * (forward_returns * Bf + backward_returns * Bb)
    return Bf, Bb, forward_returns, backward_returns, weighted


def phase_parameter_gate(d, N, t, Q, F, steps=10**6, target_bits=40):
    """Necessary phase-budget gate, deliberately NOT a circuit-privacy certificate."""
    Bf, Bb, _, _, weighted = bound(d, N, t)
    return dict(phase_budget_ok=weighted * steps * (1 << target_bits) <= 2 * F + 1,
                decrypt_margin_ok=2 * t * (F + max(Bf, Bb) + 1) < Q)


def count_row(d, N=8192, L=3):
    t = bfv.ntt_primes(61, 4, 16384)[3]  # the deployed SPDZ prime, also for alternative N
    primes = bfv.ntt_primes(61, L, 2 * N, exclude=(t,))
    Q = math.prod(primes)
    Bf, Bb, cf, cb, weighted = bound(d, N, t)
    legacy_F = 1 << ((N * (t // 2) * 32).bit_length() + 40)
    def target(steps):
        required_F = (weighted * steps * (1 << 40)) // 2 + 1
        F = 1 << (required_F - 1).bit_length()
        return dict(steps=steps, minimum_F=required_F, power_of_two_F_bits=F.bit_length()-1,
                    log2_minimum_modulus=math.log2(2*t*(required_F+max(Bf,Bb)+1)),
                    power_of_two_choice_fits_Q=2*t*(F+max(Bf,Bb)+1)<Q,
                    gate=phase_parameter_gate(d,N,t,Q,F,steps),
                    log2_phase_budget=math.log2(Fraction(weighted*steps,2*F+1)))
    hc = hm.counts(d, N=N, L=L)
    return dict(d=d,N=N,L=L,t=t,Q_primes=primes,log2_Q=math.log2(Q),
                legacy_flood_bits=legacy_F.bit_length()-1,
                legacy_gate=phase_parameter_gate(d,N,t,Q,legacy_F),
                forward_bound=Bf,backward_bound=Bb,
                forward_returns=cf,backward_returns=cb,
                legacy_log2_phase_step_union=math.log2(Fraction(weighted,2*legacy_F+1)),
                legacy_log2_phase_million_union=math.log2(Fraction(weighted*10**6,2*legacy_F+1)),
                phase_targets=[target(1),target(10**6)],he_wire_elements=hc['he_wire'],
                ciphertexts_sent=hc['cts_sent'],ciphertexts_returned=hc['cts_returned'],
                log2_c1_support_ratio=N*(math.log2(51)-math.log2(Q)))


def main():
    here=Path(__file__).parent
    sources={name:hashlib.sha256((here/name).read_bytes()).hexdigest() for name in ('bfv_ref.py','he_matvec.py')}
    out=dict(command='python3 research/dark_learning_2026_11_06/scholar_privacy.py',
             source_sha256=sources,controls=dict(cube=cube_control(),c1_support=c1_support_control(),
             malicious_key=malicious_key_control()),
             deployed_rows=[count_row(d) for d in (64,1024,4096)],alternative=count_row(4096,16384,4),
             scope='Phase statistical budget is conditional; not a full-ciphertext statistical guarantee.')
    assert all(not row['legacy_gate']['phase_budget_ok'] for row in out['deployed_rows'])
    assert all(out['alternative']['phase_targets'][1]['gate'].values())
    print(json.dumps(out,indent=2))
    (here/'scholar_privacy_results.json').write_text(json.dumps(out,indent=2)+'\n')

if __name__=='__main__':
    main()
