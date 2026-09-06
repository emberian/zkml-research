#!/usr/bin/env python3
"""Exact algebra, schedule, interval and capability experiments; NOT encryption.

Run from repository root with Python's standard library. No latency is measured.
The scalar phase toy has public test secrets and q=t*Delta; it is NOT secure BFV.
The operation ledger counts scalar arithmetic in explicitly chosen schedules,
not ciphertext instructions, packing efficiency, or GPU throughput.
"""
from __future__ import annotations

from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
from itertools import product
from pathlib import Path
import csv
import hashlib
import json
import math
import platform
import sys

HERE = Path(__file__).resolve().parent


@dataclass(frozen=True)
class Phase:
    c0: int
    c1: int
    q: int = 65536
    t: int = 256

    def add(self, other: Phase) -> Phase:
        assert (self.q, self.t) == (other.q, other.t)
        return Phase((self.c0 + other.c0) % self.q,
                     (self.c1 + other.c1) % self.q, self.q, self.t)

    def decrypt(self, secret: int) -> int:
        delta = self.q // self.t
        phase = (self.c0 + self.c1 * secret) % self.q
        return ((phase + delta // 2) // delta) % self.t


def phase(m: int, error: int, nonce: int, secret: int = 3) -> Phase:
    # This is an explicit phase-equation witness, not a cryptographic sampler.
    return Phase((256 * m + error - nonce * secret) % 65536, nonce)


def balanced_sum(xs: list[Phase]) -> Phase:
    if len(xs) == 1:
        return xs[0]
    mid = len(xs) // 2
    return balanced_sum(xs[:mid]).add(balanced_sum(xs[mid:]))


def noise_audit() -> dict:
    # Embed the scalar as entry (0,0) of a 2x2 matrix. Every update is the
    # nonzero rank-one outer product (1,0)^T (1,0). Other entries stay zero.
    base = phase(7, 1, 11)
    current = base
    fresh = []
    rows = []
    for step in range(1, 128):
        update = phase(1, 1, 11 + step)
        assert update.decrypt(3) == 1
        fresh.append(update)
        current = current.add(update)
        want = (7 + step) % 256
        got = current.decrypt(3)
        rows.append(dict(step=step, rank=1, phase_error=1 + step,
                         expected=want, observed=got, correct=(want == got)))
    assert all(row['correct'] for row in rows[:-1])
    assert not rows[-1]['correct']
    assert balanced_sum([base] + fresh) == current
    # Rerandomizing by an independently fresh encryption of zero is addition.
    rerandomized = base
    for step in range(127):
        rerandomized = rerandomized.add(phase(0, 1, step + 200))
    assert rerandomized.decrypt(3) == 8 != 7
    # Smaller errors preserve correctness for a finite addition horizon;
    # append-only storage preserves each fresh object's original phase error.
    assert all(ct.decrypt(3) == 1 for ct in fresh)
    return dict(model='insecure exact scalar phase; q=t*Delta; test secret public',
                recurrence='E_new = E_old + E_update',
                finite_positive_steps=126, first_failure=rows[-1],
                fresh_factors_still_correct=len(fresh),
                balanced_sum_equals_sequential=True,
                rerandomization_output=rerandomized.decrypt(3), rows=rows)


class Val:
    def __init__(self, value: int, private: bool, ledger: Counter):
        self.value, self.private, self.ledger = value, private, ledger

    def __add__(self, rhs: Val) -> Val:
        private = self.private or rhs.private
        self.ledger['private_add' if private else 'public_add'] += 1
        return Val(self.value + rhs.value, private, self.ledger)

    def __mul__(self, rhs: Val) -> Val:
        key = ('secret_secret_mul' if self.private and rhs.private else
               'secret_public_mul' if self.private or rhs.private else 'public_mul')
        self.ledger[key] += 1
        return Val(self.value * rhs.value, self.private or rhs.private, self.ledger)


def dot(xs: list[Val], ys: list[Val]) -> Val:
    # Explicit no-add-to-zero schedule: n products and n-1 additions.
    assert len(xs) == len(ys) and xs
    products = [a * b for a, b in zip(xs, ys)]
    acc = products[0]
    for term in products[1:]:
        acc = acc + term
    return acc


def lowrank_count(d: int, r: int, steps: int, private_x: bool) -> dict:
    # W0 x + sum_j A_j(B_j^T x); W0 public; A and B private.
    # All counts include the base, both thin matvecs, and output accumulation.
    return dict(d=d, r=r, steps=steps, private_x=private_x,
        public_mul=0 if private_x else d*d,
        secret_public_mul=d*d if private_x else steps*d*r,
        secret_secret_mul=2*steps*d*r if private_x else steps*d*r,
        public_add=0 if private_x else d*(d-1),
        private_add=(d*(d-1) if private_x else 0) +
                    steps*(r*(d-1) + d*(r-1) + d),
        private_state_scalars=2*steps*d*r,
        base_public_scalars=d*d,
        unpriced='factor generation; packing/rotations; HE rescale/relinearize; '
                 'proofs; release; ingress; refresh; authentication')


def execute_lowrank(d=4, r=2, steps=3, private_x=False) -> dict:
    counts = Counter()
    wrap = lambda n, p: Val(n, p, counts)
    x = [wrap(i-1, private_x) for i in range(d)]
    W = [[wrap((i+j)%3-1, False) for j in range(d)] for i in range(d)]
    y = [dot(row, x) for row in W]
    dense = [[v.value for v in row] for row in W]
    for step in range(steps):
        A = [[wrap((i+k+step)%3-1, True) for k in range(r)] for i in range(d)]
        B = [[wrap((j+2*k+step)%3-1, True) for k in range(r)] for j in range(d)]
        v = [dot([B[j][k] for j in range(d)], x) for k in range(r)]
        update = [dot(row, v) for row in A]
        y = [yi + zi for yi, zi in zip(y, update)]
        for i in range(d):
            for j in range(d):
                dense[i][j] += sum(A[i][k].value*B[j][k].value for k in range(r))
    expected = [sum(row[j]*x[j].value for j in range(d)) for row in dense]
    assert [yi.value for yi in y] == expected
    formula = lowrank_count(d, r, steps, private_x)
    for key in ['public_mul', 'secret_public_mul', 'secret_secret_mul',
                'public_add', 'private_add']:
        assert counts[key] == formula[key], (key, counts, formula)
    return dict(shape=[d, r, steps], private_x=private_x,
                counts=dict(counts), output=expected, formula_crosscheck=True)


def taint_audit(d=32, r=2, vocab=64) -> dict:
    # One private adapter at the start of a public dense/nonlinear/readout path.
    counts = Counter()
    wrap = lambda n, p: Val(n, p, counts)
    x = [wrap(i % 2, False) for i in range(d)]
    B = [[wrap(1, True) for _ in range(d)] for _ in range(r)]
    A = [[wrap(1, True) for _ in range(r)] for _ in range(d)]
    z = [dot(row, x) for row in B]
    h = [dot(row, z) + xi for row, xi in zip(A, x)]
    adapter_counts = dict(counts)
    dense = [dot([wrap(1, False) for _ in range(d)], h) for _ in range(d)]
    counts['private_nonlinear_activation'] += d
    activated = [wrap(max(0, v.value), v.private) for v in dense]
    logits = [dot([wrap(1, False) for _ in range(d)], activated)
              for _ in range(vocab)]
    assert all(v.private for v in logits)
    assert counts['secret_public_mul'] == d*r + d*d + vocab*d
    return dict(d=d, r=r, vocab=vocab, adapter_counts=adapter_counts,
                complete_counts=dict(counts), private_logits=vocab,
                omitted_after_adapter_secret_public_mul=d*d+vocab*d,
                unpriced='normalization, attention, private selection/sampling, '
                         'HE lowering, exact activation, proofs, release')


def ema(state: tuple[int, ...], observation: tuple[int, ...]) -> tuple[int, ...]:
    assert len(state) == len(observation)
    assert all(-127 <= x <= 127 for x in state + observation)
    return tuple((7*w + u)//8 for w, u in zip(state, observation))


def learner_audit() -> dict:
    # Private coefficients over any declared fixed public feature map.
    # This is exponentially weighted adaptation, not a claim to SGD or Adam.
    checked = 0
    for w, u in product(range(-127, 128), repeat=2):
        next_w = ema((w,), (u,))[0]
        assert -127 <= next_w <= 127
        assert 0 <= 7*w + u - 8*next_w < 8
        checked += 1
    left = ema(ema((0,), (120,)), (-120,))[0]
    right = ema(ema((0,), (-120,)), (120,))[0]
    assert left == -2 and right == 1
    state = ema((0,)*16, (120,)*16)
    assert state == (15,)*16  # persists once the observation is removed
    # Authorized basis-vector score queries reconstruct every coefficient.
    recovered = tuple(sum(w*int(i==j) for j,w in enumerate(state)) for i in range(16))
    assert recovered == state
    # Multiplication by an inverse modulo prime t is NOT integer rounding.
    t = 1032193
    modular = pow(8, -1, t)
    assert modular != 1//8
    # Exact division is a real positive control when numerator is divisible.
    assert (16*modular)%t == 2
    # Exact rational EMA avoids rounding only by growing the representation.
    rational = Fraction(0)
    denominator_bits = []
    for k in range(1, 21):
        rational = (7*rational + 1)/8
        assert rational.denominator == 8**k
        denominator_bits.append(rational.denominator.bit_length())
    return dict(exhaustive_interval_pairs=checked,
        invariant='-127 <= w,u <= 127 implies -127 <= floor((7w+u)/8) <=127',
        max_abs_numerator=1016, max_abs_public_score_r16=2032,
        order_sensitive_outputs=[left,right], persisted_coefficients=list(state),
        extraction_queries=16, extraction_exact=(recovered==state),
        modular_division_counterexample=dict(t=t,numerator=1,
            inverse_result=modular,integer_floor=0),
        rational_denominator_bits_at_20=denominator_bits[-1],
        private_learn_scalar_ops=dict(secret_public_mul=16,private_add=16,
            secure_floor_div8=16),
        private_infer_public_features_scalar_ops=dict(secret_public_mul=16,
            private_add=15,recipient_bound_score_release=1),
        private_infer_private_features_scalar_ops=dict(secret_secret_mul=16,
            private_add=15,recipient_bound_score_release=1),
        assumptions='authenticated ingress; fixed feature/update policy; secure floor; '
            'bound private release; external continuity; all unrealized here')


def parameter_ledger() -> dict:
    limbs = [0xffffee001, 0xffffc4001, 0x1ffffe0001]
    Q = math.prod(limbs)
    # Reproduce prime search with deterministic trial division at this small t.
    def prime(n):
        return n>=2 and all(n%d for d in range(2,math.isqrt(n)+1))
    t = next(n for n in range((1<<20)-1,1,-1) if n%8192==1 and prime(n))
    assert t == 1032193
    rows = []
    for name,N,bits,L in [('deployed',4096,109,3),
                         ('apple4096_total',4096,83,3),
                         ('apple8192_total',8192,148,3)]:
        # 2-component, uncompressed, full-level u64 RNS array; excludes keys.
        rows.append(dict(name=name,N=N,nominal_total_logq=bits,RNS_limbs=L,
            ct_raw_u64_bytes=2*N*L*8,
            ideal_bitpacked_ct_bytes=(2*N*bits+7)//8,
            radix2_NTT_butterflies_one_transform=L*(N//2)*int(math.log2(N))))
    return dict(deployed_Q=str(Q),log2_Q=math.log2(Q),Q_bit_length=Q.bit_length(),
        limbs=[hex(x) for x in limbs],t=t,t_is_not_2pow20=True,
        ideal_scalar_rounding_margin_floor=Q//(2*t),
        geometry=rows,security_bits=None,
        caveat='Geometry only. Apple total includes reserved key-switch modulus; '
          'our ciphertext-level comparison is not a matching implementation benchmark.')


def main() -> None:
    report = dict(status='EXECUTED exact scalar arithmetic models; NOT encrypted learner',
        command='python3 research/learn_infer_only/experiments/he_closure_costs/ledger.py',
        python=sys.version,platform=platform.platform(),
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        noise=noise_audit(),
        lowrank_executed=[execute_lowrank(private_x=b) for b in [False,True]],
        lowrank_frontier=[lowrank_count(4096,16,T,b)
                         for T in [1,128,129] for b in [False,True]],
        private_dataflow=taint_audit(),restricted_learner=learner_audit(),
        parameters=parameter_ledger())
    (HERE/'results.json').write_text(json.dumps(report,indent=2)+'\n')
    with (HERE/'lowrank_counts.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=list(report['lowrank_frontier'][0]))
        writer.writeheader(); writer.writerows(report['lowrank_frontier'])
    print(json.dumps({k: v for k,v in report.items() if k not in
        ['noise','lowrank_frontier','lowrank_executed']},indent=2))
    print('PASS: phase noise, rank-one failure, balanced sum, rerandomization, '
          'arithmetic counts, taint, interval closure, order, extraction, modular division')


if __name__ == '__main__':
    main()
