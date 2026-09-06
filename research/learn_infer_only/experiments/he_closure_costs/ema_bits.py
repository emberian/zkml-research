#!/usr/bin/env python3
"""Exact Boolean circuit cost model for bounded EMA; no FHE implementation.

Fixed ripple-carry network, no input-dependent pruning. AND/XOR/NOT counts
are logical gates; mapping them to bootstraps/latency requires a compiler.
"""
from collections import Counter
from itertools import product
from pathlib import Path
import hashlib
import json
import sys


def bits(x, width):
    return [(x >> i) & 1 for i in range(width)]


def signed(xs):
    return sum(x << i for i,x in enumerate(xs[:-1])) - (xs[-1] << (len(xs)-1))


def add(a, b, carry=0, tally=None):
    out=[]
    assert len(a)==len(b)
    for x,y in zip(a,b):
        p=x^y
        out.append(p^carry)
        carry=(x&y) ^ (p&carry)  # the two carry events are disjoint
    if tally is not None:
        tally['AND'] += 2*len(a)
        tally['XOR'] += 3*len(a)
    return out


def ema_word(w,u,tally=None):
    w8,u8=bits(w,8),bits(u,8)
    w11=w8+[w8[-1]]*3
    u11=u8+[u8[-1]]*3
    eight_w=[0]*3+w8
    seven_w=add(eight_w,[b^1 for b in w11],carry=1,tally=tally)
    numerator=add(seven_w,u11,tally=tally)
    if tally is not None:
        tally['NOT'] += 11
        tally['floor_wire_selections'] += 8
    return signed(numerator[3:])  # exact arithmetic-right-shift by3


def infer_public_boolean_features(state,features,tally=None):
    assert len(state)==len(features)==16
    words=[]
    for w,q in zip(state,features):
        assert q in [0,1]
        w8=bits(w,8)
        # Public control chooses either a signed-extended word or zero wires.
        words.append(w8+[w8[-1]]*4 if q else [0]*12)
    acc=words[0]
    for word in words[1:]:
        acc=add(acc,word,tally=tally)
    return signed(acc)


def main():
    count=0
    for w,u in product(range(-127,128),repeat=2):
        got=ema_word(w,u)
        assert got == (7*w+u)//8
        assert -127 <= got <= 127
        count += 1
    learn=Counter(); assert ema_word(120,-120,learn)==90
    # Every feature subset at the largest positive/negative states exercises
    # signed extension and the width of every partial sum in this schedule.
    tested=0
    for mask in range(1<<16):
        f=[(mask>>i)&1 for i in range(16)]
        for state in [[127]*16,[-127]*16,[127 if i%2 else -127 for i in range(16)]]:
            assert infer_public_boolean_features(state,f)==sum(w*q for w,q in zip(state,f))
            tested += 1
    infer=Counter(); assert infer_public_boolean_features([127]*16,[1]*16,infer)==2032
    result=dict(status='EXECUTED Boolean circuit, NOT FHE',
        command='python3 research/learn_infer_only/experiments/he_closure_costs/ema_bits.py',
        python=sys.version,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        exhaustive_learn_pairs=count,inference_cases=tested,
        bits_per_state_coefficient=8,private_state_bits_r16=128,
        learn_per_coefficient=dict(learn),
        learn_r16={k:16*v for k,v in learn.items()},infer_r16=dict(infer),
        nonlinear_AND_total_one_learn_one_infer=16*learn['AND']+infer['AND'],
        lowering='fixed ripple carry; signed 11-bit numerator; drop3bits; '
            '12-bit public-feature score accumulator',
        unresolved='bit ciphertext encoding; actual gate lowering and key sizes; '
            'bootstrapping/key-switch counts; noise/security; private ingress '
            'proof; recipient-bound output; timing; actual utility')
    out=Path(__file__).resolve().parent
    (out/'ema_bits_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
