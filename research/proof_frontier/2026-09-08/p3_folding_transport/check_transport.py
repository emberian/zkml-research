#!/usr/bin/env python3
"""Finite pure arithmetic/index correspondence controls; no prover or crypto runtime.

The field presentation follows pinned p3 BabyBear BinomialExtensionData<4>:
F_p[U]/(U^4-11). This script is a reference calculation, not execution of Rust.
"""
from pathlib import Path
from collections import Counter
import hashlib
import json
import time

HERE = Path(__file__).resolve().parent
P = 2013265921
ROOT27 = 440564289
HALF = pow(2, -1, P)
counts = Counter()
controls = {}

class E:
    __slots__ = ('v',)
    def __init__(self, v=0):
        self.v = v.v if isinstance(v, E) else tuple(x % P for x in (v if isinstance(v, tuple) else (v,0,0,0)))
    def __add__(self, other):
        other = E(other)
        return E(tuple(a+b for a,b in zip(self.v,other.v)))
    __radd__ = __add__
    def __neg__(self): return E(tuple(-a for a in self.v))
    def __sub__(self, other): return self + -E(other)
    def __rsub__(self, other): return E(other) + -self
    def __mul__(self, other):
        other = E(other)
        tmp = [0]*7
        for i,a in enumerate(self.v):
            for j,b in enumerate(other.v): tmp[i+j] += a*b
        for k in range(6,3,-1): tmp[k-4] += 11*tmp[k]
        return E(tuple(tmp[:4]))
    __rmul__ = __mul__
    def __pow__(self,n):
        if n < 0:
            assert self != E(0), 'inverse of zero is excluded'
            return self ** ((P**4-2)*(-n))
        a,r = self,E(1)
        while n:
            if n & 1: r = r*a
            a,n = a*a,n>>1
        return r
    def __truediv__(self,other): return self * (E(other)**-1)
    def __eq__(self,other): return self.v == E(other).v
    def __repr__(self): return repr(self.v)

def root(bits):
    assert 0 <= bits <= 27
    return pow(ROOT27,1 << (27-bits),P)

def rev(q,bits):
    assert 0 <= q < 1 << bits
    return int(f'{q:0{bits}b}'[::-1],2) if bits else 0

def bitrev(word):
    bits = len(word).bit_length()-1
    assert 1 << bits == len(word)
    return [word[rev(i,bits)] for i in range(len(word))]

def evaluate(coeffs,x):
    out = E(0)
    for c in reversed(coeffs): out = out*x+c
    return out

def coefficients(size,tag):
    return [E((3*i+tag, i*i+tag+1, 2*i+tag+2, (i+tag)%5)) for i in range(size)]

def evaluation_word(coeffs,bits,shift=1):
    g = root(bits)
    return [evaluate(coeffs,shift*pow(g,i,P)%P) for i in range(1 << bits)]

def natural_fold(word,beta):
    bits = len(word).bit_length()-1
    n = len(word)//2
    inv = pow(root(bits),-1,P)
    return [(word[i]+word[i+n])*HALF + (word[i]-word[i+n])*beta*(HALF*pow(inv,i,P)%P)
            for i in range(n)]

def source_matrix_fold(word,beta,log_arity,mutation=None):
    """Pinned two_adic_pcs.rs:256–334, including the in-place twiddle recurrence."""
    data = list(word)
    bits = len(data).bit_length()-1
    inverse = pow(root(bits),-1,P)
    twiddles = [HALF*pow(inverse,i,P)%P for i in range(len(data)//2)]
    if mutation != 'omit_twiddle_bitrev': twiddles = bitrev(twiddles)
    challenge = beta
    for step in range(log_arity):
        height = len(data)//2
        if step:
            for j in range(height): twiddles[j] = 2*twiddles[2*j]**2%P
        data = [(data[2*j]+data[2*j+1])*HALF +
                (data[2*j]-data[2*j+1])*challenge*twiddles[j] for j in range(height)]
        if mutation != 'repeat_beta': challenge = challenge*challenge
    return data

def source_row_fold(row,index,log_height,log_arity,beta,mutation=None):
    """Pinned fold_row: subgroup start, bit-reversed fibre points, interpolation."""
    start = pow(root(log_height+log_arity),rev(index,log_height),P)
    xs = [start*pow(root(log_arity),i,P)%P for i in range(1 << log_arity)]
    if mutation != 'omit_fibre_bitrev': xs = bitrev(xs)
    out = E(0)
    for i,yi in enumerate(row):
        num,den = E(1),1
        for j,xj in enumerate(xs):
            if i != j: num,den = num*(beta-xj),den*(xs[i]-xj)%P
        out += yi*num*pow(den,-1,P)
    return out

def coefficient_fold(coeffs,beta,arity):
    return [sum((coeffs[i+j]*beta**j for j in range(arity) if i+j<len(coeffs)),E(0))
            for i in range(0,len(coeffs),arity)]

def quotient_coefficients(coeffs,z):
    """Exact synthetic division of f(X)-f(z) by X-z."""
    out = [E(0)]*(len(coeffs)-1)
    carry = coeffs[-1]
    for i in range(len(coeffs)-2,-1,-1):
        out[i] = carry
        carry = coeffs[i]+z*carry
    assert carry == evaluate(coeffs,z)
    return out

start = time.monotonic()
sources = json.loads((HERE/'SOURCES.json').read_text())
for name,entry in sources['sources'].items():
    assert hashlib.sha256(Path(name).read_bytes()).hexdigest() == entry['sha256'],name
assert pow(ROOT27,1<<27,P)==1 and pow(ROOT27,1<<26,P)==P-1
assert root(20)==195061667 and pow(31,15,P)==ROOT27
assert E((0,1,0,0))**4==E(11)
for a in [E((3,5,7,11)),E((2,1,0,0)),E(31)]:
    assert a*(a**-1)==E(1)
    counts['extension_inverse_controls']+=1

# Exhaustive small index domains, every allowed reduction and every row member.
for bits in range(13):
    for q in range(1<<bits):
        rq=rev(q,bits)
        assert rev(rq,bits)==q
        counts['index_involution']+=1
        for a in range(bits+1):
            b=bits-a
            parent=q>>a
            member=q% (1<<a)
            assert rev(parent,b)==rq%(1<<b)
            assert rq==rev(parent,b)+(1<<b)*rev(member,a)
            counts['index_projection_and_fibre']+=1
    if bits:
        fibres=Counter(rev(q>>1,bits-1) for q in range(1<<bits))
        assert len(fibres)==1<<(bits-1) and set(fibres.values())=={2}
        counts['uniform_pair_seed_domains']+=1
# Actual 20-bit dimension: deterministic spread, boundaries, all 20 reductions.
target_queries=sorted({0,1,2,3,(1<<20)-1,(1<<20)-2}|{(i*7919+104729)% (1<<20) for i in range(4096)})
for q in target_queries:
    for a in range(21):
        assert rev(q>>a,20-a)==rev(q,20)%(1<<(20-a))
        counts['target20_index_projection']+=1
    seed=rev(q>>1,19)
    for j in range(19):
        assert seed%(1<<(19-j))==rev(q>>(j+1),19-j)
        counts['target20_existing_coherent_path']+=1
controls['wrong_modulo_before_bitrev']=rev(181>>3,5)!=181%32
controls['wrong_shift_direction']=rev(181>>3,5)!=rev(181%32,5)

betas=[E(0),E(1),E((3,5,7,11))]
mutations=Counter()
for bits in range(1,8):
    coeffs=coefficients(1<<bits,bits+2)
    natural=evaluation_word(coeffs,bits)
    source=bitrev(natural)
    for beta in betas:
        for a in range(1,min(bits,3)+1):
            got=source_matrix_fold(source,beta,a)
            expected=bitrev(evaluation_word(coefficient_fold(coeffs,beta,1<<a),bits-a))
            assert got==expected
            nat=list(natural)
            for step in range(a): nat=natural_fold(nat,beta**(1<<step))
            assert got==bitrev(nat)
            for r,value in enumerate(got):
                row=source[r*(1<<a):(r+1)*(1<<a)]
                assert value==source_row_fold(row,r,bits-a,a,beta)
                counts['row_matrix_coefficient_fold_equalities']+=1
            counts['fold_cases']+=1
            if bits>=3 and beta==betas[-1]:
                mutations['omit_twiddle_bitrev'] += source_matrix_fold(source,beta,a,'omit_twiddle_bitrev')!=expected
                mutations['omit_input_bitrev'] += source_matrix_fold(natural,beta,a)!=expected
                if a>1:
                    mutations['repeat_beta_within_high_arity'] += source_matrix_fold(source,beta,a,'repeat_beta')!=expected
                    mutations['omit_fibre_bitrev'] += any(
                        source_row_fold(source[r*(1<<a):(r+1)*(1<<a)],r,bits-a,a,beta,'omit_fibre_bitrev')!=got[r]
                        for r in range(len(got)))

# Exact coset/quotient pullback, with a non-base-field opening point.
coset=31
z=E((5,1,2,3))
coeffs=coefficients(13,17)
qcoeffs=quotient_coefficients(coeffs,z)
pulled=[c*pow(coset,i,P) for i,c in enumerate(qcoeffs)]
f_pulled=[c*pow(coset,i,P) for i,c in enumerate(coeffs)]
normalized_q=quotient_coefficients(f_pulled,z*pow(coset,-1,P))
assert pulled==[c*pow(coset,-1,P) for c in normalized_q]
wrong_coset=wrong_scale=False
for i in range(64):
    y=pow(root(6),rev(i,6),P)
    x=coset*y%P
    rational=(evaluate(coeffs,z)-evaluate(coeffs,x))/(z-x)
    assert rational==evaluate(pulled,y)
    assert rational==evaluate(normalized_q,y)*pow(coset,-1,P)
    wrong_coset |= rational!=evaluate(qcoeffs,y)
    wrong_scale |= rational!=evaluate(normalized_q,y)
    counts['coset_quotient_pullback_rows']+=1
controls['omit_coset_pullback']=wrong_coset
controls['omit_quotient_scaling']=wrong_scale

# Mixed heights force arities 8,4,2, exercising all injection interfaces.
heights=[7,4,2,1]
input_coeffs={h:coefficients(1<<(h-1),29+h) for h in heights}
input_words={h:bitrev(evaluation_word(c,h)) for h,c in input_coeffs.items()}
current=input_words[7]
current_coeffs=input_coeffs[7]
h=7
rounds=[]
remaining=heights[1:]
injection_controls=Counter()
while h>1:
    a=min(3,h-remaining[0],h-1)
    beta=E((h+3,h+5,2*h+7,11))
    folded=source_matrix_fold(current,beta,a)
    next_h=h-a
    next_coeffs=coefficient_fold(current_coeffs,beta,1<<a)
    inject=input_words[next_h] if next_h==remaining[0] else [E(0)]*len(folded)
    combined=[v+beta**(1<<a)*w for v,w in zip(folded,inject)]
    if next_h==remaining[0]:
        injection_controls['omit_next_height_input'] += combined!=folded
        injection_controls['use_beta_instead_of_beta_to_arity'] += combined!=[v+beta*w for v,w in zip(folded,inject)]
        next_coeffs=[c+beta**(1<<a)*d for c,d in zip(next_coeffs,input_coeffs[next_h])]
        remaining.pop(0)
    assert combined==bitrev(evaluation_word(next_coeffs,next_h))
    rounds.append(dict(bits=h,log_arity=a,beta=beta,word=current,injection=inject,next_word=combined))
    current,current_coeffs,h=combined,next_coeffs,next_h
assert not remaining and len(current_coeffs)==1
assert [r['log_arity'] for r in rounds]==[3,2,1]
for query in range(128):
    index=query
    value=input_words[7][query]
    for r in rounds:
        a=r['log_arity'];arity=1<<a
        parent=index>>a
        row=r['word'][parent*arity:(parent+1)*arity]
        assert row[index%arity]==value
        # source verifier reinserts self at index%arity; siblings retain source order.
        siblings=[x for j,x in enumerate(row) if j!=index%arity]
        reconstructed=list(siblings)
        reconstructed.insert(index%arity,value)
        assert reconstructed==row
        value=source_row_fold(reconstructed,parent,r['bits']-a,a,r['beta'])+r['beta']**arity*r['injection'][parent]
        assert value==r['next_word'][parent]
        index=parent
        counts['multiheight_query_rounds']+=1
    assert value==current_coeffs[0]
    counts['multiheight_complete_queries']+=1

# The final verifier deliberately retains the global root/reversal width.
for initial_bits in range(1,13):
    for final_bits in range(initial_bits+1):
        for q in range(1<<final_bits):
            assert pow(root(initial_bits),rev(q,initial_bits),P)==pow(root(final_bits),rev(q,final_bits),P)
            counts['final_point_global_vs_final_root']+=1
controls['wrong_final_root_without_exponent_rescaling']=(pow(root(7),rev(1,3),P)!=pow(root(3),rev(1,3),P))

assert mutations and all(mutations.values())
assert injection_controls and all(injection_controls.values())
assert all(controls.values())
result=dict(all_checks_passed=True,seconds=time.monotonic()-start,field=dict(modulus=P,degree=4,relation='U^4=11',root27=ROOT27,root20=root(20)),
            counts=dict(counts),refused_mutations=dict(mutations),injection_controls=dict(injection_controls),
            other_controls=controls,multiheight_log_schedule=[3,2,1],
            multiheight_challenges=[list(r['beta'].v) for r in rounds],
            multiheight_final_constant=list(current_coeffs[0].v),source_files_checked=len(sources['sources']),
            scope='Pure finite field/index calculations from pinned source formulas; no compiled Rust/Lean implementation equivalence or soundness proof.',
            crypto_runtime_runs=0,web_queries=0)
(HERE/'RESULTS.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
