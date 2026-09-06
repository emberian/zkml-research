#!/usr/bin/env python3
"""Exact integer/certificate and toy RNS audits; no encryption or SEAL execution."""
from __future__ import annotations
from itertools import product
from math import prod
from pathlib import Path
import hashlib, json, platform, random, sys, time


def nearest(q, t, z):
    assert q > 0
    return (t*z + q//2)//q


def doubled(q, t, z):
    return (2*t*z+q)//(2*q)


def conv_diagonal(a, b):
    n = len(a)
    assert n == len(b) and n > 0
    return [sum((1 if i <= k else -1)*a[i]*b[(k-i)%n]
                for i in range(n)) for k in range(n)]


def conv_schoolbook(a, b):
    n = len(a)
    out = [0]*n
    for i, ai in enumerate(a):
        for j, bj in enumerate(b):
            out[(i+j)%n] += (1 if i+j < n else -1)*ai*bj
    return out


def witness(q, t, a, b):
    z = conv_diagonal(a, b)
    y = [nearest(q,t,v) for v in z]
    r = [(t*v+q//2)%q for v in z]
    return dict(z=z,y=y,r=r,out=[v%q for v in y])


def checker(q, t, a, b, w):
    n = len(a)
    if not (n > 0 and len(b)==n and 0<t<q): return False
    if any(len(w[f])!=n for f in ('z','y','r','out')): return False
    if not all(0<=v<q for v in a+b): return False
    zref = conv_schoolbook(a,b)
    return all(w['z'][k] == zref[k]
               and 0 <= w['r'][k] < q
               and t*w['z'][k]+q//2 == q*w['y'][k]+w['r'][k]
               and w['out'][k] == w['y'][k]%q for k in range(n))


def redundant_crt(x, base):
    q = prod(base)
    return sum(((x % p)*pow(q//p,-1,p) % p)*(q//p) for p in base)


def fast_floor_model(x, base, output_prime):
    q=prod(base)
    # Literal modular formula from SEAL's fast_floor, given consistent full x.
    return ((x%output_prime - redundant_crt(x,base)%output_prime)
            *pow(q,-1,output_prime))%output_prime


def cost_rows():
    n=4096; moduli=[0xffffee001,0xffffc4001,0x1ffffe0001]
    q=prod(moduli); t=2**20; p=2013265921; qbits=(q-1).bit_length()
    rows=[]
    for tensor_component, mult in enumerate((1,2,1)):
        zmax=mult*n*(q-1)**2
        ymax=max(abs(nearest(q,t,-zmax)),abs(nearest(q,t,zmax)))
        assert -q*ymax <= -t*zmax+q//2
        assert t*zmax+q//2 < q*(ymax+1)
        zb=(2*zmax).bit_length(); yb=(2*ymax).bit_length()
        rows.append(dict(component=tensor_component,convolution_terms_per_coefficient=mult*n,
            z_abs_bound=zmax,z_signed_offset_range_bits=zb,
            y_abs_bound=ymax,y_signed_offset_range_bits=yb,
            remainder_bits=qbits,output_residue_bits=qbits,
            witness_range_bits_per_coefficient=zb+yb+qbits,
            witness_range_bits_all_coefficients=n*(zb+yb+qbits)))
    digit_rows=[]
    for bits in (8,14,15,16):
        digits=(qbits+bits-1)//bits
        digit_rows.append(dict(digit_bits=bits,digits_per_input=digits,
            direct_schoolbook_digit_products=4*n*n*digits*digits,
            max_single_digit_product=(2**bits-1)**2,
            single_digit_product_below_BabyBear=(2**bits-1)**2<p))
    return dict(label='DERIVED exact representation counts; no emitter, benchmark, or lower bound',
        N=n,Q=q,Q_bits=qbits,t=t,BabyBear=p,moduli=moduli,
        input_coefficients=4*n,raw_output_coefficients=3*n,
        input_booleanity_if_naive=4*n*qbits,
        output_booleanity_if_naive=3*n*qbits,
        remainder_booleanity_if_naive=3*n*qbits,
        lifted_quotient_remainder_booleanity_if_naive=sum(r['witness_range_bits_all_coefficients'] for r in rows),
        direct_scalar_products=4*n*n,rows=rows,digit_rows=digit_rows,
        byte_tile=dict(terms=256,term_max=255**2,sum_bound=256*255**2,
                       below_2pow24=256*255**2<2**24,below_BabyBear=256*255**2<p),
        excluded=['canonical residue/CRT reconstruction wiring','digit reconstruction and carries',
                  'range comparisons below Q, not merely below 2^109','operand provenance/commitments',
                  'negacyclic convolution argument','proof protocol and hashing',
                  'SEAL base extension/NTT/fast floor/Shenoy-Kumaresan refinement','relinearization'])


def main():
    start=time.monotonic(); counts={}; failures=[]
    scalar=0
    for q in range(2,40):
        for t in range(1,q):
            for z in range(-3*q,3*q+1):
                y=nearest(q,t,z); r=t*z+q//2-q*y
                assert 0<=r<q and y==doubled(q,t,z)
                assert nearest(q,t,z+q)==y+t
                for ybad in (y-1,y+1):
                    assert not (0<=r<q and t*z+q//2==q*ybad+r)
                scalar+=1
    counts['scalar_cases_with_negative_values_and_even_moduli']=scalar
    polynomials=0; mutations=0
    for q in range(2,10):
        t=max(1,q//3)
        for coeff in product(range(q),repeat=4):
            a=list(coeff[:2]); b=list(coeff[2:]); w=witness(q,t,a,b)
            assert w['z']==conv_schoolbook(a,b) and checker(q,t,a,b,w)
            assert all(abs(v)<=2*(q-1)**2 for v in w['z'])
            for field in ('z','y','r','out'):
                bad={f:list(vals) for f,vals in w.items()};bad[field][0]+=1
                assert not checker(q,t,a,b,bad)
                mutations+=1
            polynomials+=1
    rng=random.Random(20260906)
    for n in (1,3,4,8,16):
        for _ in range(80):
            q=rng.choice((31,97,65537,prod((0xffffee001,0xffffc4001,0x1ffffe0001))))
            t=rng.randrange(1,q)
            a=[rng.randrange(q) for _ in range(n)]; b=[rng.randrange(q) for _ in range(n)]
            w=witness(q,t,a,b)
            assert w['z']==conv_schoolbook(a,b) and checker(q,t,a,b,w)
            assert all(abs(v)<=n*(q-1)**2 for v in w['z'])
            polynomials+=1
    counts['polynomial_pairs_exhaustive_N2_Q2to9_plus_seeded']=polynomials
    counts['single_field_mutations_refused']=mutations
    counts['seeded_polynomial_cases']=400
    tensor_cases=0
    for q in range(2,10):
        t=max(1,q//3)
        for a0,a1,b0,b1 in product(range(q),repeat=4):
            # Full N=1 size-2 tensor; middle cross terms sum before scale.
            raw=[a0*b0,a0*b1+a1*b0,a1*b1]
            for z in raw:
                y=nearest(q,t,z); r=t*z+q//2-q*y
                assert 0<=r<q and t*z+q//2==q*y+r
            tensor_cases+=1
    counts['full_size2_tensor_cases_exhaustive_N1_Q2to9']=tensor_cases
    rns=0; disagree=0; alpha_hist={}
    for base in ((3,5),(5,7),(3,5,7)):
        q=prod(base)
        output_prime=11
        for x in range(-3*q,3*q+1):
            canonical=x%q; converted=redundant_crt(x,base)
            alpha=(converted-canonical)//q
            assert converted==canonical+alpha*q and 0<=alpha<len(base)
            expected=x//q-alpha
            assert fast_floor_model(x,base,output_prime)==expected%output_prime
            rns+=1; disagree+=expected != x//q
            alpha_hist[str(alpha)]=alpha_hist.get(str(alpha),0)+1
    counts['toy_RNS_fast_floor_cases']=rns
    counts['toy_RNS_fast_floor_differs_from_plain_floor']=disagree
    counts['toy_RNS_alpha_histogram']=alpha_hist
    teeth=dict(
        residue_only=dict(Q=31,t=4,products=[1,32],residues=[1,1],scaled=[nearest(31,4,z)%31 for z in (1,32)]),
        modular_certificate=dict(Q=31,t=4,z=1,y=17,r=19,modQ_passes=(4+15)%31==(31*17+19)%31,integer_passes=4+15==31*17+19),
        proof_field_wrap=dict(Q=31,p=7,t=4,z=1,y=7,r=19,all_witness_ranges_hold=True,residual_mod_p=(4+15-(31*7+19))%7),
        missing_remainder_range=dict(Q=31,z=1,t=4,y=1,r=-12,equality_holds=4+15==31-12),
        wrong_rounding=dict(Q=31,t=4,z=4,floor=16//31,nearest=nearest(31,4,4)),
        negative_tie=dict(Q=4,t=1,z=-2,nearest=nearest(4,1,-2),away_from_zero=-1),
        tensor_cross_terms=dict(Q=31,t=4,raw_terms=[4,4],correct_round_after_sum=nearest(31,4,8),wrong_sum_after_round=2*nearest(31,4,4)),
        fast_floor_not_plain_floor=dict(base=[3,5],x=1,redundant_lift=redundant_crt(1,(3,5)),fast_floor_integer=-1,plain_floor=0),
        noncanonical_operand_lift=dict(Q=31,t=4,a_canonical=1,a_shifted=32,b=1,same_residue=True,scaled=[0,4]),
        nonzero_negacyclic=dict(a=[1,2],b=[3,4],witness=witness(31,4,[1,2],[3,4])))
    assert all((teeth['modular_certificate']['modQ_passes'], not teeth['modular_certificate']['integer_passes']))
    data=dict(label='EXECUTED finite exact integer and toy RNS models; no encrypted computation and no SEAL execution',
        command=[sys.executable,str(Path(__file__).resolve())],python=sys.version,platform=platform.platform(),
        seed=20260906,script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        counts=counts,teeth=teeth,costs=cost_rows(),elapsed_seconds=time.monotonic()-start,
        metered_search_queries=0,primary_source_fetches=2)
    print(json.dumps(data,indent=2))

if __name__=='__main__': main()
