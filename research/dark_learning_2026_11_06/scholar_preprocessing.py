"""Conservative MASCOT compiler for the harness's dealer objects; counts, not an OT implementation.
Run: python3 scholar_preprocessing.py > scholar_preprocessing_results.json
Protocol source: local ePrint 2016/505, Protocols 3--5, section 7.1 (pp. 12--19,22).
"""
import collections
import hashlib
import json
import math
import random
from pathlib import Path
import bfv_ref
import fhe_fork
import he_matvec
import mpc_fork
import spdz
import step_counts

N, NPARTY, KBITS, LAMBDA, TAU = 8192, 3, 61, 128, 4
# Main payload of MASCOT section 7.1, without optional OT communication optimizations.
I = (NPARTY - 1) * (KBITS**2 + KBITS)
R = NPARTY * I
BROADCAST = NPARTY * (NPARTY - 1) * KBITS
T_MAIN = NPARTY * (NPARTY - 1) * (TAU * LAMBDA * KBITS + (TAU + 5) * KBITS**2)
# Add the five share-distributions omitted in sec.7.1 and two sacrifice openings.
T = T_MAIN + 5 * NPARTY * (NPARTY - 1) * KBITS + 2 * BROADCAST
# One random bit via a fresh random r, a sacrificed triple computing r*r,
# openings of both Beaver differences and r^2. Reject r^2=0; expected factor p/(p-1).
BIT = R + T + 3 * BROADCAST


def inventory(d, fork):
    P = step_counts.params(d)
    ss = [P['S1'], P['S1'], P['S2'], P['S3']]
    ks = [P['K1'], P['K1'], P['K2'], P['K3']]
    matrix = 3 if fork == 'mpc' else 0
    outer = 0 if fork == 'fhe_b' else 2
    mul = d * (sum(2*(s-1) for s in ss) + 1)
    freivalds = 3*d if fork == 'he_mpc' else 0
    # Full K+kappa bits are needed, including high part, not only the low s bits
    # stored by the ideal dealer.
    bits = d * sum(k + spdz.KAPPA for k in ks)
    randoms = matrix*(d*d+d) + outer*2*d + d
    inputs = 2*d if fork in ('mpc', 'he_mpc') else 0
    if fork == 'he_mpc':
        randoms += 3*d  # masks for auth_plain of the three returned vectors
    mask_wire = mask_pairs = mask_used = 0
    if fork.startswith('fhe'):
        Qp, Bp, E = step_counts.fhe_params()
        F = step_counts.fhe_counts(d, N, Qp, Bp, E, fork[-1])
        mask_pairs = F['mask_pairs']['pairs']
        mask_used = F['mask_pairs']['used']
        # Keep section 8's masked-input/link schedule; MASCOT supplies each private
        # owner's input tuple. Its existing broadcasts remain in mask_wire.
        inputs += NPARTY * (mask_used + mask_pairs)
        mask_wire = F['mask_cost']['wire'] * KBITS
        online = F['steady']['online_wire'] * KBITS
    else:
        online = step_counts.mpc_counts(d)['steady']['online_wire'] * KBITS
        if fork == 'he_mpc':
            H = he_matvec.counts(d)
            online += (-3*(d*d+d)*NPARTY*(NPARTY-1)+H['he_wire']+H['spdz_wire'])*KBITS
    correlated_products = matrix*d*d + outer*d*d + d*254
    triples = mul + freivalds + correlated_products
    prep_bits = inputs*I + randoms*R + bits*BIT + triples*T + 2*correlated_products*BROADCAST
    return dict(d=d, fork=fork, scalar_triples=triples, triples_for_joint_bits=bits,
                matrix_products=matrix*d*d, outer_products=outer*d*d, power_products=d*254,
                online_mul_triples=mul, freivalds_triples=freivalds,
                jointly_hidden_random_fields=randoms, owner_input_tuples=inputs,
                joint_bits=bits, mask_pairs=mask_pairs, mask_used=mask_used,
                preprocessing_payload_bits=prep_bits,
                online_bits=online, existing_mask_wire_bits=mask_wire,
                total_payload_bits=prep_bits+online+mask_wire,
                expected_extra_bit_attempts_numerator=bits,
                expected_extra_bit_attempts_denominator='p-1')


def execution_control():
    p = bfv_ref.ntt_primes(61, 4, 16384)[3]
    d=8
    D=spdz.Dealer(p,3,91); E=spdz.Engine(p,3,D)
    M=[[0]*d for _ in range(d)]
    mpc_fork.run_step(E,M,M,[0]*d,[0]*d,mpc_fork.tables(p),7)
    tags=collections.Counter(tag for tag,_ in D.streams[0])
    want={'in':2*d*d+2*d,'mA':3*d*d,'mb':3*d,'mC':3*d,
          'tr':4*d,'trb':d*(5+5+4+8),'trh':4*d,
          'ta':37*d,'tb':37*d,'tc':37*d,'lp':255*d,
          'ou':2*d,'ow':2*d,'ouw':2*d*d}
    assert dict(tags)==want,(tags,want)
    assert D.count==step_counts.mpc_counts(d)['preprocessing_auth_values']
    return dict(d=d, tags=dict(tags), dealer_auth_values=D.count, all_equal=True)


def falsifiers():
    p=97
    # Exact exhaustions of the algebraic checks; independent of simulated dealer.
    a,b,ahat=13,17,29
    c=a*b%p; chat=ahat*b%p
    sacrifice=lambda cc,hh,s: (s*cc-hh-b*(s*a-ahat))%p==0
    honest=sum(sacrifice(c,chat,s) for s in range(p))
    wrong=sum(sacrifice((c+1)%p,chat,s) for s in range(p))
    assert honest==p and wrong==1
    # Same challenge before fixing the sacrifice witness permits arbitrary errors.
    s=23; badc=(c+1)%p; adaptive_chat=(chat+s)%p
    assert sacrifice(badc,adaptive_chat,s)
    # Bounded truncation relation: authentication alone accepts any field high part.
    sbit,K,kappa=2,3,2
    r=17; low=[(r>>i)&1 for i in range(sbit)]; high=r>>sbit
    valid=lambda rr,ll,hh: (all(x in (0,1) for x in ll) and 0<=hh<2**(K+kappa-sbit)
                           and rr==sum(v<<i for i,v in enumerate(ll))+(hh<<sbit))
    assert valid(r,low,high) and not valid(r,low,high+1)
    pw=[pow(11,j,p) for j in range(1,8)]
    chain=lambda v:all(v[j]==v[j-1]*v[0]%p for j in range(1,len(v)))
    badpw=pw.copy();badpw[4]=(badpw[4]+1)%p
    assert chain(pw) and not chain(badpw)
    U=[3,5];V=[7,11]; C=[[u*v%p for v in V] for u in U]
    outer=lambda C:all(C[i][j]==U[i]*V[j]%p for i in range(2) for j in range(2))
    assert outer(C); C[1][1]=(C[1][1]+1)%p; assert not outer(C)
    # Random-square bit generation is exactly balanced, conditional on r != 0.
    roots={x*x%p:min(x,p-x) for x in range(1,p)}
    bs=[((r*pow(roots[r*r%p],-1,p)+1)*pow(2,-1,p))%p for r in range(1,p)]
    assert collections.Counter(bs)=={0:48,1:48}
    return dict(sacrifice_honest_accepts=honest,sacrifice_bad_accepts=wrong,challenge_space=p,
                adaptive_prechallenge_forgery_accepts=True,wrong_truncation_high_refused=True,
                wrong_power_refused=True,wrong_outer_refused=True,random_square_bit_histogram=dict(collections.Counter(bs)))


def main():
    files=['spdz.py','mpc_fork.py','fhe_fork.py','step_counts.py','he_matvec.py']
    out=dict(scope='MASCOT main payload model plus explicit share and sacrifice traffic; no OT execution',
             parameters=dict(n=NPARTY,field_bits=KBITS,ot_security_bits=LAMBDA,tau=TAU),
             prices_bits=dict(input=I,joint_random=R,triple_main=T_MAIN,triple_with_share_and_sacrifice=T,
                              random_bit_nonzero_attempt=BIT,broadcast=BROADCAST),
             execution_control=execution_control(),falsifiers=falsifiers(),
             rows=[inventory(d,f) for d in (64,1024,4096) for f in ('mpc','he_mpc','fhe_a','fhe_b')],
             source_sha256={f:hashlib.sha256(Path(__file__).with_name(f).read_bytes()).hexdigest() for f in files})
    print(json.dumps(out,indent=2))
if __name__=='__main__':main()
