#!/usr/bin/env python3
"""Independent public integer, finite-ring and counting audit.
No cryptographic objects, random sampling, estimator, attack or network.
"""
from pathlib import Path
from fractions import Fraction as Q
from itertools import product, combinations
from collections import Counter
from math import isqrt
import hashlib
import json

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
SOURCE=REPO/'research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_candidate'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
frozen={'CANDIDATE.md':'5010b72b024aa7154504a7c0dd0de306fe0068b3af3b33b5026b444c510a0dc2',
        'RING_REGULARITY.md':'2926555d5842bb71af7b16caec3eef512a9c7cfea99e877b862bcfea79d30e85',
        'PARAMETERS.md':'c23732e366fe5966ddf971c0f69fdf51cec41bee134d0bf3e4da19367631b78d'}
for name,digest in frozen.items(): assert sha(SOURCE/name)==digest
source_pins=json.loads((SOURCE/'SOURCES.json').read_text())
for item in source_pins['sources']:
    assert sha(Path(item['pdf_path']))==item['pdf_sha256']
    assert sha(Path(item['extract_path']))==item['extract_sha256']
scalar=source_pins['frozen_scalar_math_reference']
assert sha(Path(scalar['path']))==scalar['sha256']

# Check the order certificate directly, without calling a primality package.
cert=json.loads((SOURCE/'searches/prime_certificate.json').read_text())
q=int(cert['q'])
c=4294967767
assert c%2==1 and q==c*2**256+1
assert pow(3,c*2**255,q)==q-1
assert (2**256+1)**2>q
assert 2**288<q<2**289
N,w,d,r,W,T=4096,64,577,16,32,384
zeta=pow(3,(q-1)//(2*N),q)
assert zeta==int(cert['primitive_2N_root'])
assert pow(zeta,N,q)==q-1 and pow(zeta,2*N,q)==1
p=28439893
assert all(p%ell for ell in range(2,isqrt(p)+1))
X=(p-1)//2
D=d*X
Delta=q//D
sigK,sige,BK,BE,F=2**24,2**10,2**27,2**13,2**244
dim=N*w
delta=Q(1,2**192)
assert sigK**64 >= (212*N)**32*q**3
assert q**122>=N**64
reg=[]
for k in (1,2):
    rank=N*sum((Q(1,q**(w-i)) for i in range(k)),Q(0))
    short=Q(2**N,q**(192*(3-k)))
    assert rank+short<delta
    reg.append({'k':k,'rank_plus_short_below_2_minus192':True,'short_q_exponent':192*(3-k)})
C=w*N*BK*BE
assert C==2**58
tauK=Q(3*d*dim*sigK,2**256)
taue=Q(3*dim*sige,2**256)
smudge=Q(d*C,2*F+1)+tauK+taue
assert D>=2*W*X+1 and Delta>2*W*(F+C)
# The residue-circle gap is at least Delta, including the two extreme codepoints.
assert q-2*W*X*Delta>=Delta
correct=tauK+T*taue
assert correct<Q(1,2**203)
privacy=[]
for j in range(r+1):
    setup=(2*(d-r)+1)*delta
    mask=(2*(d-j)+1)*delta
    stat=2*setup+2*T*(smudge+mask)
    assert stat<Q(1,2**168)
    privacy.append({'coalition_size':j,'noncomputational_terms_below_2_minus168':True})
pack=lambda count,bits:(count*bits+7)//8
costs={'ciphertext_coefficients':dim+d,'ciphertext_bytes':pack(dim+d,289),
       'full_ring_ciphertext_bytes':pack((w+d)*N,289),
       'public_A_bytes':pack(dim,289),'public_P_bytes':pack(d*N,289),
       'public_A_P_bytes':pack((w+d)*N,289),
       'one_recipient_key_bytes_on_strict_tail':pack(dim,28),
       'all_recipient_key_bytes_on_strict_tail':r*pack(dim,28),
       'full_ring_products_per_encryption':w,'scalar_constant_products_per_encryption':d*N,
       'read_coefficient_products':dim,'Gaussian_coefficients_per_encryption':dim,
       'uniform_scalar_floods_per_encryption':d,'uniform_secret_coefficients_per_encryption':N}
assert costs['ciphertext_bytes']==9490797
assert costs['public_A_P_bytes']==94847488
assert costs['one_recipient_key_bytes_on_strict_tail']==917504
assert 2**279*sige>q and 2**278*sige<q

# Exhaust the rank law for all 2x3 matrices over F5, with no invertibility conditioning.
matrices=full_rank=0
for flat in product(range(5),repeat=6):
    a,b=flat[:3],flat[3:]
    rank2=any((a[i]*b[j]-a[j]*b[i])%5 for i,j in combinations(range(3),2))
    matrices+=1
    full_rank+=bool(rank2)
assert full_rank==(5**3-1)*(5**3-5) and matrices==5**6
rank_probability=Q(full_rank,matrices)
assert rank_probability==(1-Q(1,5**3))*(1-Q(5,5**3))

# Fixed nonzero ring rows may vanish in CRT slots. Test the exact per-column
# image law in R_5=F5 x F5 for both one and zero common-vanishing slots.
image_checks=[]
for s1,s2 in [((0,1),(0,2)),((1,0),(0,1))]:
    outputs=Counter()
    for a10,a11,a20,a21 in product(range(5),repeat=4):
        outputs[((s1[0]*a10+s2[0]*a20)%5,(s1[1]*a11+s2[1]*a21)%5)]+=1
    vanished=sum(s1[j]==0 and s2[j]==0 for j in range(2))
    assert len(outputs)==5**(2-vanished)
    assert set(outputs.values())=={5**(4-(2-vanished))}
    image_checks.append({'common_zero_slots':vanished,'image_size':len(outputs),
                         'preimages_each':next(iter(outputs.values()))})

def mul(a,b,mod=None):
    n=len(a)
    out=[0]*n
    for i,x in enumerate(a):
        for j,y in enumerate(b):
            out[(i+j)%n]+=(-1 if i+j>=n else 1)*x*y
    return tuple(v%mod for v in out) if mod else tuple(out)
def evaluate(a,x,mod): return sum(c*pow(x,i,mod) for i,c in enumerate(a))%mod

# The low coefficient projection is injective on each ideal, including the
# zero ideal. Enumerate all 17^4 ring elements and all 16 CRT-vanishing sets.
roots=(2,8,15,9)
assert all(pow(x,4,17)==16 for x in roots)
ideals=[{} for _ in range(16)]
for poly in product(range(17),repeat=4):
    zero_mask=sum(1<<i for i,x in enumerate(roots) if evaluate(poly,x,17)==0)
    for mask in range(16):
        if zero_mask&mask==mask:
            free=4-mask.bit_count()
            low=poly[:free]
            assert low not in ideals[mask]
            ideals[mask][low]=poly
assert all(len(ideals[mask])==17**(4-mask.bit_count()) for mask in range(16))
idempotent=(13,15,16,8)
assert mul(idempotent,idempotent,17)==idempotent
assert [evaluate(idempotent,x,17) for x in roots]==[1,0,0,0]
counterexample_ranks=[2 if evaluate(idempotent,x,17) else 1 for x in roots]
assert counterexample_ranks==[2,1,1,1]

# Check the signed constant coefficient and Euclidean adjoint independently.
constant_controls=adjoint_controls=0
for n in (2,4):
    vectors=tuple(product((-1,0,1),repeat=n))
    for a in vectors:
        invol=(a[0],)+tuple(-a[n-i] for i in range(1,n))
        for b in vectors:
            assert mul(a,b)[0]==a[0]*b[0]-sum(a[i]*b[n-i] for i in range(1,n))
            constant_controls+=1
            # Every basis vector tests one coordinate of the adjoint identity.
            for j in range(n):
                ej=tuple(int(i==j) for i in range(n))
                assert sum(x*y for x,y in zip(mul(a,b),ej))==sum(x*y for x,y in zip(b,mul(invol,ej)))
                adjoint_controls+=1

# Project an independent uniform second ring output to its constant coordinate:
# first output retained in full; projected scalar is independent and uniform.
projected=Counter()
for P0,P1,U0,U1 in product(range(5),repeat=4):
    projected[(P0,P1,(U0+U1)*pow(2,-1,5)%5)]+=1
assert len(projected)==5**3 and set(projected.values())=={5}

shift_controls=0
for f in range(1,9):
    support=set(range(-f,f+1))
    for t in range(-3*f,3*f+1):
        shifted={x+t for x in support}
        tv=Q(len(support^shifted),2*len(support))
        assert tv==min(Q(1),Q(abs(t),2*f+1))
        shift_controls+=1

result={'status':'PASS; public source/math checks only','frozen_sources':frozen,
        'script_sha256':sha(Path(__file__)),'prime_order_certificate_checked':True,
        'complete_splitting_order_checked':True,'q_bits':q.bit_length(),
        'smoothing_integer_inequality_checked':True,'regularity':reg,
        'correctness_bound':'<2^-203','privacy_coalitions':privacy,'RLWE_multiplier':2*T,
        'costs':costs,'rank_law_matrices':matrices,'rank_two_matrices':full_rank,
        'rank_two_probability':str(rank_probability),'CRT_column_image_checks':image_checks,
        'ideal_low_coordinate_injectivity':{'ring_elements':17**4,'ideals':16,'all_pass':True},
        'source_rejection_test_counterexample_CRT_ranks':counterexample_ranks,
        'constant_coefficient_controls':constant_controls,'adjoint_controls':adjoint_controls,
        'joint_projection_atoms':len(projected),'joint_projection_preimages_each':5,
        'integer_shift_controls':shift_controls,
        'noise_width_to_modulus':'2^-279 < sigma_e/q < 2^-278; width convention, not hardness',
        'source_script_executed':False,'crypto_runs':0,'estimator_runs':0,'Gaussian_samples':0,
        'private_files_read':0,'web_queries':0,'computational_security_endorsement':False}
(HERE/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
