#!/usr/bin/env python3
"""Independent public finite arithmetic controls. No crypto or Gaussian samples."""
from pathlib import Path
from fractions import Fraction as F
from itertools import product
from math import isqrt
import json,hashlib
HERE=Path(__file__).resolve().parent
AUTHOR=HERE.parent/'public_setup_pq/finite_reduction'
hash_file=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()

def logceil(x):
    assert x>=1
    k=x.bit_length()-1
    if 1<<k != x:k+=1
    assert (k==0 and x==1) or (1<<(k-1)) < x <= (1<<k)
    return k

def sqrtceil(x):
    z=isqrt(x)
    if z*z<x:z+=1
    assert z*z>=x and (z==0 or (z-1)*(z-1)<x)
    return z

def powtwo(e):return F(1<<e) if e>=0 else F(1,1<<(-e))

def rank_mod(a,p):
    a=[list(map(lambda x:x%p,row)) for row in a]
    d=len(a);n=len(a[0]);r=0
    for col in range(n):
        piv=next((i for i in range(r,d) if a[i][col]),None)
        if piv is None:continue
        a[r],a[piv]=a[piv],a[r]
        inv=pow(a[r][col],-1,p)
        a[r]=[(x*inv)%p for x in a[r]]
        for i in range(d):
            if i!=r:
                factor=a[i][col]
                a[i]=[(x-factor*y)%p for x,y in zip(a[i],a[r])]
        r+=1
        if r==d:break
    return r

rank_results=[]
for p,k,n,d in [(2,1,3,1),(2,1,3,2),(2,2,3,2),(3,1,3,2),(3,2,2,1),(2,3,2,1)]:
    q=p**k;fail=0;total=q**(n*d)
    vectors=list(product(range(q),repeat=n))
    for flat in product(range(q),repeat=n*d):
        a=[flat[i*n:(i+1)*n] for i in range(d)]
        full=rank_mod(a,p)==d
        image={tuple(sum(x*y for x,y in zip(row,v))%q for row in a) for v in vectors}
        assert full==(len(image)==q**d)
        fail+=not full
    success=F(1)
    for i in range(d):success*=1-F(1,p**(n-i))
    bound=F(p**d-1,(p-1)*p**n)
    assert F(fail,total)==1-success<=bound
    rank_results.append({'p':p,'k':k,'n':n,'d':d,'matrices':total,'failures':fail,'exact_probability':str(F(fail,total)),'geometric_upper_bound':str(bound),'image_surjectivity_matches_mod_p_rank':True})

def matmul(a,b):return [[sum(x*y for x,y in zip(row,col)) for col in zip(*b)] for row in a]
def trans(a):return [list(x) for x in zip(*a)]
def identity(n):return [[int(i==j) for j in range(n)] for i in range(n)]
def determinant(a):
    a=[[F(x) for x in row] for row in a];det=F(1);n=len(a)
    for j in range(n):
        p=next((i for i in range(j,n) if a[i][j]),None)
        if p is None:return F(0)
        if p!=j:a[p],a[j]=a[j],a[p];det=-det
        pivot=a[j][j];det*=pivot
        for i in range(j+1,n):
            c=a[i][j]/pivot
            for k in range(j,n):a[i][k]-=c*a[j][k]
    return det

# Deterministic integral block identity; these are public matrix fixtures.
n,M,L=2,3,4
X=[[1,0,2],[0,1,-1]]
R=[[1,-1,0,2],[0,1,1,-1],[1,0,-2,1]]
C=[row+[0]*(L-n) for row in identity(n)]
XR=matmul(X,R);X2t=[[a+b for a,b in zip(r,s)] for r,s in zip(C,XR)]
D=[row+[0]*(L-n) for row in trans(X)]
DRt=matmul(D,trans(R))
H=[[-x for x in row]+ir for row,ir in zip(trans(R),identity(L))]
H += [[x+y for x,y in zip(ir,row)]+[-x for x in dr] for ir,row,dr in zip(identity(M),DRt,D)]
P=trans(X)+trans(X2t)
E=identity(n)+[[0]*n for _ in range(M+L-n)]
assert matmul(H,P)==E and abs(determinant(H))==1
# Exact scalar-parameter covariance comparison on a=1, xi=2, Q=I, m=3,d=1.
qq=[0,1,1]
printed=[2*v+(4-v)+8 for v in qq]
repaired=[2*v+2*(4-v)+8 for v in qq]
assert printed==[12,13,13] and repaired==[16]*3
# The corrected integrality identity; Zb' is explicitly nonintegral.
f=F(1,2);c=F(-1,2);b=2
Zbprime=b+f;hint=f+c
assert Zbprime.denominator==2 and hint.denominator==1 and hint==(Zbprime+c)-b
# Exact rational sufficient elementary tail constant control using pi<22/7,
# pi>3 and e>8/3, which give c^2=2*pi*e^(1-2*pi)<(44/7)*(3/8)^5.
tail_c_squared_upper=F(44,7)*F(3,8)**5
assert tail_c_squared_upper<F(1,4)

inputs=json.loads((AUTHOR/'INPUTS.json').read_text())
expected=json.loads((AUTHOR/'RESULTS.json').read_text())
expected_by_name={r['name']:r for r in expected['profiles']}
kap=inputs['kappa'];lam=F(1,1<<kap);profiles=[]
for row in inputs['profiles']:
    n,d,M,L=row['n'],row['d'],row['M'],row['L'];m=M+L
    p,k=row['p'],row['k']
    assert p>=2 and all(p%a for a in range(2,isqrt(p)+1))
    q=p**k;s1=1<<row['sigma1_pow2'];s2=1<<row['sigma2_pow2']
    Ln,LM,LL,Ls=map(logceil,(n,M,L,s1))
    Q1=s1*sqrtceil(n*LM);Q2=2*sqrtceil(30*n*(Ls+Ln))
    A=sqrtceil(M)*Q1
    B=max((1+Q1*Q2)*sqrtceil(LM+LL+kap+3),sqrtceil(LM+4))
    K=(1+A)*(1+s2*Q2*sqrtceil(M*L))
    xi_min=logceil(2*K);xi_e=row.get('xi_pow2',xi_min);xi=1<<xi_e
    ae=row['encryption_error_width_pow2']-xi_e-1;a=powtwo(ae)
    checks={
      'n_at_least_100_and_kappa':n>=max(100,kap),
      'n_minus_d_at_least_kappa':n-d>=kap,
      'L_ge_M_gt_n':L>=M>n,
      'AR_sigma1':s1*s1>=81*(kap+Ln+2),
      'AR_strict_M':M>30*n*(Ls+Ln),
      'Gaussian_image_sigma2':s2>=A*B,
      'gadget_norm_tail':M>=kap+LL+1,
      'operator_norm_xi':xi>=2*K,
      'discrete_continuous_smoothing':a*a>=2*(kap+logceil(m-d)+2),
      'final_discretizer_smoothing':2*a*a*xi*xi>=kap+logceil(m)+2,
      'alpha_between_zero_and_one':(1<<row['encryption_error_width_pow2'])<q}
    er=expected_by_name[row['name']]
    assert checks==er['checks']
    assert xi_min==er['least_integer_certificate_xi_pow2']
    assert ae==er['base_LWE_error_width_pow2']
    assert logceil(A*B)==er['least_integer_certificate_sigma2_pow2']
    assert (1<<(xi_min-1))<2*K<=1<<xi_min
    # Full-width Gaussian image integer certificate and correct map alpha=2beta*xi.
    assert 2*a*xi==1<<row['encryption_error_width_pow2']
    reg=[M>=N*logceil(q)+kap+1 and s1*s1>=LM+kap+2 for N in (n,n+1)]
    assert all(reg)
    if all(checks.values()):
        assert F(L,1<<(M-1))<=lam
        rank_bound=F(p**d-1,(p-1)*p**n)
        assert rank_bound<lam
    profiles.append({'name':row['name'],'pass':all(checks.values()),'failed_checks':[x for x,v in checks.items() if not v],'xi_min_pow2':xi_min,'sigma2_min_pow2':logceil(A*B),'base_LWE_error_width_pow2':ae,'regularity_pass':reg,'prior_power_of_two_xi_fails':True})

ledger={}
for j in (0,inputs['r']):
    coeff=8*(inputs['d']-inputs['r'])+8*inputs['T']*(inputs['d']-j)+68*inputs['T']
    assert coeff==expected['privacy_ledger'][str(j)]['total_numerator_over_2_pow_kappa']
    assert F(coeff,1<<kap)<F(1,1<<139)
    ledger[j]={'LWE_multiplier':2*inputs['T'],'statistical_numerator':coeff,'denominator_pow2':kap,'strictly_below_2_pow_minus_139':True}
assert 2*1+2*3+8+16==32 and 32+2==34
result={'scope':'public exact arithmetic, deterministic matrix identities and finite rank enumeration; no crypto, Gaussian sampling, estimator or private runtime',
 'status':'PASS','reviewed_theorem_sha256':hash_file(AUTHOR/'FINITE_THEOREM.md'),
 'author_inputs_sha256':hash_file(AUTHOR/'INPUTS.json'),'author_results_sha256':hash_file(AUTHOR/'RESULTS.json'),'script_sha256':hash_file(Path(__file__)),
 'rank_controls':rank_results,'rank_matrices_total':sum(r['matrices'] for r in rank_results),
 'matrix_identity':{'dimensions':[2,3,4],'det_H':str(determinant(H)),'H_times_P_equals_E':True},
 'gaussian_parameter_covariance':{'printed_diagonal':printed,'repaired_diagonal':repaired,'target_diagonal':[16]*3},
 'integrality_counterexample':{'Zbprime':str(Zbprime),'h':str(hint),'corrected_identity':True},
 'tail_constant_squared_rational_upper':str(tail_c_squared_upper),'profiles':profiles,'ledger':ledger,
 'error_coefficients':{'ideal_reduction':32,'with_sampler_bound':34}}
(HERE/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
