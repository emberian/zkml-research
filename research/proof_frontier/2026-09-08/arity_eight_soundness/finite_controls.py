"""Exact small-prime controls; no claim of testing the asymptotic theorem."""
import json
from collections import Counter
from pathlib import Path


def mul(a,b,p):
    out=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): out[i+j]=(out[i+j]+x*y)%p
    return out

def ev(a,x,p): return sum(c*pow(x,j,p) for j,c in enumerate(a))%p

def root_poly(M,p):
    a=[1]
    for r in range(M): a=mul(a,[(-r)%p,1],p)
    return a

def curve(coeff,z,p):
    return [sum(pow(z,j,p)*v[i] for j,v in enumerate(coeff))%p
            for i in range(len(coeff[0]))]

def constants_close_zero(w,p): return len(set(w))==1

out={}
p=17
for M in [7,8]:
    P=root_poly(M,p)
    # Existing RS semantics: evaluations of degree<1 polynomials on D={0,1}.
    coeff=[[0,c] for c in P]
    good=[z for z in range(p) if constants_close_zero(curve(coeff,z,p),p)]
    common_max=max(sum(all(coeff[j][i]==cs[j] for j in range(M+1))
                       for i in range(2))
                   for cs in ([v[0] for v in coeff],[v[1] for v in coeff]))
    assert good==list(range(M)) and common_max==1 and len(good)>2
    out[f'degree_{M}_rs_counterexample']={
        'field':p,'domain':[0,1],'dimension':1,'integer_radius':0,
        'real_radius':'1/4 (same exact-agreement event on length 2)',
        'polynomial_coefficients_low_to_high':P,'coefficient_words':coeff,
        'good_challenges':good,'good_count':len(good),'max_common_agreement':common_max,
        'naive_affine_n_bound':2,'correct_curve_Mn_bound':2*M,
        'injection_interpretation': 'last coefficient is fixed g' if M==8 else 'no injection'}
# Dependence obstruction: every B(a) is a singleton but beta² is always in B(beta).
independent=sum(b==a*a%p for a in range(p) for b in range(p))
correlated=sum(a*a%p==a*a%p for a in range(p))
assert independent==p and correlated==p
out['adaptive_binary_badsets']={'field':p,'bad_set':'B(a)={a^2}',
 'max_fibre_cardinality':1,'independent_probability':f'{independent}/{p*p}',
 'correlated_probability':f'{correlated}/{p}',
 'square_pushforward_counts':dict(sorted(Counter(a*a%p for a in range(p)).items())),
 'fourth_power_pushforward_counts':dict(sorted(Counter(pow(a,4,p) for a in range(p)).items()))}
# Adaptive injection invalidates the fixed-coefficient hypothesis completely.
# u1=(0,1), other u_r=0; choose g_beta=-(beta^-7)u1 for beta !=0.
adaptive_good=[]
for b in range(p):
    g=0 if b==0 else -pow(pow(b,7,p),-1,p)%p
    folded=[0,(b+pow(b,8,p)*g)%p]
    if constants_close_zero(folded,p): adaptive_good.append(b)
assert len(adaptive_good)==p and p>8*2
out['adaptive_injection_falsifier']={'field':p,'domain':[0,1],
 'u1':[0,1],'other_u_r':'zero','g_beta':'-(beta^-7)*u1 for beta!=0, else 0',
 'good_challenges':adaptive_good,'fixed_curve_threshold':16,
 'violated_premise':'g must be fixed before beta'}
# Nontrivial inhabited premises: positive radius, degree 2, common one-error support.
p=101;n=5;d=2;e=1
for M in [7,8]:
    polynomials=[[(j+1)%p,(j+2)%p] for j in range(M+1)]
    coeff=[[((j+1)+(j+2)*i+(j*j+1 if i==0 else 0))%p for i in range(n)]
           for j in range(M+1)]
    dists=[]
    for b in range(p):
        w=curve(coeff,b,p)
        cp=[sum(pow(b,j,p)*polynomials[j][t] for j in range(M+1))%p for t in range(d)]
        dists.append(sum(x!=ev(cp,i,p) for i,x in enumerate(w)))
    assert max(dists)==e and 2*e+d<=n and p>M*n
    assert all(coeff[j][i]==ev(polynomials[j],i,p) for j in range(M+1) for i in range(1,n))
    out[f'degree_{M}_premise_witness']={'field':p,'domain':list(range(n)),
       'dimension':d,'integer_radius':e,'good_count':p,'required_threshold':M*n,
       'max_distance_to_explicit_degree_lt_2_curve':max(dists),
       'common_agreement':[1,2,3,4], 'coefficient_words':coeff,
       'coefficient_polynomials_low_to_high':polynomials}

print(json.dumps(out,indent=2,sort_keys=True))
