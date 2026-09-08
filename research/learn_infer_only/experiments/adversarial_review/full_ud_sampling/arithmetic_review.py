#!/usr/bin/env python3
"""Independent integer-cross-multiplication audit; no author-script execution."""
from pathlib import Path
from fractions import Fraction as Q
import hashlib
import json
import math

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
PARAM = REPO / 'research/proof_frontier/2026-09-08/parameter_delta'
P,N,D,M = 2013265921,2**20,2**19,19

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def check(q, tau, ext=4, target=55):
    # Equivalent to M*N/P^ext + (1-tau)^q <= 2^-target.
    survival = 1-tau
    a,b = survival.numerator,survival.denominator
    field = P**ext
    bn,an = b**q,a**q
    residual = (field-M*N*2**target)*bn - field*2**target*an
    # Narrow exact interval for error / target, with denominator 10^12.
    scaled_error_numerator = 2**target*(M*N*bn+field*an)
    denominator = field*bn
    lower = scaled_error_numerator*10**12//denominator
    return dict(q=q,tau=str(tau),extension=ext,target=target,
        passes=residual>=0,residual_sign=(residual>0)-(residual<0),
        residual_numerator_bits=abs(residual).bit_length(),
        residual_hex_sha256=hashlib.sha256(hex(residual).encode()).hexdigest(),
        error_over_target_lower=f'{lower}/1000000000000',
        error_over_target_strict_upper=f'{lower+1}/1000000000000')

old_tau=Q(8191,884736)
new_tau=Q(1,95)
assert 0<old_tau<Q(1,108)<new_tau
schedule=[]
for name,tau,band in [('new',new_tau,Q(1,4)),('old',old_tau,Q(1,6))]:
    radius=[Q(2,5)]+[(M-j)*tau for j in range(1,M+1)]
    folded=[Q(1,5)]+radius[1:M]
    gaps=[folded[j]-radius[j+1] for j in range(M)]
    assert len(gaps)==19 and all(g>=tau for g in gaps)
    assert radius[-1]==0
    assert all(0<radius[j]<band for j in range(1,M))
    degrees=[2**(19-j) for j in range(20)]
    sizes=[2**(20-j) for j in range(20)]
    assert all(degrees[j]==2*degrees[j+1] for j in range(19))
    assert all(Q(d,n)==Q(1,2) and d>=1 for d,n in zip(degrees,sizes))
    schedule.append(dict(name=name,tau=str(tau),radius=list(map(str,radius)),
        fold_radius=list(map(str,folded)),gaps=list(map(str,gaps)),
        degrees=degrees,sizes=sizes,band=str(band),all_pass=True))
assert 19*new_tau==Q(1,5) and 18*new_tau<Q(1,4)
assert 18*Q(1,108)==Q(1,6)
assert Q(1,95)<Q(2,95)  # fixed schedule falsifier fails at its last gap
boundaries=[check(3603,new_tau),check(3602,new_tau),
            check(4099,old_tau),check(4098,Q(1,108)),check(4098,old_tau)]
assert [x['passes'] for x in boundaries]==[True,False,True,False,False]

producer=json.loads((PARAM/'results.json').read_text())
rows=[]
for r in producer['fixed_initial_comparison']:
    ext,target=r['extension'],r['target_bits']
    field=P**ext
    if M*N*2**target>=field:
        assert r['new_q'] is None and r['old_q'] is None
        rows.append(dict(extension=ext,target=target,impossible_from_fixed_term=True))
        continue
    nq,oq=r['new_q'],r['old_optimal_attained_q']
    interior=Q(r['old_optimal_interior_tau'])
    checks=[check(nq,new_tau,ext,target),check(nq-1,new_tau,ext,target),
            check(oq,interior,ext,target),check(oq-1,Q(1,108),ext,target)]
    assert [x['passes'] for x in checks]==[True,False,True,False]
    assert interior<Q(1,108) and 19*interior<=Q(1,5)
    assert oq-nq==r['exact_optimal_queries_saved']
    rows.append(dict(extension=ext,target=target,old_minimum=oq,new_minimum=nq,
                     saving=oq-nq,checks=checks))

# Recompute every stored algebraic summand directly from the source formula.
profiles={'deployedBudget':(4,4,4,0,0), 'secureBudget120':(6,6,6,20,0),
          'baseGateExt4Fri':(4,1,4,20,23), 'ext6GateExt4Fri':(4,6,4,20,23),
          'unifiedExt6':(6,6,6,20,23)}
algebra=[]
for r in producer['algebra_models']:
    rexp,sexp,pexp,powbits,gates=profiles[r['model']]
    terms={'grinding':Q((2**40+2**8)*2**8*(N+1),P**rexp*2**powbits),
           'sumcheck':Q(2**8*20*3,P**sexp),
           'collision':Q(2**40*(2**40-1),2**249),
           'proximity':Q(N,P**pexp)}
    if gates:
        terms['gate_batch']=Q(gates-1,P**sexp)
    assert terms=={k:Q(v) for k,v in r['terms_exact'].items()}
    total=sum(terms.values(),Q(0))
    assert total==Q(r['total_exact'])
    bits=0
    while total<=Q(1,2**(bits+1)):
        bits+=1
    assert bits==r['floor_bits']
    algebra.append(dict(model=r['model'],floor_bits=bits,terms_identical=True))

ledger=[]
for r in producer['existing_query_ledger']:
    rate=Q(1,2**r['log_blowup'])
    error=((1+rate)/2)**r['q']/2**r['pow_bits']
    bits=0
    while error<=Q(1,2**(bits+1)):
        bits+=1
    assert bits==r['current_full_udr_floor_bits']
    ledger.append(dict(model=r['model'],floor_bits=bits,unchanged=True))

# Bounded arithmetic checks underpinning the exact existing carrier source.
prime=all(P%d for d in range(2,math.isqrt(P)+1))
assert prime and (P-1)//2==1006632960
assert pow(11,(P-1)//2,P)==P-1
assert pow((-11)%P,(P-1)//2,P)==P-1
assert N<P and P!=P**4
assert Q(4,5)*N>D
carrier=dict(modulus=P,prime_by_trial_division=prime,
    eleven_euler=pow(11,(P-1)//2,P),negative_eleven_euler=pow((-11)%P,(P-1)//2,P),
    extension_degree=4,field_cardinality=P**4,consecutive_domain_card=N,
    injective_base_domain_possible=N<P,base_field_cardinality_falsifier=P!=P**4,
    bad_pair_max_agreement=D,required_agreement=str(Q(4,5)*N))
result=dict(status='PASS',schedules=schedule,boundaries=boundaries,
    fixed_initial_rows=rows,algebraic_models=algebra,existing_query_ledger=ledger,
    carrier_arithmetic=carrier,saving=4099-3603,saving_fraction=str(Q(496,4099)),
    fixed_challenge_exceeds_2_pow_neg100=M*N*2**100>P**4,
    source_results_sha256=sha(PARAM/'results.json'),
    source_derive_sha256=sha(PARAM/'derive.py'),script_sha256=sha(Path(__file__)),
    source_script_executed=False,crypto_execution=False,lean_build=False)
(HERE/'arithmetic.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(dict(status=result['status'],query_boundaries=[(r['q'],r['tau'],r['passes']) for r in boundaries],
    savings=result['saving'],fixed_initial_rows=len(rows),algebra_models=len(algebra),
    query_ledger_rows=len(ledger),carrier_arithmetic=carrier),indent=2))
