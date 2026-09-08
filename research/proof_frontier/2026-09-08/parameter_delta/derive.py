#!/usr/bin/env python3
"""Exact rational audit of the full-UD radius change and existing consumer budgets.
No prover execution. Formula provenance is in SOURCE_MAP.md. All pass/fail and
minimum-query decisions use Fraction; log2 values are descriptive only.
"""
from fractions import Fraction as Q
from pathlib import Path
import csv, hashlib, json, math, time

OUT = Path(__file__).resolve().parent
P = 2013265921
N = 2**20
D = 2**19
T = 2**40
K = 2**8
V = 20
SC_D = 3
H = 248
HASH_Q = 2**40


def bits(x):
    assert x > 0
    return math.log2(x.denominator) - math.log2(x.numerator)


def floor_bits(x):
    k = math.floor(bits(x))
    while x > Q(2) ** (-k):
        k -= 1
    while x <= Q(2) ** (-(k+1)):
        k += 1
    return k


def min_samples(survival, fixed, target):
    assert 0 < survival < 1
    if fixed >= target:
        return None
    remainder = target - fixed
    low, high = 0, 1
    while survival**high > remainder:
        high *= 2
    while low < high:
        mid = (low + high) // 2
        if survival**mid <= remainder:
            high = mid
        else:
            low = mid + 1
    assert fixed + survival**low <= target
    assert low == 0 or fixed + survival**(low-1) > target
    return low


def algebra_terms(rbr_card, gate_card, sc_card, prox_card, pow_bits, constraints):
    terms = {
        'grinding': Q((T+K)*K*(N+1), rbr_card * 2**pow_bits),
        'sumcheck': Q(K*V*SC_D, sc_card),
        'collision': Q(HASH_Q*(HASH_Q-1), 2**(H+1)),
        'proximity': Q(N, prox_card),
    }
    if constraints:
        terms['gate_batch'] = Q(constraints-1, gate_card)
    return terms


models = {
    'deployedBudget': (P**4, None, P**4, P**4, 0, 0, 55),
    'secureBudget120': (P**6, None, P**6, P**6, 20, 0, 120),
    'baseGateExt4Fri': (P**4, P, P, P**4, 20, 23, 120),
    'ext6GateExt4Fri': (P**4, P**6, P**6, P**4, 20, 23, 120),
    'unifiedExt6': (P**6, P**6, P**6, P**6, 20, 23, 120),
}
algebra = []
for name, args in models.items():
    terms = algebra_terms(*args[:-1]); total = sum(terms.values(), Q(0))
    dominant = max(terms, key=terms.get)
    algebra.append({
        'model': name, 'delta_old': '1/8', 'delta_proposed': '1/5',
        'old_radius_ceiling': '1/6', 'new_radius_ceiling': '1/4',
        'old_delta_admissible': Q(1,8) < Q(1,6),
        'proposed_delta_old_admissible': Q(1,5) < Q(1,6),
        'proposed_delta_new_admissible': Q(1,5) < Q(1,4),
        'terms_exact': {k:str(v) for k,v in terms.items()},
        'terms_bits': {k:bits(v) for k,v in terms.items()},
        'total_exact': str(total), 'total_bits': bits(total), 'floor_bits': floor_bits(total),
        'target_bits': args[-1], 'target_met': total <= Q(1,2**args[-1]),
        'dominant_term': dominant, 'dominant_share': float(terms[dominant]/total),
        'old_new_error_equal': True,
    })

# Exact shrinking schedule satisfying the existing sampled tower hgap.
# radius(0)=Delta; foldRadius(0)=Delta/2;
# radius(j)=Delta/2-j*tau for 1<=j<=m; foldRadius(j)=radius(j) for j>0.
# tau=Delta/(2*m) => final radius0 and every hgap equality.
schedules=[]
for m in [1, 19]:
    assert m <= 19  # D / 2^m stays a positive integer.
    for label, initial, band in [('old_3over10',Q(3,10),Q(1,6)),
                                 ('new_2over5',Q(2,5),Q(1,4))]:
        tau=initial/(2*m)
        radius=[initial]+[initial/2-j*tau for j in range(1,m+1)]
        fold=[initial/2]+radius[1:m]
        assert all(radius[j+1]+tau <= fold[j] for j in range(m))
        assert radius[-1] == 0
        assert all(0 < radius[j] < band for j in range(1,m))
        assert all(D//2**j == 2*(D//2**(j+1)) for j in range(m))
        schedules.append({'label':label,'rounds':m,'initial_radius':str(initial),'tau':str(tau),
            'radius':[str(r) for r in radius], 'fold_radius':[str(r) for r in fold],
            'tail_band':str(band), 'all_gaps_hold':True,'all_positive_tail_degrees':True,
            'new_schedule_also_fits_old_band':all(0 < radius[j] < Q(1,6) for j in range(1,m)),
            'final_code_length':N//2**m,'final_degree_bound':D//2**m})

sampled=[]
for m in [1,19]:
    for ext,target in [(4,55),(4,99),(4,100),(6,120),(6,137)]:
        challenge=Q(m*N,P**ext)  # unchanged common-bound b=N consumer.
        row={'rounds':m,'extension':ext,'target_bits':target,
             'challenge_exact':str(challenge),'challenge_bits':bits(challenge),
             'challenge_floor_bits':floor_bits(challenge)}
        for key,initial in [('old',Q(3,10)),('new',Q(2,5))]:
            tau=initial/(2*m);q=min_samples(1-tau,challenge,Q(1,2**target))
            row[key+'_tau']=str(tau);row[key+'_q']=q
            if q is not None:
                total=challenge+(1-tau)**q
                row[key+'_total_bits']=bits(total)
                row[key+'_floor_bits']=floor_bits(total)
                row[key+'_minimal_exact']=True
                row[key+'_query_is_dominant']=(1-tau)**q > challenge
        if row['old_q'] is not None:
            row['queries_saved']=row['old_q']-row['new_q']
            row['fraction_saved']=Q(row['queries_saved'],row['old_q']).__str__()
        sampled.append(row)

# Fair comparison at the SAME initial farness radius Delta=2/5.
# The old theorem can spend extra slack in round zero: it need not set every
# radius gap equal. With m=19, tau_old=1/109 gives tail radius18/109<1/6.
# tau_new=1/95 saturates the final-radius budget and has tail18/95<1/4.
# The old open ceiling is tau<1/(6*(m-1))=1/108; it is not attained.
fixed_initial=[]
for ext,target in [(4,55),(4,99),(4,100),(6,120),(6,137)]:
    m=19;initial=Q(2,5);challenge=Q(m*N,P**ext)
    row={'rounds':m,'extension':ext,'target_bits':target,'initial_radius':str(initial),
         'old_open_tau_ceiling':'1/108','new_attained_tau':'1/95',
         'challenge_bits':bits(challenge)}
    for key,tau,band in [('old',Q(1,109),Q(1,6)),('new',Q(1,95),Q(1,4))]:
        radius=[initial]+[(m-j)*tau for j in range(1,m+1)]
        fold=[initial/2]+radius[1:m]
        assert all(radius[j+1]+tau<=fold[j] for j in range(m))
        assert all(0<radius[j]<band for j in range(1,m))
        assert radius[-1]==0
        q=min_samples(1-tau,challenge,Q(1,2**target))
        row[key+'_tau']=str(tau);row[key+'_tail_radius_1']=str(radius[1]);row[key+'_q']=q
        row[key+'_all_gaps_hold']=True
        if q is not None: row[key+'_floor_bits']=floor_bits(challenge+(1-tau)**q)
    # A lower bound on queries for any old-band schedule with this shared tau:
    # tau <1/108 => survival >107/108. q-1 at this unattained best limit fails.
    limq=min_samples(Q(107,108),challenge,Q(1,2**target))
    row['old_best_limit_query_lower_bound']=limq
    if limq is not None:
        # Strictly open radius ceiling: an unattained equality would cost one
        # extra query. Then exhibit a rational interior tau realizing the count.
        if challenge+Q(107,108)**limq == Q(1,2**target): limq+=1
        exponent=1
        while True:
            tau_safe=(1-Q(1,2**exponent))/108
            if challenge+(1-tau_safe)**limq <= Q(1,2**target): break
            exponent+=1
        assert 0<tau_safe<Q(1,108)
        assert 19*tau_safe<=Q(1,5)
        assert challenge+Q(107,108)**(limq-1)>Q(1,2**target)
        row['old_optimal_attained_q']=limq
        row['old_optimal_interior_tau']=str(tau_safe)
        row['exact_optimal_queries_saved']=limq-row['new_q']
        row['optimal_fraction_saved']=str(Q(limq-row['new_q'],limq))
    if row['old_q'] is not None:
        row['queries_saved']=row['old_q']-row['new_q']
        row['fraction_saved']=str(Q(row['queries_saved'],row['old_q']))
        row['saving_vs_best_old_limit_at_least']=limq-row['new_q']
    fixed_initial.append(row)

# Existing query ledger already prices full UDR; threshold port makes no numerical edit.
query_ledger=[]
for name,lb,q,pow_bits in [('ir2',6,19,16),('recursionCfg',3,38,14),
        ('prodV1',3,38,16),('lb2Drop',2,57,16),('zkdtvmCore',1,261,20)]:
    rho=Q(1,2**lb);B_old=(2+rho)/3;B_full=(1+rho)/2
    current=B_full**q/Q(2**pow_bits)
    # A counterfactual restricted-radius column, not the current ledger.
    restricted=B_old**q/Q(2**pow_bits)
    def q_for(B,target,pow_):
        return min_samples(B,Q(0),Q(2**pow_,2**target))
    query_ledger.append({'model':name,'log_blowup':lb,'q':q,'pow_bits':pow_bits,
        'rho':str(rho),'old_radius_open_ceiling':str(1-B_old),
        'full_radius_open_ceiling':str(1-B_full),
        'current_full_udr_bits':bits(current),'current_full_udr_floor_bits':floor_bits(current),
        'current_ledger_changed':False,'counterfactual_old_restricted_bits':bits(restricted),
        'q_for_100_current_udr':q_for(B_full,100,pow_bits),
        'q_for_100_counterfactual_old_radius':q_for(B_old,100,pow_bits),
        'endpoint_warning':'Consumer PG bands are strict; full-radius query ledger is a separate endpoint formula, not automatically the sampled tower tau.'})

# Radius does not change adversarial FS oracle work budget t in ErrorBudget.
# It also cannot turn the one-challenge bound into the m-round one for free.
result={'fixed':{'prime':P,'n':N,'degree':D,'adversarial_queries':T,'chain_depth':K,
                 'sumcheck_rounds':V,'sumcheck_degree':SC_D,'hash_queries':HASH_Q,'hash_bits':H},
        'algebra_models':algebra,'schedules':schedules,'sampled_tower':sampled,
        'existing_query_ledger':query_ledger,'fixed_initial_comparison':fixed_initial,
        'counts':{'web':0,'scry':0,'runtime_prover_benchmarks':0},
        'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
for filename,rows in [('sampled_tower.csv',sampled),('query_ledger.csv',query_ledger),('fixed_initial.csv',fixed_initial)]:
    keys=list(dict.fromkeys(k for row in rows for k in row))
    with (OUT/filename).open('w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=keys);w.writeheader();w.writerows(rows)
print('Algebraic models: delta 1/8 -> 1/5 leaves every error term unchanged')
for r in algebra: print(r['model'],r['floor_bits'],f"{r['total_bits']:.12f}",r['dominant_term'],r['target_met'])
print('Sampled tower: unchanged m*n/field + (1-tau)^q; old Delta3/10, new Delta2/5')
for r in sampled: print('m',r['rounds'],'ext',r['extension'],'target',r['target_bits'],
    'challenge_bits',f"{r['challenge_bits']:.12f}",'q_old',r['old_q'],'q_new',r['new_q'],
    'saved',r.get('queries_saved','impossible'))
print('Fair same-initial-radius Delta2/5 comparison, m19: tau_old1/109, tau_new1/95')
for r in fixed_initial: print('ext',r['extension'],'target',r['target_bits'],
    'q_old_interior',r['old_q'],'q_new',r['new_q'],'old_optimal',r.get('old_optimal_attained_q'),
    'optimal_saved',r.get('exact_optimal_queries_saved','impossible'))
print('Current UDR ledger already uses full radius: no change')
for r in query_ledger: print(r['model'],r['current_full_udr_floor_bits'],f"{r['current_full_udr_bits']:.12f}",
    '100-bit q full/restricted',r['q_for_100_current_udr'],r['q_for_100_counterfactual_old_radius'])
print('All minima verified exactly; preceding q fails. No source premise is asserted Lean-proved by this script.')
