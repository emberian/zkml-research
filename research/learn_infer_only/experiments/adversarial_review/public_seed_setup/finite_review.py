#!/usr/bin/env python3
"""Independent exhaustive finite public distributions, not a crypto experiment.

Only integer labels, finite tables, exact counts, and public source hashes.
No backend, ciphertext, recipient artifact, private file, CSPRNG, or network.
"""
from collections import Counter
from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import hashlib
import json

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
SOURCE=REPO/'research/learn_infer_only/experiments/private_construction/designated_span/public_coin_setup/public_seed'

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

assert sha(SOURCE/'PROPOSAL.md')=='ec9af914cb349e0bc6881bd8a5b99fd493e43b106a869a44eb58edf758083ab3'
manifest=json.loads((SOURCE/'MANIFEST.json').read_text())
for item in manifest['files']:
    assert sha(SOURCE/item['path'])==item['sha256']
deps=json.loads((SOURCE/'SOURCE_PINS.json').read_text())
for item in deps['files']:
    assert sha(Path(item['path']))==item['sha256']

p,q,g=7,3,2
gp=(1,2,4)
roots={b:tuple(u for u in range(1,p) if u*u%p==b) for b in gp}
assert all(set(roots[b])=={pow(b,(q+1)//2,p),-pow(b,(q+1)//2,p)%p} for b in gp)
deterministic_roots={pow(b,(q+1)//2,p) for b in gp}
assert len(deterministic_roots)==3 and len(set().union(*(set(v) for v in roots.values())))==6
assert (0+0)%q==(1+2)%q and (0,0)!=(1,2)
identity_one=Q(sum(u*u%p==1 for u in range(1,p)),p-1)
identity_two=Q(sum(u*u%p==1 or v*v%p==1 for u,v in product(range(1,p),repeat=2)),(p-1)**2)
assert identity_one==Q(1,3) and identity_two==Q(5,9)

def first(tape,allowed):
    return next((i for i,x in enumerate(tape) if x in allowed),None)

def program(tape,allowed,u):
    i=first(tape,allowed)
    if i is None:
        return tape
    return tape[:i]+(u,)+tape[i+1:]

# Check the finite-tape lemma for several acceptance-set shapes and caps,
# including an accepted zero, a rejected zero, and noninterval sets.
tape_cases=[]
for width,allowed in [(2,{0,1,2}),(3,{1,2,3,4,5,6}),(3,{0,3,7})]:
    for cap in (1,2,3):
        tapes=list(product(range(2**width),repeat=cap))
        mapped=Counter(program(w,allowed,u) for w in tapes for u in allowed)
        assert len(mapped)==len(tapes) and set(mapped.values())=={len(allowed)}
        failures=sum(first(w,allowed) is None for w in tapes)
        assert Q(failures,len(tapes))==Q(2**width-len(allowed),2**width)**cap
        tape_cases.append(dict(width=width,allowed=sorted(allowed),cap=cap,
            output_tapes=len(mapped),preimages_per_tape=len(allowed),
            failure_probability=str(Q(failures,len(tapes)))))

# Full rank two-row example Y=[1 0 1; 0 1 1]. The change of variables
# (s,tau,root-sign) <-> (a,tau,U) is bijective, including partial exposure.
rank2_real=Counter()
rank2_sim=Counter()
for a0,a1,t0,t1,u in product(range(q),range(q),range(q),range(q),range(1,p)):
    b=u*u%p
    h=(gp[(a0+t0)%q]*pow(b,-1,p)%p,
       gp[(a1+t1)%q]*pow(b,-1,p)%p,b)
    rank2_real[(a0,a1,t0,t1,u,h)]+=1
for s0,s1,s2,t0,t1 in product(range(q),repeat=5):
    h=(gp[s0],gp[s1],gp[s2])
    a0,a1=(s0+s2-t0)%q,(s1+s2-t1)%q
    for u in roots[h[2]]:
        rank2_sim[(a0,a1,t0,t1,u,h)]+=1
assert rank2_real==rank2_sim and len(rank2_real)==486
# Conditional product uniformity after revealing full A and a single scalar.
conditional=Counter((gp[a0],gp[a1],a0,t0,t1,u) for a0,a1,t0,t1,u,h in rank2_sim)
assert len(conditional)==486 and set(conditional.values())=={1}

# Reproduce the original cap-two m=1,n=1 full transcript with a separate loop.
raw_tau=list(product(range(4),repeat=2))
raw_u=list(product(range(8),repeat=2))
full=Counter()
success_count=0
for a,t,u in product(range(q),range(q),range(1,p)):
    b=u*u%p
    supplied_h=(gp[(a+t)%q]*pow(b,-1,p)%p,b)
    for tw,uw in product(raw_tau,raw_u):
        tx=program(tw,{0,1,2},t)
        ux=program(uw,{1,2,3,4,5,6},u)
        full[(a,tx,ux)]+=1
        ti,ui=first(tx,{0,1,2}),first(ux,{1,2,3,4,5,6})
        if ti is not None and ui is not None:
            bb=ux[ui]*ux[ui]%p
            assert (gp[(a+tx[ti])%q]*pow(bb,-1,p)%p,bb)==supplied_h
            success_count+=1
assert len(full)==3072 and set(full.values())=={18}
assert Q(success_count,sum(full.values()))==Q(225,256)

# Adversarial ordering experiment: three seed labels, cap one, N=4 padding.
# Query U of seed0 first; that answer chooses which of seed1/seed2 is touched
# next. Complete those two candidates. Prefer an identity-bearing first
# candidate; otherwise use successful second candidate; otherwise SELECT the
# remaining unqueried seed and let verification create ordinal three.
# Compare the complete selected-success transcript law for every guessed
# first-touch ordinal. This is a finite coupling check, with no LR ciphertexts.
raw_pairs=tuple(product(range(4),range(8)))
raw_triples=tuple(product(raw_pairs,repeat=3))

def run(raw, a, guess=None, target=None):
    initialized={}
    order=[]
    trace=[]
    def query(seed,role):
        if seed not in initialized:
            order.append(seed)
            t,u=raw[seed]
            if len(order)==guess:
                assert target is not None
                if t<3:
                    t=target[0]
                if 1<=u<7:
                    u=target[1]
            initialized[seed]=(t,u)
        result=initialized[seed][role]
        trace.append((seed,role,result))
        return result
    u0=query(0,1)
    second=1+(u0%2)
    t2=query(second,0)
    u2=query(second,1)
    t0=query(0,0)
    ok0=t0<3 and 1<=u0<7
    ok2=t2<3 and 1<=u2<7
    if ok0 and u0*u0%p==1:
        selected=0
    elif ok2:
        selected=second
    else:
        selected=3-second
        query(selected,1)
        query(selected,0)
    ordinal=order.index(selected)+1
    t,u=initialized[selected]
    ok=t<3 and 1<=u<7
    if not ok:
        return ordinal,None
    b=u*u%p
    h=(gp[(a+t)%q]*pow(b,-1,p)%p,b)
    if guess==ordinal:
        tb=target[1]*target[1]%p
        assert h==(gp[(a+target[0])%q]*pow(tb,-1,p)%p,tb)
    # Expose the entire small recipient scalar, so coalition disclosure is
    # included. h is deterministic from the recorded selected raw words.
    return ordinal,(a,gp[a],tuple(trace),selected,h)

real_events=[Counter() for _ in range(4)]
real_fail=Counter()
for a in range(q):
    for raw in raw_triples:
        ordinal,view=run(raw,a)
        if view is None:
            real_fail[ordinal]+=1
        else:
            real_events[ordinal-1][view]+=1

event_checks=[]
for guess in (1,2,3):
    sim_events=Counter()
    for a,t,u in product(range(q),range(q),range(1,p)):
        for raw in raw_triples:
            ordinal,view=run(raw,a,guess,(t,u))
            if ordinal==guess and view is not None:
                sim_events[view]+=1
    expected=Counter({view:count*18 for view,count in real_events[guess-1].items()})
    assert sim_events==expected
    event_checks.append(dict(guessed_ordinal=guess,real_success_count=sum(real_events[guess-1].values()),
        matched_transcript_atoms=len(sim_events),simulator_preimage_factor=18,
        exact_selected_event_identity=True))
assert not real_events[3]
denominator=q*len(raw_triples)
successful=sum(sum(c.values()) for c in real_events)
assert successful+sum(real_fail.values())==denominator
assert all(x['real_success_count']>0 for x in event_checks)

# Exact independence/union-bound control for pre-registration complete keys.
# Distinct guesses can reach Qpre/q^m; duplicate guesses never improve it.
prequery=[]
registries=tuple(product(range(q),repeat=2))
for count in (0,1,3,9,12):
    guesses=[registries[i%len(registries)] for i in range(count)]
    hits=sum(a in guesses for a in registries)
    assert Q(hits,len(registries))<=min(Q(1),Q(count,q**2))
    prequery.append(dict(m=2,q=q,queries=count,exact_bad_probability=str(Q(hits,len(registries))),
                         bound=str(min(Q(1),Q(count,q**2)))))

result=dict(status='PASS; finite public distribution checks only',
    proposal_sha256=sha(SOURCE/'PROPOSAL.md'),script_sha256=sha(Path(__file__)),
    finite_tape_cases=tape_cases,rank_two_joint_atoms=486,
    cap_two_registry_tapes=len(full),cap_two_choices=sum(full.values()),
    cap_two_preimages_per_transcript=18,cap_two_failure='31/256',
    adaptive_three_seed_experiment=dict(p=p,q=q,m=1,d=2,cap=1,padded_N=4,
        real_random_choices=denominator,real_successes=successful,failures=dict(real_fail),
        checks=event_checks,padded_ordinal4_always_aborts=True,
        selected_event_probability_sum=str(Q(successful,denominator)),
        average_guess_success_probability=str(Q(successful,denominator*4))),
    prequery_checks=prequery,identity_one_seed=str(identity_one),identity_two_seed_selection=str(identity_two),
    deterministic_root_support=len(deterministic_roots),random_sign_root_support=6,
    distinct_equal_projection_witness=[[0,0],[1,2]],
    source_script_executed=False,new_crypto_runs=0,private_files_read=0,web_queries=0)
(HERE/'finite_results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
