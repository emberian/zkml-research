#!/usr/bin/env python3
"""Decode the native accepted event stream into explicit canonical field/packed-query events.

This consumes the saved stream only. It does not run the prover or verifier again.
The small Lagrange calculation checks the representation bridge, not STARK soundness.
"""
import collections, hashlib, json, pathlib, sys
P=2013265921
RINV=pow(2**32,-1,P)
HERE=pathlib.Path(__file__).resolve().parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def bf(x):
    assert type(x) is int and 0<=x<P
    return x*RINV%P
def ef(x):
    assert set(x)=={'_phantom','value'} and x['_phantom'] is None and len(x['value'])==4
    return [bf(c) for c in x['value']]
def root(x):
    assert set(x)=={'_marker','cap'} and x['_marker'] is None
    assert all(len(r)==8 for r in x['cap'])
    return [[bf(c) for c in r] for r in x['cap']]
def opening(x):
    salts,path=x
    return {'salts':[[bf(c) for c in s] for s in salts],'siblings':[[bf(c) for c in h] for h in path]}
def points(x):return [{'point':ef(z),'values':[ef(v) for v in vs]} for z,vs in x]
def add(a,b):return [(x+y)%P for x,y in zip(a,b)]
def mul(a,b):
    r=[0]*7
    for i,x in enumerate(a):
        for j,y in enumerate(b):r[i+j]+=x*y
    for i in range(6,3,-1):r[i-4]+=11*r[i]
    return [x%P for x in r[:4]]
def lagrange(xs,ys,beta):
    result=[0]*4
    for i,(x,y) in enumerate(zip(xs,ys)):
        term=[1,0,0,0];den=1
        for j,z in enumerate(xs):
            if i!=j:
                term=mul(term,[(beta[0]-z)%P,*beta[1:]])
                den=den*(x-z)%P
        result=add(result,mul(y,[v*pow(den,-1,P)%P for v in term]))
    return result
def main():
    if len(sys.argv)!=2:raise SystemExit('usage: project.py ACCEPTED_REPLAY_DIR')
    d=pathlib.Path(sys.argv[1]).resolve()
    ev=[json.loads(s) for s in (d/'events.jsonl').read_text().splitlines()]
    acceptance=json.loads((d/'accepted.json').read_text())
    assert sha(d/'events.jsonl')==acceptance['events_sha256'] and acceptance['native_acceptance']['verified']
    by=collections.defaultdict(list)
    for e in ev:by[e['kind']].append(e)
    data=lambda k:by[k][0]['data']
    transcript=[]
    for e in ev:
        k,v=e['kind'],e['data']
        if k in ['transcript_observe','transcript_sample']:
            value=v['value']
            converted=bf(value) if type(value) is int else root(value) if 'cap' in value else ef(value)
            transcript.append({'seq':e['seq'],'operation':k,'rust_type':v['rust_type'],'canonical_value':converted})
        elif k=='transcript_sample_bits':transcript.append({'seq':e['seq'],'operation':k,**v})
    batches=[]
    for b in data('pcs_claims')['batches']:
        batches.append({'root':root(b['root']),'matrices':[{'log_domain_size':m['log_domain_size'],'domain_shift':bf(m['domain_shift']),'points_and_values':points(m['points_and_values'])} for m in b['matrices']]})
    queries=[];q=None;current_input=None;current_round=None;folds_checked=0
    for e in ev:
        k,v=e['kind'],e['data']
        if k=='fri_query':
            q={'query':v['query'],'index':v['index'],'input_batches':[],'input_reductions':[],'rounds':[]}
            queries.append(q)
        elif k=='input_batch_verified':
            current_input={'batch':v['batch'],'root':root(v['root']),'heights':v['heights'],'reduced_index':v['reduced_index'],'rows':[[bf(x) for x in row] for row in v['opened_values']],**opening(v['opening_proof'])}
            q['input_batches'].append(current_input)
        elif k=='input_matrix':
            q['input_reductions'].append({**{a:v[a] for a in ['batch','matrix','log_height','width','index','reversed_index']},'x':bf(v['x']),'alpha_power_start':ef(v['alpha_power_start']),'reduced_opening_start':ef(v['reduced_opening_start'])})
        elif k=='input_matrix_reduced':
            q['input_reductions'][-1].update(alpha_power_end=ef(v['alpha_power_end']),reduced_opening_end=ef(v['reduced_opening_end']))
        elif k=='fri_reduced_openings':q['reduced_openings']=[{'log_height':h,'value':ef(x)} for h,x in v['values']]
        elif k=='fri_packed_row_verified':
            current_round={**{a:v[a] for a in ['round','log_current_height','log_folded_height','extension_width','base_width','index_in_group','parent_index']},'root':root(v['commitment']),'evals':[ef(x) for x in v['evals']],'beta':ef(v['beta']),**opening(v['opening_proof'])}
            # The real MMCS leaf is these base coefficients in this order, followed by its salt.
            current_round['salted_packed_leaf']=[c for x in current_round['evals'] for c in x]+current_round['salts'][0]
            q['rounds'].append(current_round)
        elif k=='native_fold':
            current_round.update(xs=[bf(x) for x in v['xs']],subgroup_start=bf(v['subgroup_start']),fold_result=ef(v['result']))
            assert current_round['fold_result']==lagrange(current_round['xs'],current_round['evals'],current_round['beta'])
            folds_checked+=1
        elif k=='fri_injection':current_round['injection']={'log_height':v['log_height'],'reduced_opening':ef(v['reduced_opening']),'beta_power':ef(v['beta_power']),'after_injection':ef(v['after_injection'])}
        elif k=='fri_round_carried':current_round['carried_value']=ef(v['value'])
        elif k=='fri_terminal_check':q['terminal']={'index':v['domain_index'],'x':bf(v['x']),'evaluation':ef(v['evaluation']),'folded_eval':ef(v['folded_eval']),'equal':v['equal']}
    samples=[e for e in transcript if e['operation']=='transcript_sample_bits'][1:]
    for q,s in zip(queries,samples):
        q['raw_base_word']=s['raw_base_word']
        previous=q['reduced_openings'][0]['value'];index=q['index']
        for r in q['rounds']:
            assert r['index_in_group']==index%r['extension_width']
            assert r['evals'][r['index_in_group']]==previous
            index//=r['extension_width'];assert r['parent_index']==index
            previous=r['carried_value']
        assert q['terminal']['evaluation']==previous
    proof_source=pathlib.Path('/Users/ember/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7')
    relevant=[proof_source/'monty-31/src/monty_31.rs',proof_source/'baby-bear/src/baby_bear.rs',proof_source/'commit/src/adapters/extension_mmcs.rs',proof_source/'merkle-tree/src/hiding_mmcs.rs',proof_source/'merkle-tree/src/mmcs.rs']
    view={'schema':'ir2-accepted-fri-packed-events-v1','native_events_sha256':sha(d/'events.jsonl'),'native_acceptance':acceptance['native_acceptance'],
        'field':{'prime':P,'extension_polynomial':'X^4-11','extension_basis':'1,X,X^2,X^3','encoding':'All field elements in this projection are canonical residues. Raw events use Montgomery words except sample_bits.raw_base_word.','montgomery_R':2**32,'montgomery_inverse':RINV},
        'parameters':data('fri_begin'),'schedule':data('fri_schedule'),'batches':batches,
        'alpha':ef(data('fri_alpha')['alpha']),'betas':[ef(e['data']['beta']) for e in by['fri_beta']],
        'fri_roots':[root(e['data']['commitment']) for e in by['fri_commit_observe']],
        'final_polynomial':[ef(x) for x in data('fri_final_poly_observe')['coefficients']],
        'transcript':transcript,'queries':queries,
        'representation_checks':{'decoded_lagrange_folds':folds_checked,'carry_index_chains':len(queries),'passed':True},
        'source_locations_observed_after_replay':{str(p):sha(p) for p in relevant},
        'limits':'An accepted execution projection, not a soundness theorem. Canonical schedule and salt shape are observed, not enforced by the original verifier. No Merkle binding, random-oracle independence or scalar-to-packed theorem is assumed.'}
    out=d/'fri_view.json';assert not out.exists()
    out.write_text(json.dumps(view,separators=(',',':'))+'\n')
    print(json.dumps({'output':str(out),'sha256':sha(out),'bytes':out.stat().st_size,'decoded_lagrange_folds':folds_checked,'queries':len(queries)}))
if __name__=='__main__':main()
