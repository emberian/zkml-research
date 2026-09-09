#!/usr/bin/env python3
"""Replay a saved proof once through the instrumented actual verifier; no proving/teaching."""
import collections, hashlib, json, os, pathlib, resource, signal, subprocess, sys, time
HERE=pathlib.Path(__file__).resolve().parent
QUERY=HERE.parent
VFHE=QUERY.parent
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,v): p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
def collect(events):
    assert [e['seq'] for e in events]==list(range(len(events)))
    by=collections.defaultdict(list)
    for e in events: by[e['kind']].append(e['data'])
    assert len(by['fri_begin'])==len(by['fri_schedule'])==len(by['pcs_claims'])==1
    params=by['fri_begin'][0]; schedule=by['fri_schedule'][0]
    queries=by['fri_query']; rounds=len(schedule['actual_log_arities'])
    assert len(queries)==params['num_queries']==38
    assert [q['query'] for q in queries]==list(range(38))
    assert len(by['fri_terminal_check'])==38 and all(x['equal'] for x in by['fri_terminal_check'])
    for k in ['fri_packed_row_verified','native_fold','fri_fold_result','fri_round_carried']:
        assert len(by[k])==38*rounds,k
    bit_samples=by['transcript_sample_bits']
    # The only preceding bits draw is query PoW; commit PoW=0 consumes nothing.
    assert len(bit_samples)==39 and bit_samples[0]['bits']==16 and bit_samples[0]['index']==0
    for q,b in zip(queries,bit_samples[1:]):
        assert b['bits']==schedule['log_global_max_height'] and b['index']==q['index']
        assert b['index']==b['raw_base_word']%2**b['bits']
    salts=[];matrix_shapes=[]
    batches=by['pcs_claims'][0]['batches']
    for e in by['input_batch_verified']:
        salt_rows,path=e['opening_proof']
        assert len(salt_rows)==len(e['opened_values'])==len(e['heights'])
        assert e['root']==batches[e['batch']]['root']
        for j,(row,salt,h) in enumerate(zip(e['opened_values'],salt_rows,e['heights'])):
            m=batches[e['batch']]['matrices'][j]
            assert h==2**(m['log_domain_size']+params['log_blowup'])
            assert all(len(pv[1])==len(row) for pv in m['points_and_values'])
            salts.append(len(salt))
        assert len(path)==max(e['heights']).bit_length()-1
    for e,native,fold,carried in zip(by['fri_packed_row_verified'],by['native_fold'],by['fri_fold_result'],by['fri_round_carried']):
        salt_rows,path=e['opening_proof']
        assert len(salt_rows)==1
        salts.append(len(salt_rows[0]))
        assert e['extension_width']==len(e['evals'])==2**native['log_arity']
        assert e['base_width']==4*len(e['evals'])
        assert e['evals']==native['evals'] and e['beta']==native['beta']
        assert native['result']==fold['before_injection']
        assert native['parent_index']==e['parent_index']==carried['index']
        assert len(path)==e['log_folded_height']
    for b,batch in enumerate(batches):
        for m,mat in enumerate(batch['matrices']):
            matrix_shapes.append({'batch':b,'matrix':m,'log_domain_size':mat['log_domain_size'],'lde_height':2**(mat['log_domain_size']+params['log_blowup']),'width_base':len(mat['points_and_values'][0][1]),'opening_points':len(mat['points_and_values']),'domain_shift':mat['domain_shift'],'root':batch['root']})
    return {'parameters':params,'schedule':schedule,'input_matrix_shapes':matrix_shapes,
        'queries':[dict(q,raw_base_word=b['raw_base_word']) for q,b in zip(queries,bit_samples[1:])],
        'event_counts':dict(collections.Counter(e['kind'] for e in events)),
        'canonical_predicates':{'schedule_matches_public_height_scheduler':schedule['canonical_schedule_matches'],'all_salt_rows_exactly_four':all(n==4 for n in salts),'salt_rows_checked':len(salts),'input_widths_match_claims':True,'all_native_fold_bindings_and_terminal_equalities':True},
        'field':{'prime':2013265921,'extension_degree':4,'extension_polynomial':'X^4 - 11','encoding':'canonical base residues; extension arrays in ascending power basis'},
        'scope':'Original verifier acceptance with instrumentation. Canonical predicates are additional observed facts, not guards in the original verifier or a general soundness theorem.'}
def main():
    if len(sys.argv)!=5: raise SystemExit('usage: run.py TEMPLATE CASE PROOF NEW_OUT')
    template,case,proof,out=map(lambda x:pathlib.Path(x).resolve(),sys.argv[1:])
    out.mkdir(parents=True,exist_ok=False)
    binary=QUERY/'target/release/vfhe-acceptance-bridge'
    sources=json.loads((HERE/'build_inputs.json').read_text())
    watched={str(p):sha(p) for p in [binary,template,proof,case/'acc.ct',case/'query.json',case/'out.ct',QUERY/'Cargo.lock',QUERY/'Cargo.toml',HERE/'events.rs',HERE/'challenger.rs',HERE/'build.py',HERE/'run.py',HERE/'instrumentation.patch']}
    watched.update(sources['source_sha256'])
    watched[sources['query_source']['path']]=sources['query_source']['sha256']
    assert all(sha(pathlib.Path(p))==h for p,h in watched.items()),'source changed after build'
    cmd=[str(binary),str(template),str(case),str(proof)]
    start=time.time();t=time.monotonic()
    with (out/'stdout.jsonl').open('w') as stdout,(out/'events.jsonl').open('w') as stderr:
        proc=subprocess.Popen(cmd,stdout=stdout,stderr=stderr,start_new_session=True,env=dict(os.environ,RAYON_NUM_THREADS='4'))
        try: code=proc.wait(timeout=300)
        except BaseException:
            os.killpg(proc.pid,signal.SIGKILL);proc.wait();raise
    wall=time.monotonic()-t;usage=resource.getrusage(resource.RUSAGE_CHILDREN)
    result={'argv':cmd,'exit_code':code,'start_unix':start,'wall_seconds':wall,'user_seconds':usage.ru_utime,'system_seconds':usage.ru_stime,'max_rss_bytes':usage.ru_maxrss if sys.platform=='darwin' else usage.ru_maxrss*1024,'explicit_policy':{'RAYON_NUM_THREADS':'4'},'input_sha256':watched}
    dump(out/'command.json',result)
    assert code==0,'actual verifier rejected; no acceptance export'
    accepted=json.loads((out/'stdout.jsonl').read_text());assert accepted['verified'] is True
    assert accepted['proof_sha256']==watched[str(proof)]
    assert all(sha(pathlib.Path(p))==h for p,h in watched.items()),'source/input changed during replay'
    events=[json.loads(s) for s in (out/'events.jsonl').read_text().splitlines()]
    summary=collect(events)
    summary.update({'native_acceptance':accepted,'command_sha256':sha(out/'command.json'),'events_sha256':sha(out/'events.jsonl'),'source_and_input_posthash_match':True})
    dump(out/'accepted.json',summary)
    print(json.dumps({'accepted':True,'wall_seconds':wall,'schedule':summary['schedule'],'event_counts':summary['event_counts'],'canonical_predicates':summary['canonical_predicates']}))
if __name__=='__main__':main()
