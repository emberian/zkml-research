#!/usr/bin/env python3
"""Replay a saved proof once through the instrumented actual verifier; no proving/teaching."""
import collections, hashlib, json, os, pathlib, resource, signal, subprocess, sys, time
if not __debug__: raise RuntimeError('acceptance bridge requires assertions; Python -O is unsupported')
HERE=pathlib.Path(__file__).resolve().parent
QUERY=HERE.parent
VFHE=QUERY.parent
CANONICAL_QUERY_TEMPLATE='f42c5efcaa994656b0c9ef2d1270aa2d6eb7dae0e5ba85938d23dbb3dc46c10d'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def dump(p,v): p.write_text(json.dumps(v,indent=2,sort_keys=True)+'\n')
def canonical_profile(summary,events,template_sha):
    """Stronger, explicitly fixed-template admission; not an old-verifier soundness claim."""
    assert template_sha==CANONICAL_QUERY_TEMPLATE,'unsupported canonical template'
    assert summary['parameters']=={'log_blowup':3,'log_final_poly_len':0,'max_log_arity':3,'num_queries':38,'commit_pow_bits':0,'query_pow_bits':16}
    schedule=summary['schedule']
    assert schedule['input_log_heights']==[17] and schedule['log_global_max_height']==17
    assert schedule['extra_query_index_bits']==0
    assert schedule['actual_log_arities']==schedule['canonical_log_arities']==[3,3,3,3,2]
    assert all(summary['canonical_predicates'][k] for k in ['schedule_matches_public_height_scheduler','all_salt_rows_exactly_four','input_widths_match_claims','all_native_fold_bindings_and_terminal_equalities'])
    by=collections.defaultdict(list)
    for e in events:by[e['kind']].append(e['data'])
    assert not by['fri_injection'],'unsupported cross-height injection profile'
    before=by['hiding_claims_before_merge'][0]
    after=by['pcs_claims'][0]['batches']
    declared_widths=[[8,8],[2513,5],[8]*16,[59],[8,8]]
    point_counts=[1,2,1,1,2]
    assert len(before['batches'])==len(before['random_codeword_openings'])==len(after)==5
    for b,(batch,old,rand,widths) in enumerate(zip(after,before['batches'],before['random_codeword_openings'],declared_widths)):
        assert len(batch['matrices'])==len(old['matrices'])==len(rand)==len(widths)
        assert old['root']==batch['root']
        expected_rand=0 if b==3 else 4
        for new_m,old_m,rand_m,w in zip(batch['matrices'],old['matrices'],rand,widths):
            assert new_m['log_domain_size']==old_m['log_domain_size']==14
            assert new_m['domain_shift']==old_m['domain_shift']
            assert len(new_m['points_and_values'])==len(old_m['points_and_values'])==len(rand_m)==point_counts[b]
            for new_p,old_p,rand_p in zip(new_m['points_and_values'],old_m['points_and_values'],rand_m):
                assert new_p[0]==old_p[0]
                assert len(rand_p)==expected_rand and len(old_p[1])==w-expected_rand
                assert new_p[1]==old_p[1]+rand_p and len(new_p[1])==w
    return {'profile':'fixed-ir2-whole-query-canonical-v1','template_sha256':template_sha,
            'native_verification_required':True,'input_log_height':17,'log_arities':[3,3,3,3,2],
            'declared_base_widths':declared_widths,'random_codewords_per_matrix':4,'public_preprocessing_random_codewords':0,
            'salt_words_per_matrix':4,'passed':True}
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
        'field':{'prime':2013265921,'extension_degree':4,'extension_polynomial':'X^4 - 11','encoding':'native serde: Montgomery base words, R=2^32; extension object value holds four ascending power-basis Montgomery words; raw_base_word from sample_bits is already canonical'},
        'scope':'Original verifier acceptance with instrumentation. Canonical predicates are additional observed facts, not guards in the original verifier or a general soundness theorem.'}
def main():
    args=sys.argv[1:]
    canonical=bool(args and args[0]=='--canonical')
    if canonical:args=args[1:]
    if len(args)!=4: raise SystemExit('usage: run.py [--canonical] TEMPLATE CASE PROOF NEW_OUT')
    template,case,proof,out=map(lambda x:pathlib.Path(x).resolve(),args)
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
    if canonical:
        summary['canonical_admission']=canonical_profile(summary,events,watched[str(template)])
        summary['canonical_admission']['fresh_native_verification_in_this_invocation']=True
    summary['admission_mode']='canonical-fixed-query' if canonical else 'native-instrumentation'
    summary.update({'native_acceptance':accepted,'command_sha256':sha(out/'command.json'),'events_sha256':sha(out/'events.jsonl'),'source_and_input_posthash_match':True})
    dump(out/'accepted.json',summary)
    print(json.dumps({'accepted':True,'wall_seconds':wall,'schedule':summary['schedule'],'event_counts':summary['event_counts'],'canonical_predicates':summary['canonical_predicates']}))
if __name__=='__main__':main()
