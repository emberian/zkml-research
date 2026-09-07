"""Map the complete frozen fixture to issuer/oracle-only text and exact scores.

No model execution, training, fixture edits or outcome-based selection. This
script uses only stdlib and independently replays the signed integer window.
"""
from collections import defaultdict,deque
from pathlib import Path
import hashlib,json,shutil

ROOT=Path(__file__).resolve().parent
BASE=ROOT.parents[1]/'adaptation_utility'
ENC=BASE/'encrypted_window'
FIXTURE_SHA='41978a10b974a3e8b7f30d5f9c66f7d396fdf7df83b723b3f14dc00359cdb4c0'
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text())
canonical=lambda x:json.dumps(x,sort_keys=True,separators=(',',':'))
vdigest=lambda x:hashlib.sha256(canonical(x).encode()).hexdigest()
save=lambda p,x:Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
SKILLS={0:'plant categorization',1:'letter categorization'}
PHASES={1:'teach plant rule',2:'teach independent letter rule',3:'reverse plant rule'}

def main():
    assert sha(ENC/'fixture.txt')==FIXTURE_SHA
    assert (ROOT/'TRANSCRIPT_SELECTION.md').is_file()
    records=load(BASE/'representation_records.json')
    histories={h['seed']:h for h in load(BASE/'representation_histories.json')['groups']['test']}
    selected=load(BASE/'representation_selection.json')
    assert selected['chosen_representation_by_method']['model_window_routed']=='mean_10'
    assert selected['choices']['mean_10/model_window_routed']['configuration']=={'capacity':64}
    queryids=sorted(i for s in [0,1] for a in [0,1] for b in [0,1]
      for i in sorted(r['id'] for r in records if r['pool']=='test' and (r['skill'],r['a'],r['b'])==(s,a,b))[:2])
    assert queryids==[256,257,272,273,288,289,304,305,320,321,336,337,352,353,368,369]
    events=[];checkpoints=[];public=[];learns=[];queries=[];route_states={};seen_seeds=[]
    def target(r,phase):
        value=histories[seed]['rules'][r['skill']][2*r['a']+r['b']]
        return -value if phase==3 and r['skill']==0 else value
    lines=(ENC/'fixture.txt').read_text().splitlines()
    assert lines[0]=='Q83_WINDOW_V1 577 32 2'
    for line_number,line in enumerate(lines[1:],2):
        fields=line.split();kind=fields[0]
        if kind=='H':
            seed,coins=map(int,fields[1:]);assert seed in [63000,63001]
            seen_seeds.append(seed);ordinal=0;state=[[0]*577 for _ in range(2)];queue=[deque(),deque()]
        elif kind in ['L','Q']:
            assert len(fields)==583
            phase,number,route,one,two=map(int,fields[1:6]);vector=list(map(int,fields[6:]))
            assert all(-127<=v<=127 for v in vector)
            ordinal+=1;event_id=f'h{len(seen_seeds)-1}-e{ordinal:04d}'
            if kind=='L':
                step,rid,label=number,one,two;r=records[rid]
                assert rid==histories[seed]['phases'][phase-1][(step-1)%64]
                assert r['pool']=='teach' and r['skill']==route and label==target(r,phase)
                queue[route].append((event_id,rid,vector))
                state[route]=[x+y for x,y in zip(state[route],vector)]
                expired=None
                if len(queue[route])>32:
                    old_id,old_rid,old=queue[route].popleft();expired={'event_id':old_id,'record_id':old_rid}
                    state[route]=[x-y for x,y in zip(state[route],old)]
                entry={'kind':'Learn','step':step,'record_id':rid,'observed_label':label,
                  'contribution_sha256':vdigest(vector),'vector_length':577,
                  'queued_count_after':len(queue[route]),'expired_original_contribution':expired}
                learns.append(entry)
            else:
                rid,score,label=number,one,two;r=records[rid]
                assert r['pool']=='test' and r['skill']==route and rid in queryids and label==target(r,phase)
                expected=sum(x*y for x,y in zip(state[route],vector));assert score==expected
                prediction=1 if score>=0 else -1
                entry={'kind':'Infer','record_id':rid,'learn_steps_so_far':phase*64,
                  'query_vector_sha256':vdigest(vector),'vector_length':577,
                  'expected_score':score,'expected_sign':prediction,'target_label':label,'correct':prediction==label,
                  'public_structural_zero':len(queue[route])==0,'queued_count':len(queue[route])}
                queries.append(entry)
            entry.update(event_id=event_id,history_seed=seed,history_index=len(seen_seeds)-1,event_ordinal=ordinal,
              phase=phase,phase_name=PHASES[phase],route=route,skill_name=SKILLS[route],
              source_fixture_line=line_number,source_fixture_line_sha256=hashlib.sha256((line+'\n').encode()).hexdigest(),
              source_record=r)
            events.append(entry)
            # No source record IDs/text, labels, expected values, vector hashes,
            # fixture path or plaintext mapping path enters this host-safe index.
            public.append({'event_id':event_id,'history_index':len(seen_seeds)-1,'event_ordinal':ordinal,
                           'kind':entry['kind'],'route':route})
        elif kind=='P':
            assert len(fields)==581
            phase,route,count=map(int,fields[1:4]);values=list(map(int,fields[4:]))
            assert values==state[route] and count==len(queue[route])
            checkpoints.append({'history_seed':seed,'phase':phase,'route':route,'queue_count':count,
                'state_sha256':vdigest(values),'source_fixture_line':line_number})
            route_states[(seed,phase,route)]=values
        elif kind=='END':assert ordinal==240
        else:raise AssertionError(kind)
    assert seen_seeds==[63000,63001] and len(learns)==384 and len(queries)==96 and len(events)==480
    assert len({e['event_id'] for e in events})==480
    for seed in seen_seeds:
        for phase in [1,2,3]:assert sorted(q['record_id'] for q in queries if q['history_seed']==seed and q['phase']==phase)==queryids
        assert route_states[(seed,1,0)]==route_states[(seed,2,0)]
        assert route_states[(seed,2,1)]==route_states[(seed,3,1)]
    nonempty=[q for q in queries if not q['public_structural_zero']]
    assert len(nonempty)==80
    def stats(qs):
        return {'correct':sum(q['correct'] for q in qs),'count':len(qs),'accuracy':sum(q['correct'] for q in qs)/len(qs)}
    breakdown=[]
    for seed in seen_seeds:
        for phase in [1,2,3]:
            for route in [0,1]:
                qs=[q for q in queries if (q['history_seed'],q['phase'],q['route'])==(seed,phase,route)]
                breakdown.append({'history_seed':seed,'phase':phase,'phase_name':PHASES[phase],'route':route,
                  'public_structural_zero':all(q['public_structural_zero'] for q in qs),**stats(qs)})
    original=load(BASE/'representation_results.json')['results']['mean_10/model_window_routed']
    summary={'scope':'Descriptive fixed-subset arithmetic/oracle summary; no new population utility estimate',
       'all_selected_queries':stats(queries),'nonempty_encrypted_queries':stats(nonempty),
       'public_structural_zero_queries':stats([q for q in queries if q['public_structural_zero']]),
       'final_queries':stats([q for q in queries if q['phase']==3]),'phase_skill_history':breakdown,
       'phase_combined':[{'phase':p,**stats([q for q in queries if q['phase']==p])} for p in [1,2,3]],
       'retention_state_equalities':4,'original_32_history_result':original,
       'sign_tie_convention':'score >= 0 maps to +1; otherwise -1',
       'teaching_events':384,'selected_queries':96,'nonempty_encrypted_query_count':80,'empty_route_query_count':16}
    payload={'schema':'E2E_ISSUER_ORACLE_METADATA_V1','exposure':'PLAINTEXT: issuer/test-oracle only; never host/authority input or public log',
      'fixture_sha256':FIXTURE_SHA,'capacity_per_route':32,'dimension':577,'selected_query_ids':queryids,
      'events':events,'checkpoints':checkpoints,
      'histories':[{'seed':s,'rules':histories[s]['rules'],'phase_order':[PHASES[p] for p in [1,2,3]]} for s in seen_seeds]}
    private=ROOT/'issuer_oracle';private.mkdir(exist_ok=True)
    save(private/'mapping.json',payload);save(private/'summary.json',summary)
    save(ROOT/'public_event_index.json',{'schema':'E2E_OPAQUE_EVENT_INDEX_V1','events':public})
    # Complete human-readable teaching and query denominators, one compact file
    # per history. These remain explicitly plaintext issuer/oracle artifacts.
    for seed in seen_seeds:
        text=[f'# Complete plaintext issuer/oracle transcript: history {seed}',
          '', '[EXECUTED from frozen source] All192 teaching events and all48 preselected queries follow.',
          'This is an owner-facing analysis artifact; it must not enter host/authority inputs or public logs.',
          'Category labels are arbitrary synthetic binary rules, not horticultural or social advice.',
          'Scores below are the frozen exact-integer oracle; this file does not claim a new E2E run.', '']
        for phase in [1,2,3]:
            text += [f'## Phase {phase}: {PHASES[phase]}','','| Learn step | Record | Label | Original teaching text | Vector SHA256 prefix |','|---:|---:|---:|---|---|']
            for e in learns:
                if e['history_seed']==seed and e['phase']==phase:
                    text.append(f"| {e['step']} | {e['record_id']} | {e['observed_label']:+d} | {e['source_record']['text']} | {e['contribution_sha256'][:16]} |")
            text += ['','| Query event | Record / skill | Original held-out text | Score | Sign | Target | Correct |','|---|---|---|---:|---:|---:|---|']
            for e in queries:
                if e['history_seed']==seed and e['phase']==phase:
                    text.append(f"| {e['event_id']} | {e['record_id']} / {e['route']} | {e['source_record']['text']} | {e['expected_score']} | {e['expected_sign']:+d} | {e['target_label']:+d} | {'yes' if e['correct'] else 'no'} |")
            text+=['']
        (private/f'transcript_{seed}.md').write_text('\n'.join(text)+'\n')
    chosen=[e for e in events if e['history_seed']==63000 and ((e['kind']=='Learn' and e['record_id'] in [0,64]) or (e['kind']=='Infer' and e['record_id'] in [256,320]))]
    save(private/'illustrative_sequence.json',{'selection':'TRANSCRIPT_SELECTION.md','events':chosen})
    prereg=ROOT/'original_preregistrations';prereg.mkdir(exist_ok=True)
    for source,target_name in [(BASE/'representation_PROTOCOL.md','representation_PROTOCOL.md'),(ENC/'PREREGISTRATION.md','encrypted_window_PREREGISTRATION.md')]:
        shutil.copyfile(source,prereg/target_name)
    sources=[ENC/'fixture.txt',ENC/'fixture_manifest.json',ENC/'PREREGISTRATION.md',ENC/'results.json',
      BASE/'representation_PROTOCOL.md',BASE/'representation_records.json',BASE/'representation_histories.json',
      BASE/'representation_selection.json',BASE/'representation_results.json',BASE/'representation_features.npz',
      BASE/'representation_model_manifest.json',BASE/'model_manifest.json',BASE/'representation_data.py',
      BASE/'text_transfer_data.py',BASE/'representation_controls.py',BASE/'representation_extract.py',BASE/'requirements-lock.txt',
      ROOT/'TRANSCRIPT_SELECTION.md',Path(__file__)]
    outputs=[private/'mapping.json',private/'summary.json',private/'illustrative_sequence.json',ROOT/'public_event_index.json',
       *(private/f'transcript_{s}.md' for s in seen_seeds),*prereg.iterdir()]
    save(ROOT/'mapping_manifest.json',{'passed':True,'sources_sha256':{str(p):sha(p) for p in sources},
      'outputs_sha256':{str(p):sha(p) for p in outputs},'independent_integer_score_agreements':96,
      'independent_checkpoint_vector_agreements':12,'event_count':480,'model_executed':False})
    print(json.dumps({'passed':True,'learn_events':384,'queries':96,'phase_combined':summary['phase_combined'],
        'final_queries':summary['final_queries'],'output':str(private/'mapping.json')},indent=2))

if __name__=='__main__':main()
