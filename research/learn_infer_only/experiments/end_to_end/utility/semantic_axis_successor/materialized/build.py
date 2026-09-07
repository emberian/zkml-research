"""Materialize the frozen PUBLIC semantic fixture and segregated role inputs."""
import sys,time
sys.dont_write_bytecode=True
from common import *
import numpy as np
def main():
 started=time.perf_counter();verify();assert not (ROOT/'fixture.json').exists(),'Preserve fixture'
 select=load(ROOT/'selection.json');records=load(PARENT/'records.json');hist=load(PARENT/'histories.json')['histories']
 history_by_id={h['seed']:h for h in hist};pred={r['record_id']:r for r in load(PARENT/'teacher_predictions.json')+load(PARENT/'test_predictions.json')}
 qcache=np.load(PARENT/'features.npz')['semantic577'];statecache=np.load(PARENT/'checkpoint_states.npz')['semantic577']
 survey=load(PARENT/'results.json');full={name:{row['seed']:row for row in m['per_history']} for name,m in survey['results'].items()}
 vectors={i:onehot(records[i]['skill'],pred[i]['a'],pred[i]['b']) for i in list(range(128))+select['query_ids']}
 for i,v in vectors.items():assert v==qcache[i].tolist()
 qrecords=[];qindex={}
 for index,rid in enumerate(select['query_ids']):
  rec=records[rid];v=vectors[rid];qindex[rid]=index
  qrecords.append({'query_index':index,'query_id':f'q{index:02d}','record_id':rid,'route':rec['skill'],
   'vector':v,'vector_file_sha256':vector_sha(v),'signed_int8_bytes_sha256':signed_bytes_sha(v),
   'predicted_pair':[pred[rid]['a'],pred[rid]['b']],'selection_only_gold_pair':[rec['a'],rec['b']],
   'source_text':rec['text'],'source_factual_error':(pred[rid]['a'],pred[rid]['b'])!=(rec['a'],rec['b'])})
 events=[];learns=[];oracles={};checkpoints=[];histories=[];expiry_count=0;empty_count=0;nonempty_zero=0
 for hi,seed in enumerate(select['history_ids']):
  H=history_by_id[seed];assert list(map(len,H['phases']))==[64,64,64]
  histories.append({'history_index':hi,**H});queues=[[],[]];state=[[0]*577,[0]*577];ordinal=0;step=0
  source_hi=next(i for i,h in enumerate(hist) if h['seed']==seed)
  for phase,ids in enumerate(H['phases'],1):
   for rid in ids:
    ordinal+=1;step+=1;eventid=f'h{hi}-e{ordinal:04d}';rec=records[rid];route=rec['skill']
    y=H['rules'][route][2*rec['a']+rec['b']]
    if phase==3 and route==0:y=-y
    z=[y*x for x in vectors[rid]];assert all(-127<=x<=127 for x in z)
    queues[route].append((eventid,z));state[route]=[a+b for a,b in zip(state[route],z)];expired=None
    if len(queues[route])>32:
     expired,old=queues[route].pop(0);state[route]=[a-b for a,b in zip(state[route],old)];expiry_count+=1
    assert state[route]==[sum(v[j] for _,v in queues[route]) for j in range(577)]
    event={'event_id':eventid,'history_index':hi,'history_id':seed,'event_ordinal':ordinal,'phase':phase,'learn_step':step,
     'kind':'Learn','route':route,'record_id':rid,'learn_vector_index':len(learns),'expired_event_id':expired,'queue_count_after':len(queues[route])}
    learns.append({'event_id':eventid,'record_id':rid,'route':route,'signed_label':y,'vector':z,
     'vector_file_sha256':vector_sha(z),'signed_int8_bytes_sha256':signed_bytes_sha(z),
     'predicted_pair':[pred[rid]['a'],pred[rid]['b']],'oracle_gold_pair':[rec['a'],rec['b']],
     'source_factual_error':(pred[rid]['a'],pred[rid]['b'])!=(rec['a'],rec['b'])})
    events.append(event)
   assert state==statecache[source_hi,phase-1].tolist()
   checkpoints.append({'history_id':seed,'history_index':hi,'phase':phase,'after_learn_step':step,
    'queue_counts':[len(x) for x in queues],'queue_event_ids':[[eid for eid,_ in q] for q in queues],
    'state_vectors':state.copy()})
   for rid in select['query_ids']:
    ordinal+=1;eventid=f'h{hi}-e{ordinal:04d}';rec=records[rid];route=rec['skill'];q=vectors[rid]
    score=sum(a*b for a,b in zip(state[route],q));gold=H['rules'][route][2*rec['a']+rec['b']]
    if phase==3 and route==0:gold=-gold
    predicted=1 if score>=0 else -1;empty=len(queues[route])==0;empty_count+=empty
    nonempty_zero+=not empty and score==0
    original_records={}
    for name,method in full.items():
     row=method[seed];j=row['query_ids'].index(rid)
     entry={'score':row['scores'][phase-1][j],'prediction':row['predictions'][phase-1][j],
      'target':row['targets'][phase-1][j]};entry['correct']=entry['prediction']==entry['target'];original_records[name]=entry
    assert original_records['semantic577']=={'score':score,'prediction':predicted,'target':gold,'correct':predicted==gold}
    events.append({'event_id':eventid,'history_index':hi,'history_id':seed,'event_ordinal':ordinal,'phase':phase,'learn_step':step,
     'kind':'Infer','route':route,'record_id':rid,'query_index':qindex[rid],'public_query_id':f'q{qindex[rid]:02d}',
     'public_empty_route':empty})
    oracles[eventid]={'expected_scalar':score,'sign':predicted,'target_label':gold,'correct':predicted==gold,
     'public_structural_zero':empty,'nonempty_zero_score':not empty and score==0,'record_id':rid,'phase':phase,'history_id':seed,
     'source_factual_error':(pred[rid]['a'],pred[rid]['b'])!=(rec['a'],rec['b']),
     'original_full_survey_selected_records':original_records}
  assert step==192 and ordinal==240
 counts={'learn':len(learns),'queries':len(oracles),'events':len(events),'expiries':expiry_count,
  'empty_route_queries':empty_count,'public_query_records':len(qrecords)}
 expected=load(ROOT/'freeze.json')['expected_counts']
 if counts!=expected:
  save(ROOT/'schedule_discrepancy.json',{'actual':counts,'expected':expected});raise RuntimeError('Schedule mismatch; no adaptation authorized')
 source_records=[]
 for rid in sorted(vectors):
  rec=records[rid];source_records.append({**rec,'predicted_pair':[pred[rid]['a'],pred[rid]['b']],
   'factual_error_axes':[axis for axis in ['a','b'] if pred[rid][axis]!=rec[axis]]})
 fixture={'schema':'PUBLIC_SEMANTIC_WINDOW_FIXTURE_V1','exposure':'PUBLIC synthetic research fixture; no private user data',
  'scope':'Integration correctness subset, not a new utility estimate','dimension':577,'window_per_route':32,
  'selection_sha256':sha(ROOT/'selection.json'),'parent_results_sha256':sha(PARENT/'results.json'),
  'histories':histories,'source_records':source_records,'query_records':qrecords,'learn_vectors':learns,'events':events,
  'checkpoints':checkpoints,'counts':counts}
 save(ROOT/'fixture.json',fixture,compact=True);save(ROOT/'public_query_records.json',{'exposure':'PUBLIC research query rows; duplicates retained','queries':qrecords})
 save(ROOT/'integer_oracle.json',{'exposure':'PUBLIC test oracle; not a host/authority input','queries':oracles})
 save(ROOT/'public_event_index.json',{'schema':'E2E_PUBLIC_EVENT_INDEX_V1','events':[{k:e[k] for k in ['event_id','event_ordinal','history_index','kind','route']} for e in events]})
 save(ROOT/'full_survey_reference.json',{'parent_results_sha256':sha(PARENT/'results.json'),
  'full_denominators':survey['denominators'],'full_factual_results':survey['factual'],
  'full_final_counts':{name:{'correct':m['correct_final'],'total':m['final_queries']} for name,m in survey['results'].items()},
  'full_acceptance':survey['acceptance'],'subset_accuracy_estimate_emitted':False})
 # Regeneratable split inputs. These are public fixture bytes with role-file modes.
 runtime=ROOT/'runtime';runtime.mkdir(exist_ok=False)
 input_events=[];filecensus={}
 for q in qrecords:
  path=runtime/'public_queries'/f"{q['query_id']}.json";role_json(path,q['vector'])
  assert sha(path)==q['vector_file_sha256'];filecensus[str(path.relative_to(ROOT))]={'sha256':sha(path),'bytes':path.stat().st_size}
 for e in events:
  entry={k:e[k] for k in ['event_id','kind','route']}
  if e['kind']=='Learn':
   v=learns[e['learn_vector_index']];path=runtime/'issuer/vectors'/f"{e['event_id']}.json";role_json(path,v['vector'])
   assert sha(path)==v['vector_file_sha256'];entry['issuer_vector_path']=str(path)
   filecensus[str(path.relative_to(ROOT))]={'sha256':sha(path),'bytes':path.stat().st_size}
  else:entry['public_query_vector_path']=str(runtime/'public_queries'/f"{e['public_query_id']}.json")
  input_events.append(entry)
 role_json(runtime/'issuer/input_index.json',{'schema':'E2E_ISSUER_INPUT_INDEX_V1','exposure':'PUBLIC research fixture, issuer/coordinator role input only','events':input_events})
 role_json(runtime/'oracle/expected_scalars.json',{'schema':'E2E_TEST_ORACLE_SCALARS_V1','exposure':'PUBLIC test oracle, not host input','queries':oracles})
 for name in ['issuer/input_index.json','oracle/expected_scalars.json']:
  path=runtime/name;filecensus[str(path.relative_to(ROOT))]={'sha256':sha(path),'bytes':path.stat().st_size}
 save(ROOT/'runtime_hash_census.json',{'exposure':'PUBLIC deterministic derived role inputs, ignored and regeneratable','files':filecensus,
  'issuer_vectors':384,'query_vectors':16,'issuer_file_mode':'0600','generated_input_index':str(runtime/'issuer/input_index.json')})
 ranks={}
 for route in [0,1]:
  rows=[q for q in qrecords if q['route']==route];active=sorted({q['vector'].index(127) for q in rows})
  assert active==list(range(4*route,4*route+4))
  ranks[str(route)]={'row_records':len(rows),'unique_rows':len(active),'exact_row_rank':len(active),
   'active_coordinates':active,'basis_record_ids':{str(j):min(q['record_id'] for q in rows if q['vector'][j]==127) for j in active}}
 report={'prepared':True,'counts':counts,'nonempty_queries':96-empty_count,'nonempty_zero_queries':nonempty_zero,
  'duplicate_query_records':16-sum(v['unique_rows'] for v in ranks.values()),'row_rank_by_route':ranks,
  'global_query_row_rank':8,'effective_aggregate_rank_per_route':4,'recipient_coalition_aggregate_privacy_claim':False,
  'source_vectors_from_model_predictions_only':True,'frozen_full_run_score_comparisons':96,'frozen_full_run_state_vector_comparisons':12,
  'crypto_executions':0,'encoder_executions':0,'subset_utility_estimate':False,'parent_entries_unchanged':verify_parent(),
  'fixture_sha256':sha(ROOT/'fixture.json'),'integer_oracle_sha256':sha(ROOT/'integer_oracle.json'),
  'freeze_sha256':sha(ROOT/'freeze.json'),'build_wall_seconds':time.perf_counter()-started}
 save(ROOT/'build_results.json',report);print(json.dumps(report,indent=2))
if __name__=='__main__':main()
