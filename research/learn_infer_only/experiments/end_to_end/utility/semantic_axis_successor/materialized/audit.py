"""Independent deterministic replay and exact query-rank audit; no crypto/model."""
import sys,time
sys.dont_write_bytecode=True
from fractions import Fraction
from common import *
def rank(matrix):
 a=[[Fraction(x) for x in row] for row in matrix];pivot=0
 for col in range(len(a[0])):
  choice=next((j for j in range(pivot,len(a)) if a[j][col]),None)
  if choice is None:continue
  a[pivot],a[choice]=a[choice],a[pivot];v=a[pivot][col];a[pivot]=[x/v for x in a[pivot]]
  for j in range(len(a)):
   if j!=pivot and a[j][col]:
    v=a[j][col];a[j]=[x-v*y for x,y in zip(a[j],a[pivot])]
  pivot+=1
  if pivot==len(a):break
 return pivot
def main():
 started=time.perf_counter();verify();f=load(ROOT/'fixture.json');oracle=load(ROOT/'integer_oracle.json')['queries']
 selection=load(ROOT/'selection.json');records=load(PARENT/'records.json')
 teachers=load(PARENT/'teacher_predictions.json');test=load(PARENT/'test_predictions.json')
 predicted={x['record_id']:x for x in teachers+test};learns={x['event_id']:x for x in f['learn_vectors']}
 queries={x['query_index']:x for x in f['query_records']};survey=load(PARENT/'results.json')
 assert f['counts']==load(ROOT/'freeze.json')['expected_counts']
 expected_queries=sorted(r['id'] for s in [0,1] for a in [0,1] for b in [0,1]
  for r in sorted((r for r in records if r['pool']=='test' and (r['skill'],r['a'],r['b'])==(s,a,b)),key=lambda r:r['id'])[:2])
 assert expected_queries==selection['query_ids'] and [x['record_id'] for x in f['query_records']]==expected_queries
 for q in queries.values():
  rid=q['record_id'];p=predicted[rid];expected=[0]*577;expected[4*records[rid]['skill']+2*p['a']+p['b']]=127
  assert q['vector']==expected and q['vector_file_sha256']==vector_sha(expected)
  assert q['signed_int8_bytes_sha256']==signed_bytes_sha(expected)
 all_expiries=0;all_queries=0;learn_count=0;state_checks=0;empty_queries=0
 for history in f['histories']:
  hi=history['history_index'];seed=history['seed'];queues=[[],[]];step=0;phaselearns={1:[],2:[],3:[]};phasequeries={1:[],2:[],3:[]}
  events=[e for e in f['events'] if e['history_index']==hi];assert [e['event_ordinal'] for e in events]==list(range(1,241))
  for event in events:
   s=event['route'];phase=event['phase'];rid=event['record_id'];rec=records[rid]
   assert rec['skill']==s
   if event['kind']=='Learn':
    step+=1;learn_count+=1;row=learns[event['event_id']];p=predicted[rid]
    expected=[0]*577;y=history['rules'][s][2*rec['a']+rec['b']]
    if phase==3 and s==0:y=-y
    expected[4*s+2*p['a']+p['b']]=127*y
    assert row['vector']==expected and row['signed_label']==y
    assert row['vector_file_sha256']==vector_sha(expected) and row['signed_int8_bytes_sha256']==signed_bytes_sha(expected)
    queues[s].append(event['event_id']);expired=None
    if len(queues[s])>32:expired=queues[s].pop(0);all_expiries+=1
    assert event['expired_event_id']==expired and event['queue_count_after']==len(queues[s])
    phaselearns[phase].append(rid)
   else:
    all_queries+=1;phasequeries[phase].append(rid);q=queries[event['query_index']]['vector']
    direct=[sum(learns[eid]['vector'][j] for eid in queues[s]) for j in range(577)]
    score=sum(x*y for x,y in zip(direct,q));wanted=oracle[event['event_id']]
    assert score==wanted['expected_scalar'] and wanted['sign']==(1 if score>=0 else -1)
    target=history['rules'][s][2*rec['a']+rec['b']]
    if phase==3 and s==0:target=-target
    assert target==wanted['target_label'] and wanted['correct']==(wanted['sign']==target)
    assert wanted['public_structural_zero']==(len(queues[s])==0);empty_queries+=len(queues[s])==0
    for name,m in survey['results'].items():
     row=next(row for row in m['per_history'] if row['seed']==seed);j=row['query_ids'].index(rid)
     entry=wanted['original_full_survey_selected_records'][name]
     assert entry['score']==row['scores'][phase-1][j] and entry['prediction']==row['predictions'][phase-1][j]
     assert entry['target']==row['targets'][phase-1][j]
   assert event['learn_step']==step
  for phase in [1,2,3]:
   assert phaselearns[phase]==history['phases'][phase-1] and phasequeries[phase]==expected_queries
   checkpoint=next(x for x in f['checkpoints'] if x['history_id']==seed and x['phase']==phase)
   for s in [0,1]:
    ids=checkpoint['queue_event_ids'][s];direct=[sum(learns[eid]['vector'][j] for eid in ids) for j in range(577)]
    assert direct==checkpoint['state_vectors'][s] and len(ids)==checkpoint['queue_counts'][s];state_checks+=1
 assert (learn_count,all_queries,all_expiries,state_checks,empty_queries)==(384,96,256,12,16)
 ranks={}
 for s in [0,1]:
  rows=[q['vector'][4*s:4*s+4] for q in queries.values() if q['route']==s]
  ranks[str(s)]=rank(rows);assert ranks[str(s)]==4
 global_rank=rank([q['vector'][:8] for q in queries.values()]);assert global_rank==8
 census=load(ROOT/'runtime_hash_census.json')['files'];assert len(census)==402
 for relative,meta in census.items():
  path=ROOT/relative;assert sha(path)==meta['sha256'] and path.stat().st_size==meta['bytes']
  assert path.stat().st_mode&0o777==0o600
 index=load(ROOT/'runtime/issuer/input_index.json');assert len(index['events'])==480
 assert len(list((ROOT/'runtime/issuer/vectors').glob('*.json')))==384
 assert len(list((ROOT/'runtime/public_queries').glob('*.json')))==16
 for e in index['events']:
  if e['kind']=='Learn':assert load(e['issuer_vector_path'])==learns[e['event_id']]['vector']
  else:
   source=next(x for x in f['events'] if x['event_id']==e['event_id']);assert load(e['public_query_vector_path'])==queries[source['query_index']]['vector']
 out={'passed':True,'learn_vectors':learn_count,'exact_query_scores':all_queries,'same_identity_expiries':all_expiries,
  'checkpoint_vectors':state_checks,'empty_route_queries':empty_queries,'public_query_record_count':16,
  'exact_fraction_rank_by_route':ranks,'global_exact_fraction_rank':global_rank,'generated_files_verified':len(census),
  'all_parent_entries_unchanged':verify_parent(),'crypto_executions':0,'encoder_executions':0,
  'subset_utility_estimate':False,'fixture_sha256':sha(ROOT/'fixture.json'),'freeze_sha256':sha(ROOT/'freeze.json'),
  'audit_wall_seconds':time.perf_counter()-started}
 save(ROOT/'audit.json',out);print(json.dumps(out,indent=2))
if __name__=='__main__':main()
