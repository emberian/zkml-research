"""No model inference: independent integer replay, exact denominator and pins."""
import hashlib,json,math,sys,time
from pathlib import Path
sys.dont_write_bytecode=True
import numpy as np
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 t=time.perf_counter();r=load(ROOT/'results.json');records=load(ROOT/'records.json');Hs=load(ROOT/'histories.json')['histories'];Q=np.load(ROOT/'features.npz')
 for p,h in load(ROOT/'freeze.json')['source_sha256'].items():assert sha(p)==h,p
 assert r['selection_sha256']==sha(ROOT/'selection.json') and r['features_sha256']==sha(ROOT/'features.npz')
 for name in ['e5_test','smol_test']:assert load(ROOT/f'{name}.extraction.json')['selection_sha256']==sha(ROOT/'selection.json')
 count=0;final=0;retention=0;correct={};bounds={}
 for name,method in r['results'].items():
  d=Q[name].shape[1];assert d==(769 if name=='e5_raw769' else 577);assert Q[name].shape==(384,d)
  assert int(Q[name].min())>=-127 and int(Q[name].max())<=127
  bounds[name]={'dimension':d,'generic_abs_score_bound':d*32*127**2,'observed_abs_score_max':0};correct[name]=[0,0,0]
  assert len(method['per_history'])==64
  for H,row in zip(Hs,method['per_history']):
   assert H['seed']==row['seed'];assert row['query_ids']==list(range(256,384))
   for phase in range(3):
    assert len(row['scores'][phase])==len(row['predictions'][phase])==len(row['targets'][phase])==128
    for rid,score,pred,target in zip(row['query_ids'],row['scores'][phase],row['predictions'][phase],row['targets'][phase]):
     a=records[rid];gold=H['rules'][a['skill']][2*a['a']+a['b']]
     if phase==2 and a['skill']==0:gold=-gold
     assert gold==target and pred==(1 if score>=0 else -1);count+=1;final+=int(phase==2);correct[name][phase]+=int(pred==target)
     assert abs(score)<=bounds[name]['generic_abs_score_bound'];bounds[name]['observed_abs_score_max']=max(bounds[name]['observed_abs_score_max'],abs(score))
    assert row['targets'][phase].count(1)==64
   assert row['predictions'][0][:64]==row['predictions'][1][:64] and row['predictions'][1][64:]==row['predictions'][2][64:];retention+=2
  assert correct[name][2]/8192==method['metrics']['final_mean']['mean']
 assert count==147456 and final==49152 and retention==768
 # Pure Python lists, signed integer input encoding, direct retained queue sums.
 primary=Q['e5_projected577'].tolist();integer_scores=0;vectors=0
 for H,row in zip(Hs,r['results']['e5_projected577']['per_history']):
  queues=[[],[]];prior=None
  for phase,ids in enumerate(H['phases']):
   for rid in ids:
    a=records[rid];s=a['skill'];y=H['rules'][s][2*a['a']+a['b']]
    if phase==2 and s==0:y=-y
    queues[s]=(queues[s]+[[y*x for x in primary[rid]]])[-32:]
   state=[[sum(v[j] for v in q) for j in range(577)] for q in queues];vectors+=2
   assert all(abs(v)<=4064 for rowstate in state for v in rowstate)
   if phase==1:assert state[0]==prior[0]
   if phase==2:assert state[1]==prior[1]
   for rid,want in zip(row['query_ids'],row['scores'][phase]):
    assert sum(a*b for a,b in zip(state[records[rid]['skill']],primary[rid]))==want;integer_scores+=1
   prior=state
 assert integer_scores==24576 and vectors==384
 paired={}
 for ref in r['paired_primary_minus']:
  differences=[]
  for a,b in zip(r['results']['e5_projected577']['per_history'],r['results'][ref]['per_history']):
   aa=sum(x==y for x,y in zip(a['predictions'][2],a['targets'][2]));bb=sum(x==y for x,y in zip(b['predictions'][2],b['targets'][2]));differences.append((aa-bb)/128)
  mean=sum(differences)/64;half=1.96*math.sqrt(sum((d-mean)**2 for d in differences)/63)/8
  assert mean==r['paired_primary_minus'][ref]['mean'] and abs(half-r['paired_primary_minus'][ref]['normal95_half_width'])<1e-14
  paired[ref]={'net_additional_final_correct':int(mean*8192),'difference':mean,'normal95_half_width':half}
 # Independent inventory of projection draw/value range; no new draw selected.
 signs=np.load(ROOT/'projection.npz')['signs'];proj=load(ROOT/'projection.json')
 assert signs.shape==(768,576) and set(np.unique(signs))=={-1,1}
 assert hashlib.sha256(signs.tobytes()).hexdigest()==proj['signs_raw_sha256']
 assert proj['candidate_projections_drawn']==1
 import run as protocol
 E=np.concatenate([np.load(ROOT/'e5_train.npz')['features'],np.load(ROOT/'e5_test.npz')['features']]);routes=np.array([a['skill'] for a in records])
 rebuilt,_,_=protocol.make_e5_features(E,routes)
 for name,q in rebuilt.items():assert np.array_equal(q,Q[name])
 norms=np.linalg.norm(E.astype(float),axis=1)
 assert float(np.max(np.abs(norms-1)))<1e-5
 # Every query is new, and the teacher stream only references original teacher IDs.
 assert all(all(rid<128 for phase in H['phases'] for rid in phase) for H in Hs)
 result={'passed':True,'all_prediction_records':count,'all_final_prediction_records':final,
  'correct_counts_by_phase':correct,'bounds':bounds,'paired_primary_minus_counts':paired,
  'primary_independent_integer_scores':integer_scores,'primary_independent_checkpoint_vectors':vectors,
  'untouched_route_state_output_equalities':retention,'e5_features_rebuilt_without_label_arguments':True,
  'e5_embedding_max_abs_unit_norm_error':float(np.max(np.abs(norms-1))),
  'one_projection_pinned':True,'new_test_records_absent_from_teaching':True,
  'results_sha256':sha(ROOT/'results.json'),'audit_source_sha256':sha(__file__),'wall_seconds':time.perf_counter()-t}
 (ROOT/'audit.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
