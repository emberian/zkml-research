"""Independent integer/expiry and complete outcome audit, without model calls."""
import sys,time,math
sys.dont_write_bytecode=True
from common import *
import numpy as np
def main():
 t=time.perf_counter();verify();r=load(ROOT/'results.json');records=load(ROOT/'records.json')
 Hs=load(ROOT/'histories.json')['histories'];Q=np.load(ROOT/'features.npz');states=np.load(ROOT/'checkpoint_states.npz')
 assert [h['seed'] for h in Hs]==list(range(67000,67064))
 assert r['features_sha256']==sha(ROOT/'features.npz') and r['checkpoint_states_sha256']==sha(ROOT/'checkpoint_states.npz')
 assert load(ROOT/'score_results.json')['actual_forward_examples']==256
 count=0;final=0;retention=0;correct={};bounds={}
 for name,method in r['results'].items():
  assert Q[name].shape==(384,577) and states[name].shape==(64,3,2,577)
  assert int(Q[name].min())>=-127 and int(Q[name].max())<=127
  bound=(577 if name=='original577' else 1)*32*127**2;maximum=0;correct[name]=[0,0,0]
  for hi,(H,row) in enumerate(zip(Hs,method['per_history'])):
   assert H['seed']==row['seed'] and row['query_ids']==list(range(256,384))
   for phase in range(3):
    assert len(row['scores'][phase])==len(row['predictions'][phase])==len(row['targets'][phase])==128
    for rid,score,pred,target in zip(row['query_ids'],row['scores'][phase],row['predictions'][phase],row['targets'][phase]):
     a=records[rid];gold=H['rules'][a['skill']][2*a['a']+a['b']]
     if phase==2 and a['skill']==0:gold=-gold
     assert gold==target and pred==(1 if score>=0 else -1) and abs(score)<=bound
     count+=1;final+=phase==2;correct[name][phase]+=pred==target;maximum=max(maximum,abs(score))
    assert row['targets'][phase].count(1)==64
   assert np.array_equal(states[name][hi,0,0],states[name][hi,1,0])
   assert np.array_equal(states[name][hi,1,1],states[name][hi,2,1])
   assert row['predictions'][0][:64]==row['predictions'][1][:64] and row['predictions'][1][64:]==row['predictions'][2][64:]
   retention+=2
  assert correct[name][2]==method['correct_final'] and correct[name][2]/8192==method['metrics']['final_mean']['mean']
  bounds[name]={'absolute_score_bound':bound,'observed_absolute_maximum':maximum}
 assert count==73728 and final==24576 and retention==384
 # No numpy arithmetic or imported update/label helper in this replay.
 primary=Q['semantic577'].tolist();teacher=load(ROOT/'teacher_predictions.json');test=load(ROOT/'test_predictions.json')
 for pred in teacher+test:
  i=pred['record_id'];s=records[i]['skill'];want=[0]*577;want[4*s+2*pred['a']+pred['b']]=127
  assert primary[i]==want
 assert all(all(x==0 for x in row) for row in primary[128:256])
 vectors=0;integer_scores=0;update_checks=0;expiries=0;parity_checks=0
 for hi,(H,row) in enumerate(zip(Hs,r['results']['semantic577']['per_history'])):
  queues=[[],[]];sparse=[[0]*4,[0]*4]
  for phase,ids in enumerate(H['phases']):
   assert len(ids)==64 and all(i<128 for i in ids)
   for rid in ids:
    a=records[rid];s=a['skill'];y=H['rules'][s][2*a['a']+a['b']]
    if phase==2 and s==0:y=-y
    active=[j for j,x in enumerate(primary[rid]) if x]
    assert len(active)==1 and primary[rid][active[0]]==127 and 4*s<=active[0]<4*s+4
    j=active[0]-4*s;queues[s].append((j,y));sparse[s][j]+=127*y
    if len(queues[s])>32:
     oldj,oldy=queues[s].pop(0);sparse[s][oldj]-=127*oldy;expiries+=1
    direct=[sum(127*label for coordinate,label in queues[s] if coordinate==k) for k in range(4)]
    assert direct==sparse[s];assert all(abs(x)<=4064 for x in direct);update_checks+=1
    if len(queues[s])==32:
     z=[x//127 for x in direct];assert sum(abs(x) for x in z)<=32 and sum(z)%2==0;parity_checks+=1
   dense=[]
   for s in [0,1]:
    v=[0]*577;v[4*s:4*s+4]=sparse[s];dense.append(v)
    assert v==states['semantic577'][hi,phase,s].tolist();vectors+=1
   for rid,want in zip(row['query_ids'],row['scores'][phase]):
    got=sum(a*b for a,b in zip(dense[records[rid]['skill']],primary[rid]));assert got==want;integer_scores+=1
 assert vectors==384 and integer_scores==24576 and update_checks==12288 and expiries==8192
 raw=load(ROOT/'raw_scores.json');oracle={x['record_id']:x for x in load(ROOT/'test_oracle.json')}
 assert {(x['record_id'],x['axis']) for x in raw}=={(i,a) for i in range(256,384) for a in ['a','b']}
 factual=0
 for x in raw:
  assert x['framing']=='A' and x['alternative_token_ids_in_bit_order']==[15,16]
  pred=int(x['logits_in_bit_order'][0]<x['logits_in_bit_order'][1]);assert pred==x['predicted_bit']
  factual+=pred==oracle[x['record_id']][x['axis']]
 assert factual==r['factual']['overall']['correct_bits']
 paired={}
 for ref in ['original577','attribute8']:
  values=[(sum(x==y for x,y in zip(a['predictions'][2],a['targets'][2]))-sum(x==y for x,y in zip(b['predictions'][2],b['targets'][2])))/128
   for a,b in zip(r['results']['semantic577']['per_history'],r['results'][ref]['per_history'])]
  mean=sum(values)/64;half=1.96*math.sqrt(sum((v-mean)**2 for v in values)/63)/8
  assert mean==r['paired_primary_minus'][ref]['mean'] and abs(half-r['paired_primary_minus'][ref]['normal95_half_width'])<1e-14
  paired[ref]={'mean':mean,'normal95_half_width':half,'net_additional_final_correct':round(mean*8192)}
 rank=load(ROOT/'image_rank_scope.json');assert rank['exact_score_basis_determinant_per_route']==16129**4
 for s in [0,1]:
  for pool,ids in [('teacher',range(128)),('test',range(256,384))]:
   images={tuple(primary[i][4*s:4*s+4]) for i in ids if records[i]['skill']==s}
   assert all(sum(x!=0 for x in v)==1 and max(v)==127 for v in images)
   assert len(images)==rank['observed_images'][str(s)][pool]['exact_rank']
 out={'passed':True,'all_prediction_records':count,'all_final_prediction_records':final,'correct_counts_by_phase':correct,
  'primary_independent_integer_scores':integer_scores,'primary_independent_checkpoint_vectors':vectors,
  'every_update_direct_queue_checks':update_checks,'same_contribution_expiries_checked':expiries,
  'full_window_lattice_necessary_condition_checks':parity_checks,'untouched_route_state_and_output_equalities':retention,
  'bounds':bounds,'factual_bits_audited':256,'paired_primary_minus':paired,'image_rank_checked':True,
  'model_calls_in_audit':0,'results_sha256':sha(ROOT/'results.json'),'wall_seconds':time.perf_counter()-t}
 save(ROOT/'audit.json',out);print(json.dumps(out,indent=2))
if __name__=='__main__':main()
