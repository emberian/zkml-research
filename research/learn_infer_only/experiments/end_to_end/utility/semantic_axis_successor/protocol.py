"""Frozen one-hot source map, unchanged integer routed W32 and summaries."""
import sys,math,statistics
sys.dont_write_bytecode=True
from collections import deque
import numpy as np
from common import *
sys.path.insert(0,str(BASE))
import text_transfer_data as olddata
def summary(values):
 v=np.array(values,dtype=float);sd=float(v.std(ddof=1)) if len(v)>1 else 0.
 return {'mean':float(v.mean()),'n_histories':len(v),'sd':sd,'normal95_half_width':1.96*sd/math.sqrt(len(v)),
  'min':float(v.min()),'max':float(v.max())}
def one_hot(predictions,routes):
 q=np.zeros((384,577),np.int8)
 for r in predictions:
  i=r['record_id'];s=int(routes[i]);a=r['a'];b=r['b'];assert a in [0,1] and b in [0,1]
  q[i,4*s+2*a+b]=127
 return q
def original_features(hidden,routes):
 policy=load(UTILITY/'encoder_policy.json')['policies_by_public_route'];q=np.zeros((384,577),np.int8)
 for s in [0,1]:
  ids=np.where(routes==s)[0];p=policy[str(s)]
  x=(hidden[ids]-np.array(p['center']))/p['scale']
  q[ids]=np.clip(np.rint(127*np.column_stack([x,np.full(len(ids),1/p['scale'])])),-127,127).astype(np.int8)
 return q
def run_history(H,records,Q):
 query=list(range(256,384));routes=np.array([records[i]['skill'] for i in query]);d=577
 state=np.zeros((2,d),np.int64);queues=[deque(),deque()];states=[];scores=[];predictions=[];targets=[]
 for phase,ids in enumerate(H['phases']):
  for rid,y in zip(ids,olddata.labels(H,records,ids,flip0=phase==2)):
   s=records[rid]['skill'];v=int(y)*Q[rid].astype(np.int64);queues[s].append(v);state[s]+=v
   if len(queues[s])>32:state[s]-=queues[s].popleft()
  scalar=np.einsum('ij,ij->i',state[routes],Q[query].astype(np.int64),dtype=np.int64)
  scores.append(scalar.tolist());predictions.append(np.where(scalar>=0,1,-1).tolist())
  targets.append(olddata.labels(H,records,query,flip0=phase==2).tolist());states.append(state.copy())
 assert np.array_equal(states[0][0],states[1][0]) and np.array_equal(states[1][1],states[2][1])
 assert predictions[0][:64]==predictions[1][:64] and predictions[1][64:]==predictions[2][64:]
 accuracy=lambda phase,s:float(np.mean(np.array(predictions[phase])[routes==s]==np.array(targets[phase])[routes==s]))
 metrics={'plant_initial':accuracy(0,0),'plant_after_letters':accuracy(1,0),'letter_after_learning':accuracy(1,1),
  'plant_changed':accuracy(2,0),'letter_retained':accuracy(2,1),'final_mean':(accuracy(2,0)+accuracy(2,1))/2}
 types=['nonlinear' if rule[0]==rule[3] and rule[1]==rule[2] else 'linear' for rule in H['rules']]
 return {'seed':H['seed'],'rule_types':types,'joint_stratum':'/'.join(types),'query_ids':query,
  'scores':scores,'predictions':predictions,'targets':targets,'metrics':metrics},np.array(states)
def factual_cell(rows):
 groups={}
 for r in rows:groups.setdefault(r['record_id'],[]).append(r)
 return {'correct_bits':sum(r['correct'] for r in rows),'bits':len(rows),'bit_accuracy':sum(r['correct'] for r in rows)/len(rows),
  'correct_pairs':sum(len(v)==2 and all(r['correct'] for r in v) for v in groups.values()),
  'pairs':sum(len(v)==2 for v in groups.values()),'ties':sum(r['exact_tie'] for r in rows),
  'mean_alternative_probability_mass':statistics.mean(r['alternative_probability_mass'] for r in rows)}
