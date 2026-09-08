"""Fixed selection from existing public benchmark vectors; no model/crypto run."""
import hashlib,json
from pathlib import Path
import numpy as np
from basis import D,R,P,GeneralBasis,pivots
HERE=Path(__file__).resolve().parent;OLD=HERE.parent/'useful_learner_2026_09_08'
CLASSES=['card_arrival','cash_withdrawal_charge']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(path,data):path.write_text(json.dumps(data,indent=2)+'\n')
def main():
 data=json.loads((OLD/'data/selected.json').read_text());arrays=np.load(OLD/'features.npz')
 qi=[]
 for label in CLASSES:qi += [i for i,row in enumerate(data['test']) if row['category']==label][:8]
 ti={label:[i for i,row in enumerate(data['train']) if row['category']==label][:3] for label in CLASSES}
 queries=[{'coordinate':j,'test_index':i,'text':data['test'][i]['text'],'label':data['test'][i]['category'],'vector':arrays['test'][i].tolist()} for j,i in enumerate(qi)]
 rows=[q['vector'] for q in queries];pc=pivots(rows,P)
 registry={'schema':'restricted-semantic-query-registry-v1','p':P,'dimension':D,'registered_recipients':R,'selection':'First8 original test rows for each of fixed classes card_arrival and cash_withdrawal_charge, in that order; no score-based selection','classes':CLASSES,'queries':queries,'pivot_columns':pc,'identity_columns':[i for i in range(D) if i not in pc],'basis_rule':'First16 rows are actual saved query vectors; remaining rows are identity rows in ascending nonpivot columns','source_sha256':{str(OLD/x):sha(OLD/x) for x in ['config.json','encoder.py','features.npz','data/selected.json']}}
 b=GeneralBasis(registry);save(HERE/'registry.json',registry)
 events=[];queues={c:[] for c in CLASSES};snapshots=[]
 for round_ in range(3):
  for label in CLASSES:
   i=ti[label][round_];x=arrays['train'][i].tolist();assert len(x)==577 and x[-1]==0 and max(map(abs,x))<=127
   a=b.transform(x);assert b.inverse(a)==[v%P for v in x]
   assert a[:R]==[sum(v*w for v,w in zip(q,x)) for q in rows]
   event={'event':len(events)+1,'class':label,'train_index':i,'text':data['train'][i]['text'],'vector':x,'expired_event':queues[label].pop(0)['event'] if len(queues[label])==2 else None};queues[label].append(event);events.append(event)
  scores=[{c:sum(sum(v*w for v,w in zip(q,e['vector'])) for e in queues[c]) for c in CLASSES} for q in rows]
  predictions=[max(CLASSES,key=lambda c:(s[c],-CLASSES.index(c))) for s in scores]
  snapshots.append({'revision':len(events),'counts':{c:len(queues[c]) for c in CLASSES},'live_events':{c:[e['event'] for e in queues[c]] for c in CLASSES},'scores':scores,'predictions':predictions,'correct':sum(label==q['label'] for label,q in zip(predictions,queries))})
 save(HERE/'fixture.json',{'classes':CLASSES,'capacity':2,'events':events,'snapshots':snapshots,'scope':'Known-public reused benchmark fixture; no new held-out estimate'})
 bounds=[2*x for x in b.bounds]
 check={'status':'PASS','query_row_rank':len(pc),'basis_dimension':D,'identity_completion_rows':len(b.rest),'registered_coordinates':R,'absent_coordinates':D-R,'max_query_L1':max(sum(map(abs,q)) for q in rows),'whole_window_bound_all_int8_observations':max(bounds),'p_half_floor':P//2,'whole_window_bound_strictly_below_p_half':max(bounds)<P//2,'six_input_basis_roundtrips':6,'six_input_scores_no_modular_wrap':True,'new_model_forwards':0,'new_crypto_runs':0,'snapshots':[{'revision':s['revision'],'correct':s['correct'],'total':16} for s in snapshots],'sources_unchanged':all(sha(Path(k))==v for k,v in registry['source_sha256'].items())}
 save(HERE/'PREPARATION.json',check);print(json.dumps(check))
if __name__=='__main__':main()
