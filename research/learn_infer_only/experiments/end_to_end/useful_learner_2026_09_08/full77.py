"""The unchanged learner on every BANKING77 class, with a fixed train/test split."""
import csv,hashlib,json,time
from pathlib import Path
import numpy as np
from learner import HERE,Learner,save
from encoder import Encoder
START=time.perf_counter()
OUT=HERE/'full77'
def main():
 OUT.mkdir()
 train=list(csv.DictReader((HERE/'data/train.csv').open()));test=list(csv.DictReader((HERE/'data/test.csv').open()));labels=sorted({r['category'] for r in train});assert len(labels)==77 and len(test)==3080
 testtexts={r['text'].strip().casefold() for r in test};chosen={}
 for label in labels:
  rows=[dict(r,source_row=i) for i,r in enumerate(train) if r['category']==label and r['text'].strip().casefold() not in testtexts]
  rows.sort(key=lambda r:hashlib.sha256(('useful-learner-2026-09-08:'+r['text']).encode()).digest());chosen[label]=rows[:16];assert len(chosen[label])==16
 schedule=[]
 for group,indices in [(labels[:38],range(8)),(labels[38:],range(8)),(labels,range(8,16))]:
  for i in indices:
   for label in group:schedule.append(chosen[label][i])
 save(OUT/'selection.json',{'classes':labels,'train':schedule,'test':test,'schedule':'8 rounds first38 alphabetic classes; 8 rounds remaining39; then8 rounds all77','unchanged_algorithm':True,'settings_selected_using_this_test':False})
 encoder=Encoder();features=encoder.encode([r['text'] for r in schedule+test]);trainx=features[:1232];testx=features[1232:]
 np.savez(OUT/'features.npz',train=trainx,test=testx)
 save(OUT/'encoder_result.json',dict(encoder.stats,feature_sha256=hashlib.sha256((OUT/'features.npz').read_bytes()).hexdigest(),elapsed_seconds=time.perf_counter()-START))
 learner=Learner.create(HERE/'models/full77');truth=np.array([labels.index(r['category']) for r in test]);checkpoints={};snapshots=[]
 def checkpoint():
  active=sorted(learner.state['classes'])
  sums=np.array([learner.state['classes'][l]['sum'] for l in active],dtype=np.int64);counts=np.array([len(learner.state['classes'][l]['queue']) for l in active])
  assert np.all(counts==8)
  scores=testx@sums.T;predlabels=[active[i] for i in np.argmax(scores,axis=1)];pred=np.array([labels.index(l) for l in predlabels]);correct=pred==truth
  result={'revision':learner.state['revision'],'classes':len(active),'correct':int(correct.sum()),'total':3080,'accuracy':float(correct.mean()),'first38_correct':int(correct[truth<38].sum()),'first38_total':1520,'new39_correct':int(correct[truth>=38].sum()),'new39_total':1560,'by_class':{l:int(correct[truth==i].sum()) for i,l in enumerate(labels)},'predictions':predlabels}
  # A direct CLI implementation query checks the vectorized arithmetic path at 3 fixed rows.
  for qi in [0,1540,3079]:assert learner.query_vector(testx[qi])['label']==predlabels[qi]
  checkpoints[str(learner.state['revision'])]=result;snapshots.append(sums.copy())
  print(json.dumps({k:v for k,v in result.items() if k not in ['by_class','predictions']}),flush=True)
 expiries=0
 for i,(record,vector) in enumerate(zip(schedule,trainx),1):
  expiries+=learner.teach_vector(record['category'],vector)['expired']
  if i in [304,616,1232]:checkpoint()
  if i==616:
   assert np.array_equal(snapshots[0],snapshots[1][:38])
 result={'ok':True,'classes':77,'learns':1232,'expiries':expiries,'heldout_queries_per_checkpoint':3080,'checkpoints':checkpoints,'old38_prototypes_unchanged_during_class_addition':True,'encrypted_full77_executed':False,'algorithm_changes':0,'hyperparameter_searches':0,'elapsed_seconds':time.perf_counter()-START}
 save(OUT/'result.json',result)
if __name__=='__main__':main()
