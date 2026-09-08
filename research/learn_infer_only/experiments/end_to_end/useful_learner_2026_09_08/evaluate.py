"""One fixed dataset split; no validation search or model fine-tuning."""
import hashlib,json,platform,time
from pathlib import Path
import numpy as np
from encoder import Encoder,CFG,HERE
from learner import Learner,save
START=time.perf_counter()
def metrics(pred,records):
 labels=CFG['classes'];truth=[r['category'] for r in records]
 result={'correct':sum(a==b for a,b in zip(pred,truth)),'total':len(truth)}
 result['accuracy']=result['correct']/result['total']
 result['by_class']={l:{'correct':sum(p==l for p,t in zip(pred,truth) if t==l),'total':sum(t==l for t in truth)} for l in labels}
 for name,group in [('original_four',labels[:4]),('introduced_four',labels[4:])]:
  result[name]={'correct':sum(p==t for p,t in zip(pred,truth) if t in group),'total':sum(t in group for t in truth)}
 return result
def main():
 data=json.loads((HERE/'data/selected.json').read_text());allrows=data['train']+data['test']
 # Match the existing inspected model inventory before first forward.
 inv=json.loads((HERE.parent/'utility/encoder_feasibility/candidates.json').read_text())[CFG['model']]
 for name,row in inv['files'].items():assert hashlib.sha256((Path(CFG['model_path'])/name).read_bytes()).hexdigest()==row['sha256'],name
 encoder=Encoder();vectors=encoder.encode([r['text'] for r in allrows]);np.savez(HERE/'features.npz',train=vectors[:128],test=vectors[128:])
 save(HERE/'encoder_result.json',dict(encoder.stats,model_revision=CFG['revision'],model_files=inv['files'],projection_sha256=hashlib.sha256(encoder.projection.tobytes()).hexdigest(),feature_sha256=hashlib.sha256((HERE/'features.npz').read_bytes()).hexdigest(),total_seconds=time.perf_counter()-START,python=platform.python_version()))
 learner=Learner.create(HERE/'models/plain');checkpoints={};prequential=[];history={l:[] for l in CFG['classes']};updates=[]
 def checkpoint():
  out=[learner.query_vector(v) for v in vectors[128:]];pred=[r['label'] for r in out]
  row={'revision':learner.state['revision'],'metrics':metrics(pred,data['test']),'predictions':pred,'sum_scores':[{r['label']:r['sum_dot'] for r in o['ranking']} for o in out],'counts':learner.status()['classes']}
  checkpoints[str(learner.state['revision'])]=row
  print(json.dumps({'checkpoint':learner.state['revision'],'metrics':row['metrics']}),flush=True)
 checkpoint()
 for i,(record,vector) in enumerate(zip(data['train'],vectors[:128]),1):
  pred=learner.query_vector(vector)['label'];prequential.append({'event':i,'prediction':pred,'truth':record['category'],'correct':pred==record['category']})
  updates.append(learner.teach_vector(record['category'],vector))
  history[record['category']].append(vector.tolist())
  for label,entry in learner.state['classes'].items():
   expected=np.array(history[label][-8:],dtype=np.int64).sum(0).tolist()
   assert entry['sum']==expected and len(entry['queue'])==min(8,len(history[label]))
  if i in [4,16,32,36,48,64,96,128]:checkpoint()
  if i==64:
   old_before={l:np.sum(history[l][-8:],axis=0).tolist() for l in CFG['classes'][:4]}
   assert all(learner.state['classes'][l]['sum']==old_before[l] for l in CFG['classes'][:4])
 report={'checkpoints':checkpoints,'updates':updates,'prequential':prequential,'prequential_correct':sum(r['correct'] for r in prequential),'prequential_total':128,'expiries':sum(r['expired'] for r in updates),'uninformed_majority_correct':40,'test_count':320,'test_labels_used_for_updates':False,'model_fine_tuning':False,'hyperparameter_searches':0,'integer_state_checks':128,'selected_sha256':hashlib.sha256((HERE/'data/selected.json').read_bytes()).hexdigest(),'elapsed_seconds':time.perf_counter()-START}
 save(HERE/'plaintext_result.json',report)
if __name__=='__main__':main()
