"""Actual encrypted continuing prototypes; all public computation before score decode."""
import collections,hashlib,json,time
from pathlib import Path
import numpy as np
from learner import HERE,CFG,Learner,save,BINARY,BINARY_SHA
from evaluate import metrics
START=time.perf_counter()
def main():
 data=json.loads((HERE/'data/selected.json').read_text());reference=json.loads((HERE/'plaintext_result.json').read_text());features=np.load(HERE/'features.npz')
 learner=Learner.create(HERE/'models/bfv',backend='bfv');tickets=[];updates=[]
 for revision,(record,vector) in enumerate(zip(data['train'],features['train']),1):
  updates.append(learner.teach_vector(record['category'],vector))
  if revision in [32,64,128]:
   for qi,query in enumerate(features['test']):
    ticket=learner.public_query(query,f'r{revision:03}-q{qi:03}')
    tickets.append({'revision':revision,'query_index':qi,'ticket':ticket})
    if (qi+1)%40==0:print(json.dumps({'phase':'public','revision':revision,'queries_complete':qi+1,'elapsed_seconds':time.perf_counter()-START}),flush=True)
 save(HERE/'encrypted_public_complete.json',{'updates':len(updates),'expiries':sum(u['expired'] for u in updates),'queries':len(tickets),'scalar_outputs':sum(len(t['ticket']['outputs']) for t in tickets),'public_elapsed_seconds':time.perf_counter()-START,'binary_sha256':BINARY_SHA,'source_sha256':hashlib.sha256((HERE/'encrypted_evaluate.py').read_bytes()).hexdigest(),'private_decryptions_so_far':0,'subprocesses_all_returned':True})
 public_elapsed=time.perf_counter()-START;decoded=[];integer_matches=0;checkpoint_predictions=collections.defaultdict(list)
 for i,entry in enumerate(tickets):
  received=learner.receive(entry['ticket']);scores={r['label']:r['sum_dot'] for r in received['ranking']}
  expected=reference['checkpoints'][str(entry['revision'])]['sum_scores'][entry['query_index']]
  assert scores==expected,(entry['revision'],entry['query_index'])
  integer_matches+=len(scores);checkpoint_predictions[entry['revision']].append(received['label'])
  decoded.append({'revision':entry['revision'],'query_index':entry['query_index'],'label':received['label'],'integer_scores':scores})
  if (i+1)%80==0:print(json.dumps({'phase':'private_compare','queries_complete':i+1,'integer_matches':integer_matches,'elapsed_seconds':time.perf_counter()-START}),flush=True)
 costs=[json.loads(line) for line in (learner.root/'operations.jsonl').read_text().splitlines()]
 summaries={}
 for command in sorted({r['command'] for r in costs}):
  rows=[r for r in costs if r['command']==command];times=[r['elapsed_seconds'] for r in rows]
  summaries[command]={'calls':len(rows),'seconds':sum(times),'mean_seconds':sum(times)/len(times),'max_seconds':max(times)}
 checkpoint_results={str(k):metrics(v,data['test']) for k,v in checkpoint_predictions.items()}
 for k,pred in checkpoint_predictions.items():assert pred==reference['checkpoints'][str(k)]['predictions']
 save(HERE/'encrypted_predictions.json',decoded)
 report={'ok':True,'learns':128,'expiries':sum(u['expired'] for u in updates),'queries':len(tickets),'exact_integer_matches':integer_matches,'prediction_matches':len(tickets),'checkpoint_results':checkpoint_results,'public_elapsed_seconds':public_elapsed,'total_elapsed_seconds':time.perf_counter()-START,'commands':summaries,'private_after_public_complete':True,'decryption_semantics':'Full-key BFV reader internally decrypts complete polynomial; this experiment compares coefficient576 only. No restricted release.','queries_public':True,'classes_and_counts_public':True,'encoder_plaintext':True,'cryptographic_backend_changed':False,'new_wrapper_previously_verified':False}
 save(HERE/'encrypted_result.json',report);print(json.dumps(report,indent=2),flush=True)
if __name__=='__main__':main()
