"""Actual BFV kernel workflow on the fixed continuing eight-intent stream."""
import collections,json,time
import numpy as np
from model import HERE,OLD,Model,save
start=time.perf_counter()
def main():
 data=json.loads((OLD/'data/selected.json').read_text());features=np.load(HERE/'features.npz');labels=json.loads((OLD/'config.json').read_text())['classes'];reference=json.loads((HERE/'plaintext_result.json').read_text())
 selected=[i for label in labels for i,r in [(j,r) for j,r in enumerate(data['test']) if r['category']==label][:2]]
 assert len(selected)==16;save(HERE/'encrypted_selection.json',{'test_indices':selected,'checkpoints':[32,64,128],'scope':'First2 original test rows per class, fixed reused-data integration slice, not a new utility estimate'})
 m=Model.create(HERE/'models/bfv','bfv');history=collections.defaultdict(list);tickets=[];expiries=0
 for i,(r,v) in enumerate(zip(data['train'],features['train']),1):
  expiries+=m.teach_vector(r['category'],v)['expired'];history[r['category']].append(v)
  if i in [32,64,128]:
   for qi,index in enumerate(selected):
    ticket=m.public_query(features['test'][index],f'r{i:03}-q{index:03}')
    expected={l:[int(v@features['test'][index])**2 for v in rows[-8:]] for l,rows in history.items()}
    tickets.append({'revision':i,'test_index':index,'ticket':ticket,'expected':expected})
   print(json.dumps({'public_revision':i,'queries':len(tickets),'elapsed_seconds':time.perf_counter()-start}),flush=True)
 public_elapsed=time.perf_counter()-start;save(HERE/'public_complete.json',{'learns':128,'expiries':expiries,'queries':48,'ct_ct_multiplications':320,'rotations':3200,'private_decryptions':0,'public_elapsed_seconds':public_elapsed,'all_public_subprocesses_returned':True})
 results=[];kernel_matches=0;sum_matches=0;prediction_matches=0
 for row in tickets:
  scores={}
  for label,path in row['ticket']['outputs'].items():
   raw=m.crypto('read',dir=m.root,ct=path);expected=row['expected'][label]
   assert raw['kernel_values']==expected,(row['revision'],row['test_index'],label)
   assert raw['sum_kernel']==sum(expected);kernel_matches+=8;sum_matches+=1;scores[label]=raw['sum_kernel']
  from model import rank
  pred=rank(scores,row['ticket']['counts'])['label'];assert pred==reference['checkpoints'][str(row['revision'])]['predictions'][row['test_index']];prediction_matches+=1
  results.append({'revision':row['revision'],'test_index':row['test_index'],'prediction':pred,'truth':data['test'][row['test_index']]['category'],'sum_scores':scores})
 costs=[json.loads(x) for x in (m.root/'operations.jsonl').read_text().splitlines()];commands={}
 for command in sorted({r['command'] for r in costs}):
  rows=[r for r in costs if r['command']==command];commands[command]={'calls':len(rows),'seconds':sum(r['elapsed_seconds'] for r in rows),'mean_seconds':sum(r['elapsed_seconds'] for r in rows)/len(rows)}
 save(HERE/'encrypted_predictions.json',results)
 report={'ok':True,'learns':128,'expiries':expiries,'multiclass_queries':48,'ct_ct_multiplications':320,'rotations':3200,'exact_kernel_value_matches':kernel_matches,'exact_class_sum_matches':sum_matches,'prediction_matches':prediction_matches,'public_elapsed_seconds':public_elapsed,'total_elapsed_seconds':time.perf_counter()-start,'commands':commands,'public_before_private':True,'scope':'Actual nonlinear BFV execution; reused-test integration slice; public label/lane/query; full reader key; new adapter'}
 save(HERE/'encrypted_result.json',report);print(json.dumps(report,indent=2))
if __name__=='__main__':main()
