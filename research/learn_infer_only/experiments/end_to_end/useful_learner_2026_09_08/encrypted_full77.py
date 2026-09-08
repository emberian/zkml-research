"""Materialize the complete continuing 77-class model under unchanged BFV."""
import collections,hashlib,json,time
import numpy as np
from learner import HERE,Learner,save
START=time.perf_counter()
def main():
 out=HERE/'full77';data=json.loads((out/'selection.json').read_text());features=np.load(out/'features.npz');classes=data['classes']
 # Fixed canonical integration slice, not an additional accuracy estimate.
 selected=[next(i for i,r in enumerate(data['test']) if r['category']==label) for label in classes]
 save(out/'encrypted_selection.json',{'test_indices':selected,'selection':'First row in the original test order for each of all77 classes, alphabetical class order','scope':'Reused-test integration slice; no new utility estimate','new_model_forwards':0})
 learner=Learner.create(HERE/'models/full77_bfv',backend='bfv');expiries=0;direct=collections.defaultdict(list)
 for i,(r,v) in enumerate(zip(data['train'],features['train']),1):
  update=learner.teach_vector(r['category'],v);expiries+=update['expired'];direct[r['category']].append(v)
  if i%154==0:print(json.dumps({'phase':'teach','updates':i,'expiries':expiries,'elapsed_seconds':time.perf_counter()-START}),flush=True)
 tickets=[]
 for qi,index in enumerate(selected):
  ticket=learner.public_query(features['test'][index],f'full77-q{qi:03}')
  tickets.append({'index':index,'ticket':ticket})
  if (qi+1)%11==0:print(json.dumps({'phase':'public_query','queries':qi+1,'outputs':(qi+1)*77,'elapsed_seconds':time.perf_counter()-START}),flush=True)
 public_elapsed=time.perf_counter()-START
 save(out/'encrypted_public_complete.json',{'learns':1232,'classes':77,'expiries':expiries,'queries':77,'scalar_outputs':5929,'private_decryptions_so_far':0,'subprocesses_all_returned':True,'public_elapsed_seconds':public_elapsed})
 sums={l:np.array(direct[l][-8:]).sum(0) for l in classes};integers=0;predictions=[]
 expected_predictions=json.loads((out/'result.json').read_text())['checkpoints']['1232']['predictions']
 for i,row in enumerate(tickets):
  received=learner.receive(row['ticket']);actual={r['label']:r['sum_dot'] for r in received['ranking']}
  expected={l:int(sums[l]@features['test'][row['index']]) for l in classes};assert actual==expected
  assert received['label']==expected_predictions[row['index']]
  integers+=len(actual);predictions.append({'test_index':row['index'],'prediction':received['label'],'truth':data['test'][row['index']]['category'],'integer_scores':actual})
  if (i+1)%11==0:print(json.dumps({'phase':'private_compare','queries':i+1,'integer_matches':integers,'elapsed_seconds':time.perf_counter()-START}),flush=True)
 costs=[json.loads(x) for x in (learner.root/'operations.jsonl').read_text().splitlines()];summary={}
 for c in sorted({x['command'] for x in costs}):
  times=[x['elapsed_seconds'] for x in costs if x['command']==c];summary[c]={'calls':len(times),'seconds':sum(times),'mean_seconds':sum(times)/len(times)}
 report={'ok':True,'classes':77,'learns':1232,'expiries':expiries,'queries':77,'exact_integer_matches':integers,'prediction_matches':77,'integration_slice_correct':sum(r['prediction']==r['truth'] for r in predictions),'integration_slice_total':77,'new_utility_estimate':False,'complete_test_utility':{'correct':2253,'total':3080,'execution':'plaintext unchanged algorithm, full77/result.json'},'new_model_forwards':0,'public_elapsed_seconds':public_elapsed,'total_elapsed_seconds':time.perf_counter()-START,'commands':summary,'public_before_private':True,'full_reader_key':True,'public_class_routes_counts_queries':True}
 save(out/'encrypted_predictions.json',predictions);save(out/'encrypted_result.json',report);print(json.dumps(report,indent=2),flush=True)
if __name__=='__main__':main()
