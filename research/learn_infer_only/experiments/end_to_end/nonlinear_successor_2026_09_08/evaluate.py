"""One nonlinear law, two fixed linear controls on reused data; no model rerun."""
import json,time
import numpy as np
from model import HERE,OLD,Model,transform,save
START=time.perf_counter()
def metrics(pred,rows):return {'correct':sum(p==r['category'] for p,r in zip(pred,rows)),'total':len(rows)}
def main():
 data=json.loads((OLD/'data/selected.json').read_text());old=np.load(OLD/'features.npz');train=transform(old['train']);test=transform(old['test']);np.savez(HERE/'features.npz',train=train,test=test)
 m=Model.create(HERE/'models/plain','plain');checkpoints={};updates=[];reference=json.loads((OLD/'plaintext_result.json').read_text())
 for i,(r,v) in enumerate(zip(data['train'],train),1):
  updates.append(m.teach_vector(r['category'],v))
  if i in [32,64,96,128]:
   nonlinear=[m.query_vector(q) for q in test];pred=[r['label'] for r in nonlinear];sums={l:np.sum([v for v in e['slots'] if v is not None],axis=0) for l,e in m.state['classes'].items()}
   labels=sorted(sums);matrix=test@np.array([sums[l] for l in labels]).T
   assert len({e['count'] for e in m.state['classes'].values()})==1
   linear=[labels[j] for j in np.argmax(matrix,axis=1)];original=reference['checkpoints'][str(i)]['predictions']
   row={'revision':i,'nonlinear':metrics(pred,data['test']),'requantized_linear':metrics(linear,data['test']),'original_linear':metrics(original,data['test']),'nonlinear_vs_requantized_changed':sum(a!=b for a,b in zip(pred,linear)),'nonlinear_gains_over_requantized':sum(a==r['category'] and b!=r['category'] for a,b,r in zip(pred,linear,data['test'])),'nonlinear_losses_vs_requantized':sum(a!=r['category'] and b==r['category'] for a,b,r in zip(pred,linear,data['test'])),'predictions':pred,'sum_scores':[{x['label']:x['sum_kernel'] for x in r['ranking']} for r in nonlinear]}
   checkpoints[str(i)]=row;print(json.dumps({k:v for k,v in row.items() if k not in ['predictions','sum_scores']}),flush=True)
 result={'checkpoints':checkpoints,'learns':128,'expiries':sum(u['expired'] for u in updates),'max_feature_norm_squared':int(max(np.max(np.sum(train*train,axis=1)),np.max(np.sum(test*test,axis=1)))),'new_model_forwards':0,'architectures_tested':1,'hyperparameter_searches':0,'scope':'Reused-test exploratory comparison; no fresh held-out estimate','elapsed_seconds':time.perf_counter()-START}
 save(HERE/'plaintext_result.json',result)
if __name__=='__main__':main()
