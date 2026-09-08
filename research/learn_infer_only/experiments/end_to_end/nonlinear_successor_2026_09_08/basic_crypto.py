"""Necessary new-packing check: all8 lanes and one replacement, actual text vectors."""
import json,time
import numpy as np
from model import HERE,OLD,Model,save
start=time.perf_counter();data=json.loads((OLD/'data/selected.json').read_text());features=np.load(HERE/'features.npz');label='card_arrival';indices=[i for i,r in enumerate(data['train']) if r['category']==label][:9]
m=Model.create(HERE/'models/basic','bfv');slots=[None]*8
for j,i in enumerate(indices):m.teach_vector(label,features['train'][i]);slots[j%8]=features['train'][i]
q=features['test'][0];ticket=m.public_query(q,'basic',trace=True);raw=m.crypto('read',dir=m.root,ct=ticket['outputs'][label]);expected=[int(v@q)**2 for v in slots]
assert raw['kernel_values']==expected and raw['sum_kernel']==sum(expected)
save(HERE/'basic_crypto_result.json',{'ok':True,'learns':9,'expiries':1,'lane_matches':8,'all8192_slots_repeat8':raw['all8192_slots_repeat8'],'expected_kernel_values':expected,'sum_kernel':sum(expected),'elapsed_seconds':time.perf_counter()-start,'scope':'Actual saved text features; necessary packing/ct×ct correctness check, not accuracy evaluation'})
print(json.dumps(json.loads((HERE/'basic_crypto_result.json').read_text())))
