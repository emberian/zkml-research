#!/usr/bin/env python3
"""Adapt the pinned known-public cached learner arrays; never invokes an encoder."""
from pathlib import Path
import hashlib,json,math,struct
import numpy as np

OUT=Path(__file__).resolve().parent
SOURCE=OUT.parents[2]/'learn_infer_only/experiments/end_to_end/useful_learner_2026_09_08'
PINS={
 'models/plain/learner.json':'9aa42d447794a8c685924ff89b745857b753ec7f83c70480f41e9e2ba65979d8',
 'features.npz':'03959f885631c4b095d81210b06def3e4071a1d9bf98e1c7427b1cd114aeaf6a',
 'data/selected.json':'5e1e10fce61b7074345bdee1e5cecf5768f5cdd91684e06fb37cf783abe2eb09',
 'plaintext_result.json':'0d2ea48a4640d660c3cef2c775a4113f05ae945c1156286a936a8ac8c6935a9d',
 'config.json':'1e051be559a01ce600f4434bf9a85c2585023f14e425d86c55cf0cd77a0ca5ee',
}
def main():
 for rel,h in PINS.items():assert hashlib.sha256((SOURCE/rel).read_bytes()).hexdigest()==h,rel
 config=json.loads((SOURCE/'config.json').read_text()); labels=config['classes']
 learner=json.loads((SOURCE/'models/plain/learner.json').read_text())
 selected=json.loads((SOURCE/'data/selected.json').read_text())['test']
 prior=json.loads((SOURCE/'plaintext_result.json').read_text())['checkpoints']['128']
 assert learner['revision']==128 and len(labels)==8
 indices=[next(i for i,row in enumerate(selected) if row['category']==label) for label in labels]
 prototype=np.array([learner['classes'][label]['sum'] for label in labels],dtype=np.int64)
 query=np.load(SOURCE/'features.npz')['test'][indices].astype(np.int64)
 assert prototype.shape==(8,577) and query.shape==(8,577)
 assert (prototype[:,-1]==0).all() and (query[:,-1]==0).all()
 prototype=prototype[:,:576];query=query[:,:576]
 assert all(prior['counts'][label]==8 for label in labels)
 scores=query@prototype.T
 assert all(int(scores[t,c])==prior['sum_scores'][i][label] for t,i in enumerate(indices) for c,label in enumerate(labels))
 decisions=[min(range(8),key=lambda c:(-int(scores[t,c]),labels[c])) for t in range(8)]
 assert [labels[c] for c in decisions]==[prior['predictions'][i] for i in indices]
 D=4096;W=16384;p1,p2=16381,16369;q=18446744069414584321;sigma=2**33
 assert math.gcd(p1,p2)==1
 score_bound=576*1016*127
 assert p1*p2>2*score_bound
 assert abs(prototype).max()<=1016 and abs(query).max()<=127
 positions=[(c//3)*D+(c%3)*1152 for c in range(8)]
 packed=[0]*W
 for c,pos in enumerate(positions):
  assert pos%D+1152<=D
  for limb,p in enumerate([p1,p2]):
   delta=q//p
   for t,v in enumerate(prototype[c]):packed[pos+limb*576+t]=delta*(int(v)%p)%q
 # Literal coefficient check for the existing reversed-negated matrix lift:
 # coefficient u is sum_t w[t] M[t+u] when every support position t+u<D.
 checks=0;wrong_shift_controls=0
 for t in range(8):
  for c,pos in enumerate(positions):
   for limb,p in enumerate([p1,p2]):
    u=limb*576
    literal=sum(int(query[t,f])*packed[pos+f+u] for f in range(576))%q
    T=sum(int(query[t,f])*(int(prototype[c,f])%p) for f in range(576))
    assert literal==(q//p)*T%q
    assert T%p==int(scores[t,c])%p
    checks+=1
   wrong=sum(int(query[t,f])*packed[pos+f+577] for f in range(576))%q
   correct=sum(int(query[t,f])*packed[pos+f+576] for f in range(576))%q
   wrong_shift_controls+=wrong!=correct
 l1=[int(abs(row).sum()) for row in query]
 l2sq=[int((row*row).sum()) for row in query]
 # A 16-sigma weighted Gaussian condition plus per-sample rounding error.
 # Integer ceil sqrt keeps the conditional arithmetic bound conservative.
 bounds=[]
 for t in range(8):
  root=math.isqrt(l2sq[t]);root+=root*root<l2sq[t]
  e_bound=16*sigma*root+(l1[t]+1)//2
  for p in [p1,p2]:
   r=q%p;T_bound=(p-1)*l1[t]
   assert 2*(p*e_bound+r*T_bound)<q
   bounds.append({'query':t,'plaintext_modulus':p,'delta':q//p,'q_remainder':r,
     'weighted_error_bound':e_bound,'absolute_unreduced_residue_score_bound':T_bound,
     'twice_decoder_error_numerator':2*(p*e_bound+r*T_bound),'required_strict_upper_bound':q})
 output=bytearray(b'LRNJ0001')
 for n in [D,W,64,576,8,8,p1,p2,128]:output.extend(struct.pack('<Q',n))
 for label in labels:
  raw=label.encode();output.extend(struct.pack('<Q',len(raw)));output.extend(raw)
 for i in indices:output.extend(struct.pack('<Q',i))
 for array in [prototype,query,scores]:output.extend(np.asarray(array,dtype='<i8').tobytes(order='C'))
 for c in decisions:output.extend(struct.pack('<Q',c))
 (OUT/'learner_inputs.bin').write_bytes(output)
 report={'status':'PASS','source_root':str(SOURCE),'source_sha256':PINS,'selection_rule':'first original cached test row per class in config class order',
  'labels':labels,'test_indices':indices,'selected_public_rows':[selected[i] for i in indices],
  'revision':128,'active_examples_per_class':8,'features':576,'discarded_bias_coordinate':'577th coordinate exactly zero in all inputs',
  'prototype_range':[int(prototype.min()),int(prototype.max())],'query_range':[int(query.min()),int(query.max())],
  'scores':scores.tolist(),'predictions':[labels[c] for c in decisions],'decisions_correct_in_reused_eight':sum(labels[decisions[t]]==labels[t] for t in range(8)),
  'signed_score_bound':score_bound,'crt_moduli':[p1,p2],'crt_product':p1*p2,'class_start_positions':positions,
  'literal_shifted_coefficient_checks':checks,'wrong_577_shift_differs':wrong_shift_controls,
  'query_l1':l1,'query_l2_squared':l2sq,'conditional_decode_bounds':bounds,
  'ideal_gaussian_union_bound':128*2*math.exp(-128),
  'probability_scope':'Only an ideal independent Gaussian model before rounding; this is not a rigorous analysis of the floating-point rand_distr sampler.',
  'input_bytes':len(output),'input_sha256':hashlib.sha256(output).hexdigest(),
  'adapter_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
 (OUT/'input_reference.json').write_text(json.dumps(report,indent=2)+'\n')
 print(json.dumps({k:report[k] for k in ['status','test_indices','prototype_range','query_range','signed_score_bound','crt_product','literal_shifted_coefficient_checks','wrong_577_shift_differs','input_bytes','input_sha256','ideal_gaussian_union_bound']},indent=2))
if __name__=='__main__':main()
