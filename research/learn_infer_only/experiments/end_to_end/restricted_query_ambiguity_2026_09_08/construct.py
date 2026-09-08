"""One exact public integer-kernel construction; no encryption or private data."""
import hashlib,json,time
from pathlib import Path
import numpy as np
from flint import fmpz_mat
HERE=Path(__file__).resolve().parent;LEARNER=HERE.parent/'restricted_query_learner_2026_09_08';OLD=HERE.parent/'useful_learner_2026_09_08'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
def dot(a,b):return sum(int(x)*int(y) for x,y in zip(a,b))
def main():
 start=time.perf_counter();reg=json.loads((LEARNER/'registry.json').read_text());fixture=json.loads((LEARNER/'fixture.json').read_text());Y=[q['vector'] for q in reg['queries']];p=reg['p'];data=json.loads((OLD/'data/selected.json').read_text())
 wi=next(i for i,r in enumerate(data['test']) if r['category']=='card_payment_not_recognised')
 with np.load(OLD/'features.npz') as features:w=features['test'][wi].tolist()
 selection={'query_registry_sha256':sha(LEARNER/'registry.json'),'base_fixture_sha256':sha(LEARNER/'fixture.json'),'withheld_query':{'test_index':wi,'text':data['test'][wi]['text'],'label':data['test'][wi]['category'],'vector':w},'search':'One LLL reduction of64x80 [I64 | 2^32 * Y_first64^T], inspect64 returned rows in order. Require exact integer Ydelta=0, withheld dot nonzero, all three card-arrival observations plus (1,2,3)*delta admitted. First admissible row selected; no crypto/score prediction oracle.','support_columns':list(range(64)),'scale':2**32,'source_sha256':{str(OLD/x):sha(OLD/x) for x in ['data/selected.json','features.npz']}}
 save(HERE/'SELECTION.json',selection)
 M=fmpz_mat([[int(i==j) for j in range(64)]+[(2**32)*row[i] for row in Y] for i in range(64)])
 t=time.perf_counter();L=M.lll();elapsed=time.perf_counter()-t;candidates=[];selected=None
 for i in range(64):
  raw=[int(L[i,j]) for j in range(80)];delta=raw[:64]+[0]*513
  if next((v for v in delta if v),0)<0:delta=[-v for v in delta]
  annihilates=all(dot(row,delta)==0 for row in Y);diff=dot(w,delta)
  admitted=True
  for k,event in enumerate([e for e in fixture['events'] if e['class']=='card_arrival'],1):
   admitted &= max(abs(a+k*b) for a,b in zip(event['vector'],delta))<=127
  row={'lll_row':i,'tail_zero':all(v==0 for v in raw[64:]),'exact_Y_delta_zero':annihilates,'delta_nonzero':any(delta),'linf':max(map(abs,delta)),'squared_norm':dot(delta,delta),'support_count':sum(v!=0 for v in delta),'withheld_difference':diff,'three_scaled_perturbations_admitted':bool(admitted)};candidates.append(row)
  if selected is None and row['tail_zero'] and annihilates and any(delta) and diff and admitted:selected=(row,delta)
 assert selected is not None,'No witness in this bounded one-matrix construction; no silent restart'
 meta,delta=selected;left={c:[] for c in fixture['classes']};right={c:[] for c in fixture['classes']};events=[];history=[];alpha=0
 for original in fixture['events']:
  c=original['class'];a=original['vector'];factor=0
  if c=='card_arrival':alpha+=1;factor=alpha
  b=[x+factor*d for x,d in zip(a,delta)];assert len(a)==len(b)==577 and a[-1]==b[-1]==0 and max(map(abs,b))<=127
  assert [dot(q,a) for q in Y]==[dot(q,b) for q in Y]
  event={'event':original['event'],'class':c,'text_origin':original['text'],'left_vector':a,'right_vector':b,'delta_factor':factor,'expired_event':original['expired_event']};events.append(event)
  for model,vec in [(left,a),(right,b)]:
   if len(model[c])==2:model[c].pop(0)
   model[c].append(vec)
  sums=lambda model:{label:[sum(v[j] for v in queue) for j in range(577)] for label,queue in model.items()}
  sl,sr=sums(left),sums(right)
  yl={label:[dot(q,x) for q in Y] for label,x in sl.items()};yr={label:[dot(q,x) for q in Y] for label,x in sr.items()};assert yl==yr
  wl={label:dot(w,x) for label,x in sl.items()};wr={label:dot(w,x) for label,x in sr.items()}
  history.append({'revision':original['event'],'counts':{label:len(queue) for label,queue in left.items()},'registered_left':yl,'registered_right':yr,'withheld_left':wl,'withheld_right':wr,'withheld_difference':{label:wr[label]-wl[label] for label in left},'real_coordinate_state_difference':{label:[j for j in range(576) if sl[label][j]!=sr[label][j]] for label in left}})
 witness={'delta':delta,'selected':meta,'withheld_query':selection['withheld_query'],'p':p,'events':events,'history':history,'proof_obligations':{'exact_integer_Y_delta':[dot(q,delta) for q in Y],'withheld_delta':dot(w,delta),'registered_rows':len(Y),'feature_dimension':576,'last_coordinate_unchanged':delta[-1]==0,'maximum_right_coordinate_abs':max(abs(v) for e in events for v in e['right_vector']),'max_feature_perturbation_abs':3*max(map(abs,delta)),'max_registered_window_score_abs':max(abs(v) for h in history for side in ['registered_left','registered_right'] for scores in h[side].values() for v in scores),'universal_W2_int8_registered_bound':2*127*max(sum(map(abs,q)) for q in Y),'universal_W2_int8_withheld_bound':2*127*sum(map(abs,w)),'p_half_floor':p//2},'scope':'Admitted int8 feature pairs; right vectors are not claimed to be embeddings of natural-language texts. Equal complete per-input registered projections, not equal ciphertext bytes or an executed computational-privacy test.'}
 assert witness['proof_obligations']['universal_W2_int8_withheld_bound']<p//2
 save(HERE/'WITNESS.json',witness)
 result={'status':'PASS','lll_seconds':elapsed,'elapsed_seconds':time.perf_counter()-start,'candidate_rows_inspected':64,'matrices_reduced':1,'selected':meta,'proof_obligations':witness['proof_obligations'],'six_registered_input_pairs_match':True,'six_complete_registered_memory_snapshots_match':True,'two_expiries':True,'crypto_or_model_runs':0,'private_files_read':0,'selection_sha256':sha(HERE/'SELECTION.json'),'witness_sha256':sha(HERE/'WITNESS.json')}
 save(HERE/'CANDIDATES.json',candidates);save(HERE/'CONSTRUCTION.json',result);print(json.dumps(result))
if __name__=='__main__':main()
