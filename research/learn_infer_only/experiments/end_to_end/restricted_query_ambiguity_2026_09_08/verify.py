"""Standard-library exact certificate check; no LLL, model, crypto or key reads."""
import ast,hashlib,json,struct,zipfile
from pathlib import Path
HERE=Path(__file__).resolve().parent;LEARNER=HERE.parent/'restricted_query_learner_2026_09_08'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
def dot(a,b):return sum(x*y for x,y in zip(a,b))
def npz_integer_row(path,name,index):
 with zipfile.ZipFile(path) as archive:raw=archive.read(name+'.npy')
 assert raw[:6]==b'\x93NUMPY';major=raw[6]
 if major==1:header_len=struct.unpack_from('<H',raw,8)[0];start=10
 elif major==2:header_len=struct.unpack_from('<I',raw,8)[0];start=12
 else:raise ValueError('unsupported NumPy container version')
 header=ast.literal_eval(raw[start:start+header_len].decode('latin1'));assert header['descr']=='<i8' and not header['fortran_order'];rows,cols=header['shape'];assert 0<=index<rows and len(raw)==start+header_len+8*rows*cols
 return list(struct.unpack_from('<'+'q'*cols,raw,start+header_len+index*cols*8))
def main():
 w=json.loads((HERE/'WITNESS.json').read_text());s=json.loads((HERE/'SELECTION.json').read_text());reg=json.loads((LEARNER/'registry.json').read_text());fixture=json.loads((LEARNER/'fixture.json').read_text());delta=w['delta'];p=reg['p'];Y=[q['vector'] for q in reg['queries']]
 assert sha(LEARNER/'registry.json')==s['query_registry_sha256'] and sha(LEARNER/'fixture.json')==s['base_fixture_sha256']
 assert all(sha(Path(path))==h for path,h in s['source_sha256'].items())
 old=HERE.parent/'useful_learner_2026_09_08';data=json.loads((old/'data/selected.json').read_text());unregistered=w['withheld_query'];i=unregistered['test_index']
 assert i==next(j for j,q in enumerate(data['test']) if q['category']=='card_payment_not_recognised')
 assert unregistered['vector']==npz_integer_row(old/'features.npz','test',i)
 assert unregistered['text']==data['test'][i]['text'] and unregistered['label']==data['test'][i]['category']
 assert len(delta)==577 and delta[-1]==0 and all(type(v) is int for v in delta) and any(delta[:576]);assert all(dot(q,delta)==0 for q in Y)
 h=unregistered['vector'];diff=dot(h,delta);assert diff and diff%p
 left={c:[] for c in fixture['classes']};right={c:[] for c in fixture['classes']};maxstate=0;score_matches=0;all_input_matches=0;seen_factors=[];rows=[]
 for original,event,record in zip(fixture['events'],w['events'],w['history']):
  assert event['left_vector']==original['vector'] and event['class']==original['class'] and event['event']==original['event'] and event['expired_event']==original['expired_event']
  factor=event['delta_factor'];seen_factors.append(factor);a=event['left_vector'];b=event['right_vector'];assert b==[x+factor*d for x,d in zip(a,delta)]
  assert all(type(v) is int and -127<=v<=127 for v in a+b) and a[-1]==b[-1]==0
  assert [dot(q,a) for q in Y]==[dot(q,b) for q in Y];all_input_matches+=16;c=event['class']
  for model,vector in [(left,a),(right,b)]:
   model[c].append((event['event'],vector))
   if len(model[c])>2:expired,_=model[c].pop(0);assert expired==event['expired_event']
   else:assert event['expired_event'] is None
  for label in fixture['classes']:
   sums=[[sum(vec[j] for _,vec in model[label]) for j in range(577)] for model in [left,right]]
   maxstate=max(maxstate,max(abs(v) for state in sums for v in state));projections=[[dot(q,state) for q in Y] for state in sums]
   assert projections[0]==projections[1]==record['registered_left'][label]==record['registered_right'][label];score_matches+=16
   actual=[dot(h,state) for state in sums];assert actual==[record['withheld_left'][label],record['withheld_right'][label]]
   rows.append({'revision':event['event'],'class':label,'registered_scores_match':True,'withheld_left':actual[0],'withheld_right':actual[1],'difference':actual[1]-actual[0]})
 assert seen_factors==[1,0,2,0,3,0]
 rb=2*127*max(sum(map(abs,q)) for q in Y);hb=2*127*sum(map(abs,h));assert max(rb,hb)<p//2
 result={'status':'PASS','registered_rows':16,'real_delta_support':sum(v!=0 for v in delta[:576]),'delta_linf':max(map(abs,delta)),'delta_squared_norm':dot(delta,delta),'integer_kernel_equalities':16,'withheld_dot_delta':diff,'withheld_not_in_registered_Fp_span':True,'exact_per_input_registered_score_matches':all_input_matches,'exact_memory_registered_score_matches':score_matches,'teaches_in_each_history':6,'expiries_in_each_history':2,'max_actual_state_coordinate_abs':maxstate,'registered_W2_signed_bound':rb,'withheld_W2_signed_bound':hb,'p_half_floor':p//2,'final_card_arrival_hidden_score_difference':rows[-2]['difference'],'rows':rows,'witness_sha256':sha(HERE/'WITNESS.json'),'verifier_sha256':sha(HERE/'verify.py'),'model_crypto_or_private_key_reads':0}
 (HERE/'VERIFICATION.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='rows'}))
if __name__=='__main__':main()
