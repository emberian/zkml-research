"""Frozen E5 projection, teacher calibration and exact W32 utility experiment."""
import argparse,hashlib,importlib.util,json,math,resource,sys,time
from collections import deque
from pathlib import Path
sys.dont_write_bytecode=True
import numpy as np
ROOT=Path(__file__).resolve().parent;UTILITY=ROOT.parent;BASE=UTILITY.parents[1]/'adaptation_utility'
sys.path.insert(0,str(BASE))
import text_transfer_data as olddata
import representation_data as repdata
from surfaces import make_records
spec=importlib.util.spec_from_file_location('old_attribute_surfaces',UTILITY/'attribute_calibration/data.py')
prior=importlib.util.module_from_spec(spec);spec.loader.exec_module(prior)
load=lambda p:json.loads(Path(p).read_text())
save=lambda p,x:Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def start():return time.perf_counter(),time.process_time()
def cost(t):return {'wall_seconds':time.perf_counter()-t[0],'cpu_seconds':time.process_time()-t[1],
 'process_high_water_rss_bytes_macos':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
def summary(values):
 v=np.array(values,dtype=float);sd=float(v.std(ddof=1)) if len(v)>1 else 0.
 return {'mean':float(v.mean()),'n_histories':len(v),'sd':sd,'normal95_half_width':1.96*sd/math.sqrt(len(v)),'min':float(v.min()),'max':float(v.max())}
def verify():
 for p,h in load(ROOT/'freeze.json')['source_sha256'].items():assert sha(p)==h,p
def quantize(v):return np.clip(np.rint(v*127),-127,127).astype(np.int8)
def prepare():
 assert not (ROOT/'freeze.json').exists(),'Preserve frozen outputs'
 records=make_records(load(BASE/'representation_records.json'),[olddata,repdata],prior)
 oldtexts={r['text'] for r in load(UTILITY/'attribute_calibration/records.json') if r['pool']=='test'}
 assert oldtexts.isdisjoint(r['text'] for r in records[256:])
 save(ROOT/'records.json',records);save(ROOT/'histories.json',{'seeds':list(range(66000,66064)),
   'histories':[olddata.history(s,records) for s in range(66000,66064)]})
 signs=2*np.random.Generator(np.random.PCG64(66901)).integers(0,2,size=(768,576),dtype=np.int8)-1
 assert set(np.unique(signs))=={-1,1};np.savez(ROOT/'projection.npz',signs=signs)
 save(ROOT/'projection.json',{'seed':66901,'generator':'numpy2.4.2 Generator(PCG64)','shape':[768,576],
   'distribution':'int8 uniform0/1 mapped to-1/+1, float64 divide24','signs_raw_sha256':hashlib.sha256(signs.tobytes()).hexdigest(),
   'npz_sha256':sha(ROOT/'projection.npz'),'candidate_projections_drawn':1})
 source=[ROOT/n for n in ['CONTRACT.md','surfaces.py','run.py','extract.py','records.json','histories.json','projection.json','projection.npz']]
 source +=[BASE/n for n in ['representation_records.json','representation_features.npz','representation_histories.json','text_transfer_data.py','representation_data.py']]
 source +=[UTILITY/n for n in ['encoder_policy.json','encoder_feasibility.json','nonlinear_successor/parameters.npz',
   'nonlinear_successor/preparation.json','nonlinear_successor/selection.json','attribute_calibration/calibration_policy.json',
   'attribute_calibration/selection.json','attribute_calibration/features.npz','attribute_calibration/data.py',
   'encoder_feasibility/candidates.json','encoder_feasibility/manifest.json']]
 save(ROOT/'freeze.json',{'source_sha256':{str(p):sha(p) for p in source},'new_texts':128,'new_histories':64,
   'exact_names_templates_cues_disjoint_from_three_generators':True,'new_attribute_supervision_primary':0,
   'model_forwards_so_far_in_this_experiment':0})
 print(json.dumps({'prepared':True,'freeze_sha256':sha(ROOT/'freeze.json'),'projection_sha256':sha(ROOT/'projection.npz')}))
def make_e5_features(hidden,routes,fit=False):
 """Only embeddings and public routes enter features; no labels/attributes."""
 t=start();R=np.load(ROOT/'projection.npz')['signs'].astype(np.float64)/24
 policy={} if fit else load(ROOT/'encoder_policy.json')['routes'];out={name:np.zeros((len(hidden),d),np.int8) for name,d in [('e5_projected577',577),('e5_raw769',769)]}
 for s in [0,1]:
  ids=np.where(routes==s)[0];teacher=[int(i) for i in ids if i<128];h=hidden[ids].astype(np.float64)
  if fit:
   center=hidden[teacher].astype(np.float64).mean(0);rho=float(np.sqrt(np.mean(np.sum((hidden[teacher]-center)**2,axis=1))))
   assert rho>0;policy[str(s)]={'center':center.tolist(),'rms_radius':rho,'teacher_ids':teacher,'scales':{}}
  p=policy[str(s)];u=(h-np.array(p['center']))/p['rms_radius'];matrices={'e5_projected577':u@R,'e5_raw769':u}
  for name,z in matrices.items():
   v=np.column_stack([z,np.ones(len(ids))])
   if fit:p['scales'][name]=float(np.linalg.norm(v[[j for j,rid in enumerate(ids) if rid<128]],axis=1).max())
   out[name][ids]=quantize(v/p['scales'][name])
 return out,policy,cost(t)
def old_features(hidden,routes):
 t=start();cfg=load(UTILITY/'encoder_policy.json')['policies_by_public_route'];out={};Q=np.zeros((len(hidden),577),np.int8);x=np.zeros_like(hidden,dtype=np.float64)
 for s in [0,1]:
  ids=np.where(routes==s)[0];p=cfg[str(s)];x[ids]=(hidden[ids]-np.array(p['center']))/p['scale']
  Q[ids]=quantize(np.column_stack([x[ids],np.full(len(ids),1/p['scale'])]))
 out['original577']=Q;pp=np.load(UTILITY/'nonlinear_successor/parameters.npz');Q=np.zeros_like(Q)
 assert load(UTILITY/'nonlinear_successor/selection.json')['chosen_k']['quadratic']==8
 for s in [0,1]:
  ids=np.where(routes==s)[0];z=(hidden[ids]-pp[f'r{s}_pca_center'])@pp[f'r{s}_basis32'][:8].T
  z/=pp[f'quadratic8_r{s}_std'];v=np.column_stack([z,*[z[:,i]*z[:,j] for i in range(8) for j in range(i,8)]])
  v-=pp[f'quadratic8_r{s}_offset'];Q[ids,:45]=quantize(np.column_stack([v,np.ones(len(ids))])/pp[f'quadratic8_r{s}_scale'])
 out['quadratic8']=Q;params=load(UTILITY/'attribute_calibration/calibration_policy.json')['fit_parameters'];Q=np.zeros_like(Q)
 for s in [0,1]:
  ids=np.where(routes==s)[0];p=np.clip(x[ids]@np.array(params[f'r{s}_coef'])+np.array(params[f'r{s}_intercept']),0,1)
  a,b=p.T;Q[ids,4*s:4*s+4]=quantize(np.column_stack([(1-a)*(1-b),(1-a)*b,a*(1-b),a*b]))
 out['calibrated_soft8']=Q
 return out,cost(t)
def run_history(H,records,Q,pool,independent=False):
 query=[r['id'] for r in records if r['pool']==pool];routes=np.array([records[i]['skill'] for i in query]);d=Q.shape[1]
 state=np.zeros((2,d),np.int64);queues=[deque(),deque()];states=[];scores=[];predictions=[];targets=[];checks=0
 for phase,ids in enumerate(H['phases'],1):
  for rid,y in zip(ids,olddata.labels(H,records,ids,flip0=phase==3)):
   s=records[rid]['skill'];v=int(y)*Q[rid].astype(np.int64);queues[s].append(v);state[s]+=v
   if len(queues[s])>32:state[s]-=queues[s].popleft()
  if independent:
   for s in [0,1]:
    assert state[s].tolist()==[sum(int(v[j]) for v in queues[s]) for j in range(d)];checks+=1
  scalar=np.einsum('ij,ij->i',state[routes],Q[query].astype(np.int64),dtype=np.int64)
  scores.append(scalar.tolist());predictions.append(np.where(scalar>=0,1,-1).tolist());targets.append(olddata.labels(H,records,query,flip0=phase==3).tolist());states.append(state.copy())
 assert np.array_equal(states[0][0],states[1][0]) and np.array_equal(states[1][1],states[2][1])
 assert predictions[0][:64]==predictions[1][:64] and predictions[1][64:]==predictions[2][64:]
 accuracy=lambda phase,s:float(np.mean(np.array(predictions[phase])[routes==s]==np.array(targets[phase])[routes==s]))
 metrics={'plant_initial':accuracy(0,0),'plant_after_letters':accuracy(1,0),'letter_after_learning':accuracy(1,1),
   'plant_changed':accuracy(2,0),'letter_retained':accuracy(2,1),'final_mean':(accuracy(2,0)+accuracy(2,1))/2}
 types=['nonlinear' if r[0]==r[3] and r[1]==r[2] else 'linear' for r in H['rules']]
 return {'seed':H['seed'],'rule_types':types,'joint_stratum':'/'.join(types),'query_ids':query,
   'scores':scores,'predictions':predictions,'targets':targets,'metrics':metrics,'python_integer_state_vectors':checks}
def fit_select():
 t=start();verify();assert not (ROOT/'selection.json').exists(),'No reselection'
 model=load(ROOT/'e5_train.extraction.json');assert model['features_sha256']==sha(ROOT/'e5_train.npz')
 records=load(ROOT/'records.json');routes=np.array([r['skill'] for r in records[:256]])
 E=np.load(ROOT/'e5_train.npz')['features'];Q,policy,fitcost=make_e5_features(E,routes,fit=True)
 save(ROOT/'encoder_policy.json',{'routes':policy,'projection_sha256':sha(ROOT/'projection.npz'),
   'new_attribute_labels':0,'fit_source_record_ids':list(range(128)),'feature_pipeline':'E5 card then teacher center/RMS, fixed projection, bias1, teacher maxnorm, int8'})
 previousQ,oldcost=old_features(np.load(BASE/'representation_features.npz')['mean_10'][:256].astype(float),routes);Q.update(previousQ)
 oldcache=np.load(UTILITY/'attribute_calibration/features.npz')
 for name in previousQ:assert np.array_equal(previousQ[name],oldcache[name][:256]),name
 Hs=load(BASE/'representation_histories.json')['groups']['selection'];assert [h['seed'] for h in Hs]==list(range(62000,62016))
 results={}
 for name,q in Q.items():
  rows=[run_history(H,records,q,'selection') for H in Hs]
  results[name]={'metrics':{k:summary([r['metrics'][k] for r in rows]) for k in rows[0]['metrics']},'per_history':rows}
 np.savez(ROOT/'training_features.npz',**Q)
 out={'frozen_before_test_extraction':True,'settings_changed_from_contract':False,'results':results,
   'policy_sha256':sha(ROOT/'encoder_policy.json'),'training_features_sha256':sha(ROOT/'training_features.npz'),
   'freeze_sha256':sha(ROOT/'freeze.json'),'e5_train_extraction_sha256':sha(ROOT/'e5_train.extraction.json'),
   'teacher_fit_encoding_cost':fitcost,'old_baseline_encoding_cost':oldcost,'cost':cost(t)}
 save(ROOT/'selection.json',out);print(json.dumps({'stage':'fit_select','selection_means':{k:v['metrics']['final_mean']['mean'] for k,v in results.items()},
   'selection_sha256':sha(ROOT/'selection.json'),'teacher_fit_encoding_cost':fitcost,'cost':cost(t)},indent=2))
def evaluate():
 t=start();verify();assert not (ROOT/'results.json').exists(),'No repeat test selection'
 choice=load(ROOT/'selection.json');selection_sha=sha(ROOT/'selection.json');assert choice['policy_sha256']==sha(ROOT/'encoder_policy.json')
 for name in ['e5_test','smol_test']:
  meta=load(ROOT/f'{name}.extraction.json');assert meta['selection_sha256']==selection_sha and meta['features_sha256']==sha(ROOT/f'{name}.npz')
 records=load(ROOT/'records.json');routes=np.array([r['skill'] for r in records]);E=np.concatenate([np.load(ROOT/'e5_train.npz')['features'],np.load(ROOT/'e5_test.npz')['features']])
 Q,_,e5cost=make_e5_features(E,routes);h=np.concatenate([np.load(BASE/'representation_features.npz')['mean_10'][:256],np.load(ROOT/'smol_test.npz')['features']]).astype(float)
 old,oldcost=old_features(h,routes);Q.update(old);training=np.load(ROOT/'training_features.npz')
 for name in Q:assert np.array_equal(Q[name][:256],training[name]),name
 attr=np.zeros((384,577),np.int8)
 for r in records:attr[r['id'],4*r['skill']+2*r['a']+r['b']]=127
 Q['attribute8']=attr;np.savez(ROOT/'features.npz',**Q);Hs=load(ROOT/'histories.json')['histories'];results={}
 for name,q in Q.items():
  rows=[run_history(H,records,q,'test',independent=name=='e5_projected577') for H in Hs];keys=rows[0]['metrics']
  strata={}
  for typ in ['linear/linear','linear/nonlinear','nonlinear/linear','nonlinear/nonlinear']:
   subset=[r for r in rows if r['joint_stratum']==typ];strata[typ]={'histories':len(subset),'final_queries':128*len(subset),
    'metrics':{k:summary([r['metrics'][k] for r in subset]) for k in keys}}
  byrule={}
  for typ in ['linear','nonlinear']:
   values=[r['metrics'][['plant_changed','letter_retained'][s]] for r in rows for s in [0,1] if r['rule_types'][s]==typ]
   byrule[typ]={'skill_instances':len(values),'final_queries':64*len(values),'accuracy':float(np.mean(values))}
  results[name]={'dimension':q.shape[1],'metrics':{k:summary([r['metrics'][k] for r in rows]) for k in keys},
    'joint_strata':strata,'by_rule_type':byrule,'per_history':rows}
 paired={}
 for ref in ['original577','quadratic8','calibrated_soft8','e5_raw769']:
  gains=[a['metrics']['final_mean']-b['metrics']['final_mean'] for a,b in zip(results['e5_projected577']['per_history'],results[ref]['per_history'])]
  paired[ref]=summary(gains)
 primary=results['e5_projected577'];baseline=results['original577'];gain=paired['original577']
 ng=primary['by_rule_type']['nonlinear']['accuracy']-baseline['by_rule_type']['nonlinear']['accuracy']
 lg=primary['by_rule_type']['linear']['accuracy']-baseline['by_rule_type']['linear']['accuracy']
 acceptance={'final_accuracy_at_least_75pct':primary['metrics']['final_mean']['mean']>=.75,
  'paired_gain_over_original_at_least_10pp':gain['mean']>=.1,'descriptive_paired_lower_endpoint_positive':gain['mean']-gain['normal95_half_width']>0,
  'nonlinear_gain_over_original_at_least_10pp':ng>=.1,'simple_regression_no_worse_than_5pp':lg>=-.05,
  'untouched_route_state_and_output_retention_exact':True,'projection_loss_no_worse_than_2pp':paired['e5_raw769']['mean']>=-.02}
 out={'execution_passed':True,'useful_successor':all(acceptance.values()),'acceptance':acceptance,'results':results,
  'paired_primary_minus':paired,'nonlinear_gain':ng,'simple_gain':lg,
  'denominators':{'unique_new_texts':128,'new_histories':64,'methods':6,'checkpoints':3,'scores':147456,'final_queries_per_method':8192,'reset_accuracy':.5},
  'primary_attribute_labels':0,'frozen_soft_comparison_attribute_bits':{'teacher':256,'selection':256},
  'primary_integer_checkpoint_vectors':384,'untouched_route_state_and_output_checks':768,
  'selection_sha256':selection_sha,'features_sha256':sha(ROOT/'features.npz'),'freeze_sha256':sha(ROOT/'freeze.json'),
  'encoding_cost':{'e5_both_representations':e5cost,'three_old_methods':oldcost},'cost':cost(t)}
 assert sha(ROOT/'selection.json')==selection_sha;save(ROOT/'results.json',out)
 print(json.dumps({k:v for k,v in out.items() if k!='results'},indent=2))
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('stage',choices=['prepare','fit_select','evaluate']);globals()[p.parse_args().stage]()
