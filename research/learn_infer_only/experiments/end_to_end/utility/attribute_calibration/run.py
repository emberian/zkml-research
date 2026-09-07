"""Contract-frozen supervised feature calibration, selection and integer utility."""
import argparse,hashlib,importlib.util,json,math,resource,sys,time
from pathlib import Path
sys.dont_write_bytecode=True
import numpy as np
ROOT=Path(__file__).resolve().parent
UTILITY=ROOT.parent
BASE=UTILITY.parents[1]/'adaptation_utility'
PREVIOUS=UTILITY/'nonlinear_successor'
sys.path.insert(0,str(BASE))
import text_transfer_data as olddata
import representation_data as repdata
from data import make_new_records
spec=importlib.util.spec_from_file_location('previous_frozen',PREVIOUS/'run.py')
previous=importlib.util.module_from_spec(spec);spec.loader.exec_module(previous)
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
save=lambda p,x:Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
LAMBDAS=[.0001,.001,.01,.1,1.]
def start(): return time.perf_counter(),time.process_time()
def cost(t):return {'wall_seconds':time.perf_counter()-t[0],'cpu_seconds':time.process_time()-t[1],
 'process_high_water_rss_bytes_macos':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
def pins(paths):return {str(p):sha(p) for p in paths}
def verify_pins(table):
    for p,digest in table.items():assert sha(p)==digest,(p,'changed')
def normalized(h,routes):
    policy=load(UTILITY/'encoder_policy.json')['policies_by_public_route'];out=np.empty_like(h,dtype=np.float64)
    for s in [0,1]:
        mask=routes==s;c=policy[str(s)];out[mask]=(h[mask]-np.array(c['center']))/c['scale']
    return out
def quantize(x):return np.clip(np.rint(127*x),-127,127).astype(np.int8)
def attr_report(probs,gold,routes):
    pred=probs>=.5;per={}
    for s in [0,1]:
        mask=routes==s
        for j in [0,1]:per[f'route{s}_attribute{j}']=float(np.mean(pred[mask,j]==gold[mask,j]))
    return {'head_accuracy':per,'mean_accuracy':float(np.mean(list(per.values()))),
      'mse_clipped':float(np.mean((probs-gold)**2)),
      'joint_attribute_accuracy':float(np.mean(np.all(pred==gold,axis=1)))}
def prepare():
    assert not (ROOT/'selection.json').exists(),'Fresh preparation only; preserve prior outputs'
    records=make_new_records(load(BASE/'representation_records.json'),[olddata,repdata])
    save(ROOT/'records.json',records)
    save(ROOT/'histories.json',{'seeds':list(range(65000,65064)),
      'histories':[olddata.history(s,records) for s in range(65000,65064)]})
    save(ROOT/'attribute_supervision.json',{'teacher_bits':256,'selection_bits':256,
      'rows':[{'record_id':r['id'],'pool':r['pool'],'route':r['skill'],'a':r['a'],'b':r['b']} for r in records[:256]]})
    source=[ROOT/n for n in ['CONTRACT.md','data.py','run.py','extract.py','records.json','histories.json','attribute_supervision.json']]
    source +=[BASE/n for n in ['representation_features.npz','representation_records.json','representation_model_manifest.json','model_manifest.json','requirements-lock.txt','text_transfer_data.py','representation_data.py']]
    source +=[UTILITY/n for n in ['encoder_policy.json','encoder_feasibility.json']]
    source +=[PREVIOUS/n for n in ['run.py','preparation.json','selection.json','parameters.npz']]
    save(ROOT/'freeze.json',{'source_sha256':pins(source),'new_test_surfaces':True,
       'full_names_templates_cues_disjoint_from_two_prior_generators':True,'test_texts':128,
       'ordinary_words_and_all_logical_combinations_overlap':True,'new_history_count':64,
       'selection_and_test_not_yet_run':True})
    print(json.dumps({'stage':'prepare','freeze_sha256':sha(ROOT/'freeze.json'),'test_texts':128}))
def select():
    t=start();verify_pins(load(ROOT/'freeze.json')['source_sha256'])
    assert not (ROOT/'selection.json').exists(),'Refuse reselection'
    records=load(ROOT/'records.json')[:256];h=np.load(BASE/'representation_features.npz')['mean_10'][:256].astype(np.float64)
    routes=np.array([r['skill'] for r in records]);gold=np.array([[r['a'],r['b']] for r in records]);x=normalized(h,routes)
    fits={};reports={}
    for lam in LAMBDAS:
        prob=np.zeros((256,2));fit={}
        for s in [0,1]:
            tr=np.array([r['id'] for r in records if r['pool']=='teach' and r['skill']==s]);ids=np.where(routes==s)[0]
            xm=x[tr].mean(0);ym=gold[tr].mean(0);X=x[tr]-xm
            coef=X.T@np.linalg.solve(X@X.T+lam*np.eye(len(tr)),gold[tr]-ym)
            intercept=ym-xm@coef;prob[ids]=np.clip(x[ids]@coef+intercept,0,1)
            fit[f'r{s}_coef']=coef;fit[f'r{s}_intercept']=intercept
        fits[lam]=fit;reports[str(lam)]={'teacher':attr_report(prob[:128],gold[:128],routes[:128]),
          'selection':attr_report(prob[128:],gold[128:],routes[128:])}
    chosen=max(LAMBDAS,key=lambda l:(reports[str(l)]['selection']['mean_accuracy'],-reports[str(l)]['selection']['mse_clipped'],l))
    np.savez(ROOT/'parameters.npz',**fits[chosen])
    # Public source policy retained as JSON; NPZ is a regeneratable runtime artifact.
    save(ROOT/'calibration_policy.json',{'lambda':chosen,'normalized_input_policy_sha256':sha(UTILITY/'encoder_policy.json'),
      'fit_parameters':{k:v.tolist() for k,v in fits[chosen].items()},'teacher_attribute_bits':256,
      'selection_attribute_bits':256,'output':'soft conjunctions in route4 slots, padded577, nearest-even int8 range127'})
    out={'stage':'selection','frozen_before_test_extraction':True,'chosen_lambda':chosen,'grid':reports,
       'parameters_sha256':sha(ROOT/'parameters.npz'),'policy_sha256':sha(ROOT/'calibration_policy.json'),
       'freeze_sha256':sha(ROOT/'freeze.json'),'cost':cost(t)}
    save(ROOT/'selection.json',out);print(json.dumps(out,indent=2))
def feature_arrays(h,routes):
    """Gold attributes intentionally absent from this API."""
    t=start();x=normalized(h,routes);policy=load(UTILITY/'encoder_policy.json')['policies_by_public_route']
    original=np.zeros((len(h),577),dtype=np.int8)
    for s in [0,1]:
        ids=np.where(routes==s)[0];original[ids]=quantize(np.column_stack([x[ids],np.full(len(ids),1/policy[str(s)]['scale'])]))
    original_cost=cost(t);t=start()
    params=load(ROOT/'calibration_policy.json')['fit_parameters'];probs=np.zeros((len(h),2))
    for s in [0,1]:
        ids=np.where(routes==s)[0];probs[ids]=np.clip(x[ids]@np.array(params[f'r{s}_coef'])+np.array(params[f'r{s}_intercept']),0,1)
    out={'original577':original}
    for name,p in [('calibrated_soft8',probs),('calibrated_hard8',(probs>=.5).astype(float))]:
        a,b=p.T;four=np.column_stack([(1-a)*(1-b),(1-a)*b,a*(1-b),a*b]);Q=np.zeros_like(original)
        for s in [0,1]:
            ids=np.where(routes==s)[0];Q[ids,4*s:4*s+4]=quantize(four[ids])
        out[name]=Q
    calibration_cost=cost(t);t=start();prep=load(PREVIOUS/'preparation.json')
    assert sha(PREVIOUS/'parameters.npz')==prep['parameters_sha256']
    pp=np.load(PREVIOUS/'parameters.npz');Q=np.zeros_like(original)
    assert load(PREVIOUS/'selection.json')['chosen_k']['quadratic']==8
    for s in [0,1]:
        ids=np.where(routes==s)[0];z=(h[ids]-pp[f'r{s}_pca_center'])@pp[f'r{s}_basis32'][:8].T
        z/=pp[f'quadratic8_r{s}_std'];v=np.column_stack([z,*[z[:,i]*z[:,j] for i in range(8) for j in range(i,8)]])
        v-=pp[f'quadratic8_r{s}_offset'];v=np.column_stack([v,np.ones(len(ids))])/pp[f'quadratic8_r{s}_scale']
        Q[ids,:45]=quantize(v)
    out['quadratic8']=Q
    return out,probs,{'original577':original_cost,'calibration_soft_and_hard':calibration_cost,'quadratic8':cost(t)}
def evaluate():
    t=start();freeze=load(ROOT/'freeze.json');verify_pins(freeze['source_sha256'])
    choice=load(ROOT/'selection.json');selection_sha=sha(ROOT/'selection.json');assert not (ROOT/'results.json').exists(),'No test reselection'
    assert choice['policy_sha256']==sha(ROOT/'calibration_policy.json')
    model=load(ROOT/'extraction.json');assert model['selection_sha256']==selection_sha
    assert model['features_sha256']==sha(ROOT/'new_features.npz')
    records=load(ROOT/'records.json');routes=np.array([r['skill'] for r in records]);gold=np.array([[r['a'],r['b']] for r in records])
    h=np.concatenate([np.load(BASE/'representation_features.npz')['mean_10'][:256],np.load(ROOT/'new_features.npz')['mean_10']]).astype(np.float64)
    Q,probs,encoding_cost=feature_arrays(h,routes)
    previous_features=np.load(PREVIOUS/'features.npz')
    for name in ['original577','quadratic8']:assert np.array_equal(Q[name][:256],previous_features[name][:256]),name
    attr=np.zeros((384,577));attr[np.arange(384),4*routes+2*gold[:,0]+gold[:,1]]=1;Q['attribute8']=quantize(attr)
    np.savez(ROOT/'features.npz',**Q);save(ROOT/'attribute_predictions.json',[{'record_id':r['id'],'route':r['skill'],
      'gold_attributes':[r['a'],r['b']],'predicted_probabilities':probs[r['id']].tolist()} for r in records[256:]])
    Hs=load(ROOT/'histories.json')['histories'];results={}
    for name,q in Q.items():
        rows=[previous.run_history(H,records,q,'test',independent=name=='calibrated_soft8') for H in Hs]
        keys=rows[0]['metrics'];aggregate={k:previous.summary([r['metrics'][k] for r in rows]) for k in keys}
        strata={}
        for label in ['linear/linear','linear/nonlinear','nonlinear/linear','nonlinear/nonlinear']:
            subset=[r for r in rows if r['joint_stratum']==label]
            strata[label]={'n_histories':len(subset),'final_query_predictions':len(subset)*128,
              'metrics':{k:previous.summary([r['metrics'][k] for r in subset]) for k in keys}}
        by_rule={}
        for typ in ['linear','nonlinear']:
            v=[r['metrics'][['plant_changed','letter_retained'][s]] for r in rows for s in [0,1] if r['rule_types'][s]==typ]
            by_rule[typ]={'skill_instances':len(v),'final_query_predictions':64*len(v),'accuracy':float(np.mean(v))}
        for r in rows:
            assert r['predictions'][0][:64]==r['predictions'][1][:64]
            assert r['predictions'][1][64:]==r['predictions'][2][64:]
        results[name]={'metrics':aggregate,'joint_strata':strata,'by_rule_type':by_rule,'per_history':rows}
    primary=results['calibrated_soft8'];comparisons={}
    for method in ['calibrated_soft8','calibrated_hard8']:
        comparisons[method]={}
        for ref in ['original577','quadratic8']:
            gains=[a['metrics']['final_mean']-b['metrics']['final_mean'] for a,b in zip(results[method]['per_history'],results[ref]['per_history'])]
            comparisons[method][ref]=previous.summary(gains)
    paired=comparisons['calibrated_soft8']['original577'];base=results['original577']
    nonlinear_gain=primary['by_rule_type']['nonlinear']['accuracy']-base['by_rule_type']['nonlinear']['accuracy']
    simple_gain=primary['by_rule_type']['linear']['accuracy']-base['by_rule_type']['linear']['accuracy']
    acceptance={'final_at_least_75pct':primary['metrics']['final_mean']['mean']>=.75,
      'paired_gain_at_least_10pp':paired['mean']>=.1,'descriptive_lower_endpoint_positive':paired['mean']-paired['normal95_half_width']>0,
      'nonlinear_gain_at_least_10pp':nonlinear_gain>=.1,'simple_regression_at_most_5pp':simple_gain>=-.05,
      'untouched_route_state_and_output_retention_exact':True}
    result={'execution_passed':True,'useful_successor':all(acceptance.values()),'acceptance':acceptance,
      'teacher_attribute_bits':256,'selection_attribute_bits':256,'test_attribute_report':attr_report(probs[256:],gold[256:],routes[256:]),
      'paired_final':comparisons,'nonlinear_gain':nonlinear_gain,'simple_gain':simple_gain,'results':results,
      'denominators':{'histories':64,'unique_new_texts':128,'checkpoints':3,'methods':5,'predictions':122880,
        'final_predictions_per_method':8192,'zero_reset_accuracy':.5},
      'exact_checks':{'baseline_and_quadratic_teacher_selection_coordinates':2*256*577,
        'primary_python_integer_checkpoint_vectors':384,'primary_python_integer_final_scores':8192,
        'untouched_route_state_and_output_equalities':64*2*5},
      'selection_sha256':selection_sha,'freeze_sha256':sha(ROOT/'freeze.json'),'extraction_sha256':sha(ROOT/'extraction.json'),
      'features_sha256':sha(ROOT/'features.npz'),'encoding_cost':encoding_cost,'evaluation_cost':cost(t)}
    assert sha(ROOT/'selection.json')==selection_sha
    save(ROOT/'results.json',result)
    print(json.dumps({k:v for k,v in result.items() if k!='results'},indent=2))
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('stage',choices=['prepare','select','evaluate']);globals()[p.parse_args().stage]()
