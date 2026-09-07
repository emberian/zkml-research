"""Preregistered cached-feature successor. No model execution or encryption."""
from collections import deque
from pathlib import Path
import argparse,hashlib,json,math,resource,sys,time
sys.dont_write_bytecode=True
import numpy as np
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parents[2]/'adaptation_utility'
sys.path.insert(0,str(BASE))
from text_transfer_data import history,labels,features
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
save=lambda p,x:Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')

def timing():return time.perf_counter(),time.process_time()
def cost(start):
    return {'wall_seconds':time.perf_counter()-start[0],'cpu_seconds':time.process_time()-start[1],
      'process_high_water_rss_bytes_macos':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
def summary(values):
    v=np.array(values,dtype=np.float64);sd=float(v.std(ddof=1)) if len(v)>1 else 0
    return {'mean':float(v.mean()),'n_histories':len(v),'sd':sd,'normal95_half_width':1.96*sd/math.sqrt(len(v)),'min':float(v.min()),'max':float(v.max())}

def prepare():
    start=timing();records=load(BASE/'representation_records.json')
    # Freeze all history metadata before selection or final evaluation.
    final=[history(s,records) for s in range(64000,64064)]
    save(ROOT/'histories.json',{'seeds':list(range(64000,64064)),'histories':final,
      'text_surfaces_reused':True,'preregistration_sha256':sha(ROOT/'PREREGISTRATION.md')})
    hidden=np.load(BASE/'representation_features.npz')['mean_10'].astype(np.float64)
    original,skill,_,_=features(records,hidden)
    arrays={'original577':np.clip(np.rint(original['model']*127),-127,127).astype(np.int8)}
    attr=np.pad(original['attribute'],((0,0),(0,569)))
    arrays['attribute8']=np.clip(np.rint(attr*127),-127,127).astype(np.int8)
    parameter_arrays={};fits={};encodings={};dimensions={'original577':577,'attribute8':8}
    fitted={};fit_start=timing()
    for route in [0,1]:
        teacher=[r['id'] for r in records if r['pool']=='teach' and r['skill']==route]
        center=hidden[teacher].mean(0);centered=hidden[teacher]-center
        _,singular,vt=np.linalg.svd(centered,full_matrices=False)
        for j in range(len(vt)):
            if vt[j,np.abs(vt[j]).argmax()]<0:vt[j]*=-1
        parameter_arrays[f'r{route}_pca_center']=center
        parameter_arrays[f'r{route}_basis32']=vt[:32]
        fitted[route]=(teacher,center,vt[:32])
        fits[str(route)]={'teacher_count':len(teacher),'top32_singular_values':singular[:32].tolist()}
    fitting_cost=cost(fit_start)
    for k in [8,16,32]:
        for family in ['linear','quadratic']:
            begin=timing();name=f'{family}{k}';all_features=np.zeros((384,577),dtype=np.int8)
            d=k+1 if family=='linear' else k+k*(k+1)//2+1;dimensions[name]=d;clips={}
            for route in [0,1]:
                teacher,center,basis=fitted[route]
                ids=[r['id'] for r in records if r['skill']==route]
                teacher_local=[ids.index(i) for i in teacher]
                z=(hidden[ids]-center)@basis[:k].T
                std=np.maximum(z[teacher_local].std(axis=0,ddof=0),1e-8);z/=std
                transformed=z if family=='linear' else np.column_stack([z,*[z[:,i]*z[:,j] for i in range(k) for j in range(i,k)]])
                offset=transformed[teacher_local].mean(0);transformed-=offset
                biased=np.column_stack([transformed,np.ones(len(ids))]);scale=float(np.linalg.norm(biased[teacher_local],axis=1).max())
                normalized=biased/scale;rounds=np.rint(127*normalized)
                clips[str(route)]={pool:int(np.count_nonzero(np.abs(rounds[[j for j,i in enumerate(ids) if records[i]['pool']==pool]])>127)) for pool in ['teach','selection','test']}
                all_features[ids,:d]=np.clip(rounds,-127,127).astype(np.int8)
                parameter_arrays[f'{name}_r{route}_std']=std
                parameter_arrays[f'{name}_r{route}_offset']=offset
                parameter_arrays[f'{name}_r{route}_scale']=np.array(scale)
            arrays[name]=all_features;encodings[name]={'cost':cost(begin),'clipping_counts':clips,'dimension_before_padding':d}
    np.savez(ROOT/'features.npz',**arrays);np.savez(ROOT/'parameters.npz',**parameter_arrays)
    sources=[BASE/x for x in ['representation_records.json','representation_features.npz','representation_histories.json','representation_selection.json','representation_results.json','representation_model_manifest.json','text_transfer_data.py']]
    save(ROOT/'preparation.json',{'passed':True,'preregistration_sha256':sha(ROOT/'PREREGISTRATION.md'),
      'script_sha256':sha(__file__),'source_sha256':{str(p):sha(p) for p in sources},
      'histories_sha256':sha(ROOT/'histories.json'),'features_sha256':sha(ROOT/'features.npz'),
      'parameters_sha256':sha(ROOT/'parameters.npz'),'fitting':fits,'pca_fit_cost':fitting_cost,
      'encodings':encodings,'dimensions':dimensions,'total_cost':cost(start),'model_executed':False})
    print(json.dumps({'stage':'prepare','passed':True,'pca_fit':fitting_cost,'total':cost(start)},indent=2))

def run_history(H,records,Q,pool,independent=False):
    query=[r['id'] for r in records if r['pool']==pool];route=np.array([records[i]['skill'] for i in query])
    state=np.zeros((2,577),dtype=np.int64);queue=[deque(),deque()];states=[];predictions=[];scores=[];targets=[]
    checks={'checkpoint_vectors':0,'final_bigint_scores':0}
    for phase,ids in enumerate(H['phases'],1):
        ys=labels(H,records,ids,flip0=phase==3)
        for rid,y in zip(ids,ys):
            s=records[rid]['skill'];z=int(y)*Q[rid].astype(np.int64)
            queue[s].append(z);state[s]+=z
            if len(queue[s])>32:state[s]-=queue[s].popleft()
        if independent:
            for s in [0,1]:
                reference=[sum(int(z[j]) for z in queue[s]) for j in range(577)]
                assert state[s].tolist()==reference;checks['checkpoint_vectors']+=1
        scalar=np.einsum('ij,ij->i',state[route],Q[query].astype(np.int64),dtype=np.int64)
        if independent and phase==3:
            for i,rid in enumerate(query):
                assert int(scalar[i])==sum(int(a)*int(b) for a,b in zip(state[records[rid]['skill']],Q[rid]))
                checks['final_bigint_scores']+=1
        target=labels(H,records,query,flip0=phase==3);pred=np.where(scalar>=0,1,-1)
        states.append(state.copy());scores.append(scalar.tolist());predictions.append(pred.tolist());targets.append(target.tolist())
    assert np.array_equal(states[0][0],states[1][0]) and np.array_equal(states[1][1],states[2][1])
    accuracy=lambda p,s:float(np.mean(np.array(predictions[p])[route==s]==np.array(targets[p])[route==s]))
    ruletypes=['nonlinear' if r[0]==r[3] and r[1]==r[2] else 'linear' for r in H['rules']]
    metrics={'plant_initial':accuracy(0,0),'plant_after_letters':accuracy(1,0),'letter_after_learning':accuracy(1,1),
      'plant_changed':accuracy(2,0),'letter_retained':accuracy(2,1),'final_mean':(accuracy(2,0)+accuracy(2,1))/2}
    assert all(np.mean(labels(H,records,query,flip0=p==3)==1)==.5 for p in [1,2,3])
    return {'seed':H['seed'],'rule_types':ruletypes,'joint_stratum':'/'.join(ruletypes),'metrics':metrics,
      'query_ids':query,'scores':scores,'predictions':predictions,'targets':targets,'checks':checks}

def select():
    start=timing();prep=load(ROOT/'preparation.json');assert prep['script_sha256']==sha(__file__)
    records=load(BASE/'representation_records.json');Q=np.load(ROOT/'features.npz')
    histories=load(BASE/'representation_histories.json')['groups']['selection']
    assert [h['seed'] for h in histories]==list(range(62000,62016))
    results={}
    for name in ['original577','linear8','linear16','linear32','quadratic8','quadratic16','quadratic32','attribute8']:
        rows=[run_history(h,records,Q[name],'selection') for h in histories]
        results[name]={'final_mean':summary([r['metrics']['final_mean'] for r in rows]),
          'per_history_metrics':[{'seed':r['seed'],**r['metrics']} for r in rows]}
    chosen={family:max([8,16,32],key=lambda k:(results[f'{family}{k}']['final_mean']['mean'],-k)) for family in ['linear','quadratic']}
    result={'frozen_before_test':True,'chosen_k':chosen,'selection':results,'cost':cost(start),
      'preregistration_sha256':sha(ROOT/'PREREGISTRATION.md'),'script_sha256':sha(__file__),
      'preparation_sha256':sha(ROOT/'preparation.json'),'histories_sha256':sha(ROOT/'histories.json')}
    save(ROOT/'selection.json',result)
    print(json.dumps({'stage':'selection','chosen_k':chosen,'selection_means':{k:v['final_mean']['mean'] for k,v in results.items()},'cost':cost(start)},indent=2))

def evaluate():
    start=timing();choice=load(ROOT/'selection.json');selection_hash=sha(ROOT/'selection.json')
    assert choice['script_sha256']==sha(__file__) and choice['histories_sha256']==sha(ROOT/'histories.json')
    records=load(BASE/'representation_records.json');Q=np.load(ROOT/'features.npz');Hs=load(ROOT/'histories.json')['histories']
    quad=f"quadratic{choice['chosen_k']['quadratic']}";linear=f"linear{choice['chosen_k']['linear']}"
    results={}
    for name in ['original577',linear,quad,'attribute8']:
        rows=[run_history(h,records,Q[name],'test',independent=name==quad) for h in Hs]
        keys=rows[0]['metrics'];aggregate={k:summary([r['metrics'][k] for r in rows]) for k in keys}
        strata={}
        for label in ['linear/linear','linear/nonlinear','nonlinear/linear','nonlinear/nonlinear']:
            subset=[r for r in rows if r['joint_stratum']==label]
            strata[label]={'count':len(subset),'metrics':{k:summary([r['metrics'][k] for r in subset]) for k in keys}}
        nonlin=[r['metrics'][['plant_changed','letter_retained'][s]] for r in rows for s in [0,1] if r['rule_types'][s]=='nonlinear']
        results[name]={'metrics':aggregate,'joint_strata':strata,'nonlinear_final_skill_accuracy':float(np.mean(nonlin)),
          'nonlinear_skill_instances':len(nonlin),'per_history':rows}
    baseline=results['original577']['per_history'];qrows=results[quad]['per_history']
    gains=[a['metrics']['final_mean']-b['metrics']['final_mean'] for a,b in zip(qrows,baseline)]
    paired=summary(gains)
    joint_gains={label:summary([g for g,r in zip(gains,qrows) if r['joint_stratum']==label]) for label in results[quad]['joint_strata']}
    nonlinear_gain=results[quad]['nonlinear_final_skill_accuracy']-results['original577']['nonlinear_final_skill_accuracy']
    acceptance={'final_mean_at_least_60pct':results[quad]['metrics']['final_mean']['mean']>=.60,
      'paired_gain_at_least_5points':paired['mean']>=.05,'paired_descriptive_lower_bound_positive':paired['mean']-paired['normal95_half_width']>0,
      'nonlinear_gain_at_least_10points':nonlinear_gain>=.10}
    assert sha(ROOT/'selection.json')==selection_hash
    result={'passed_execution':True,'useful_successor':all(acceptance.values()),'acceptance':acceptance,
      'selected_quadratic':quad,'selected_linear_control':linear,'paired_quadratic_minus_original':paired,
      'joint_stratum_paired_gains':joint_gains,'nonlinear_gain':nonlinear_gain,'results':results,
      'reset_accuracy':.5,'route_state_retention_equalities':len(Hs)*2*len(results),
      'final_selected_bigint_scores':sum(r['checks']['final_bigint_scores'] for r in qrows),
      'selected_checkpoint_vectors':sum(r['checks']['checkpoint_vectors'] for r in qrows),
      'selection_sha256':selection_hash,'histories_sha256':sha(ROOT/'histories.json'),
      'preregistration_sha256':sha(ROOT/'PREREGISTRATION.md'),'script_sha256':sha(__file__),
      'cost':cost(start),'model_executed':False,'text_surfaces_reused':True}
    save(ROOT/'results.json',result)
    print(json.dumps({k:v for k,v in result.items() if k!='results'},indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('stage',choices=['prepare','select','evaluate'])
    globals()[p.parse_args().stage]()
