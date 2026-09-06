"""Exact additive memory window; symbolic integers, no encryption in this script."""
import json,time
from pathlib import Path
import numpy as np
from run_controls import sha,interval
import text_transfer_controls as ttc
from text_transfer_data import features,labels
ROOT=Path(__file__).resolve().parent
METHODS={'model_window_shared':('model',False),'model_window_routed':('model',True),
         'lexical_window_routed':('lexical',True),'attribute_window_shared':('attribute',False),
         'attribute_window_routed':('attribute',True)}
CHECKS={'queue_recomputations':0,'score_reference_agreements':0,'max_observed_score':0}

def train(name,W,H,records,quant,skill,reverse=False):
    feature,routed=METHODS[name];P=quant[feature];routes=2 if routed else 1
    cap=W//routes;queue=[[] for _ in range(routes)];C=np.zeros((routes,P.shape[1]),dtype=np.int32)
    states=[]
    for phase,ids in enumerate(H['phases']):
        y=labels(H,records,ids,flip0=(phase==2)^reverse)
        for j,v in zip(ids,y):
            k=int(skill[j]) if routed else 0;z=(int(v)*P[j]).astype(np.int8)
            old=queue[k].pop(0).astype(np.int32) if len(queue[k])==cap else 0
            C[k]=C[k]+z.astype(np.int32)-old;queue[k].append(z.copy())
            expected=np.array([sum(int(z[i]) for z in queue[k]) for i in range(P.shape[1])],dtype=np.int32)
            assert np.array_equal(C[k],expected)
            assert np.max(np.abs(C[k]))<=127*cap
            CHECKS['queue_recomputations']+=1
        states.append(C.copy())
    return states

def predict(name,state,ids,quant,skill):
    feature,routed=METHODS[name];P=quant[feature];pred=[]
    for i in ids:
        C=state[int(skill[i]) if routed else 0]
        score=int(C@P[i].astype(np.int32))
        reference=sum(int(c)*int(p) for c,p in zip(C,P[i]));assert score==reference
        assert abs(score)<=577*128*127**2<2**31
        CHECKS['score_reference_agreements']+=1;CHECKS['max_observed_score']=max(CHECKS['max_observed_score'],abs(score))
        pred.append(1 if score>=0 else -1)
    return np.array(pred)

def main():
    start=time.perf_counter();records=json.loads((ROOT/'text_transfer_records.json').read_text())
    maps,skill,vocab,scales=features(records,np.load(ROOT/'text_transfer_features.npz')['hidden'])
    quant={k:np.clip(np.rint(v*127),-127,127).astype(np.int8) for k,v in maps.items()}
    historyfile=json.loads((ROOT/'text_transfer_histories.json').read_text());groups=historyfile['groups']
    qsel=np.array([r['id'] for r in records if r['pool']=='selection']);q=np.array(historyfile['query_ids'])
    s0=skill[q]==0;s1=~s0;selected={};tuning={}
    for name in METHODS:
        tuning[name]=[]
        for W in [16,32,64,128]:
            scores=[]
            for H in groups['selection']:
                C=train(name,W,H,records,quant,skill)[-1]
                scores.append(ttc.accuracy(predict(name,C,qsel,quant,skill),labels(H,records,qsel,flip0=True)))
            tuning[name].append({'W':W,'accuracy':interval(scores)})
        best=sorted(tuning[name],key=lambda row:(-row['accuracy']['mean'],row['W']))[0]
        selected[name]=best['W']
        print(json.dumps({'selected':name,'W':best['W'],'selection':best['accuracy']['mean']}),flush=True)
    (ROOT/'text_window_selection.json').write_text(json.dumps({'selected':selected,'tuning':tuning},indent=2,sort_keys=True)+'\n')
    results={};decisions={}
    for name in METHODS:
        W=selected[name];feature,routed=METHODS[name];r=quant[feature].shape[1];routes=2 if routed else 1
        states=[train(name,W,H,records,quant,skill) for H in groups['test']];rows=[];out=[]
        for i,H in enumerate(groups['test']):
            p=[predict(name,C,q,quant,skill) for C in states[i]]
            orig=labels(H,records,q);target=labels(H,records,q,flip0=True)
            reverse=predict(name,train(name,W,H,records,quant,skill,reverse=True)[-1],q,quant,skill)
            swap=predict(name,states[(i+1)%len(states)][-1],q,quant,skill)
            rows.append({'seed':H['seed'],'final_mean':ttc.accuracy(p[-1],target),
              'skill0_initial':ttc.accuracy(p[0][s0],orig[s0]),'skill0_final_changed':ttc.accuracy(p[2][s0],target[s0]),
              'skill1_after_learning':ttc.accuracy(p[1][s1],orig[s1]),'skill1_final_retained':ttc.accuracy(p[2][s1],orig[s1]),
              'skill0_interference_loss':ttc.accuracy(p[0][s0],orig[s0])-ttc.accuracy(p[1][s0],orig[s0]),
              'skill1_interference_loss':ttc.accuracy(p[1][s1],orig[s1])-ttc.accuracy(p[2][s1],orig[s1]),
              'order_disagreement_skill0':float(np.mean(p[2][s0]!=reverse[s0])),
              'order_disagreement_skill1':float(np.mean(p[2][s1]!=reverse[s1])),
              'reset':ttc.accuracy(np.ones(len(q)),target),'swap':ttc.accuracy(swap,target)})
            out.append({'seed':H['seed'],'phase_predictions':[a.tolist() for a in p],
              'final_targets':target.tolist(),'reverse':reverse.tolist(),'swap':swap.tolist()})
        results[name]={'W':W,'dimension':r,'routes':routes,'queue_int8_bytes':W*r,'accumulator_int32_bytes':4*routes*r,
          'max_abs_accumulator_bound':(W//routes)*127,'max_abs_score_bound':r*(W//routes)*127**2,
          'learn_integer_add_sub_count':2*r,'infer_integer_multiply_count':r,
          'feature_clipping_count':int(np.count_nonzero(np.rint(maps[feature]*127)!=quant[feature])),
          'metrics':{k:interval([row[k] for row in rows]) for k in rows[0] if k!='seed'},'per_history':rows}
        decisions[name]=out
    # In-sample diagnostic with original selected hyperparameters; no reselection.
    original=json.loads((ROOT/'text_transfer_selection.json').read_text())['selected']
    teacher=np.array([r['id'] for r in records if r['pool']=='teach']);distance={}
    for feature in ['model','lexical']:
        F=maps[feature];norm=np.sum(F*F,axis=1);distance[feature]=np.maximum(0,norm[:,None]+norm[None,:]-2*F@F.T)
    diagnostic={}
    for name,cfg in original.items():
        scores=[]
        for H in groups['test']:
            st=ttc.train(name,cfg,H,records,maps,skill)[-1]
            scores.append(ttc.accuracy(ttc.predict(name,cfg,st,teacher,maps,skill,distance),labels(H,records,teacher,flip0=True)))
        diagnostic[name]=interval(scores)
    result={'scope':'plaintext exact additive window; no encryption, no restricted release',
      'results':results,'exact_checks':CHECKS,'universal_int32_score_bound':577*128*127**2,
      'selected_original_methods_in_sample_diagnostic':diagnostic,'runtime_seconds':time.perf_counter()-start,
      'script_sha256':sha(__file__),'protocol_sha256':sha(ROOT/'TEXT_WINDOW_PROTOCOL.md'),
      'selection_sha256':sha(ROOT/'text_window_selection.json')}
    (ROOT/'text_window_results.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    (ROOT/'text_window_decisions.json').write_text(json.dumps(decisions,separators=(',',':'),sort_keys=True)+'\n')
    print(json.dumps({'complete':True,'runtime_seconds':result['runtime_seconds'],'final_mean':{k:v['metrics']['final_mean']['mean'] for k,v in results.items()},'checks':CHECKS}),flush=True)

if __name__=='__main__':main()
