"""Preregistered pooling/control comparison on new synthetic histories and text."""
import json,time
from pathlib import Path
import numpy as np
import text_transfer_controls as ttc
from text_transfer_data import features,history,labels
from run_controls import interval,sha
ROOT=Path(__file__).resolve().parent
REPRS=['last_30','mean_10','mean_20','mean_30']
MODEL_METHODS=['model_lms_shared','model_lms_routed','model_knn_shared','model_knn_routed',
               'model_window_shared','model_window_routed']
CONTROLS=['lexical_lms_routed','lexical_knn_routed','lexical_window_routed',
          'attribute_lms_8','attribute_window_shared','no_memory']


def description(name):
    if 'window' in name:return 'window',name.endswith('routed'),name.split('_')[0]
    return ttc.METHODS[name]

def configurations(name):
    if 'window' in name:return [dict(capacity=w) for w in [16,32,64,128]]
    return ttc.configs(name)

def train(name,cfg,H,rec,F,Q,skill):
    typ,routed,feature=description(name)
    if typ!='window':return ttc.train(name,cfg,H,rec,F,skill)
    cap=cfg['capacity']//(2 if routed else 1);P=Q[feature]
    C=np.zeros((2 if routed else 1,P.shape[1]),dtype=np.int32)
    buffers=[[] for _ in range(C.shape[0])];snapshots=[]
    for phase,ids in enumerate(H['phases']):
        ys=labels(H,rec,ids,flip0=phase==2)
        for i,y in zip(ids,ys):
            route=int(skill[i]) if routed else 0
            z=(int(y)*P[i]).astype(np.int8)
            old=buffers[route].pop(0).astype(np.int32) if len(buffers[route])==cap else 0
            C[route]=C[route]+z.astype(np.int32)-old;buffers[route].append(z)
        snapshots.append(C.copy())
    return snapshots

def predict(name,cfg,st,q,F,Q,skill,distance):
    typ,routed,feature=description(name)
    if typ!='window':return ttc.predict(name,cfg,st,q,F,skill,distance)
    P=Q[feature];result=[]
    for i in q:
        v=int(st[int(skill[i]) if routed else 0]@P[i].astype(np.int32))
        result.append(1 if v>=0 else -1)
    return np.array(result)

def accuracy(p,target):return float(np.mean(p==target))

def main():
    began=time.perf_counter();rec=json.loads((ROOT/'representation_records.json').read_text())
    z=np.load(ROOT/'representation_features.npz')
    fm={};qm={};dm={};vocab=None;scales={}
    for representation in REPRS:
        F,skill,vocab,S=features(rec,z[representation]);fm[representation]=F;scales[representation]=S
        qm[representation]={k:np.clip(np.rint(v*127),-127,127).astype(np.int8) for k,v in F.items()}
        dm[representation]={}
        for k in ['model','lexical']:
            norm=np.sum(F[k]*F[k],axis=1)
            dm[representation][k]=np.maximum(0,norm[:,None]+norm[None,:]-2*F[k]@F[k].T)
    groups={'development':[history(s,rec) for s in range(61000,61008)],
            'selection':[history(s,rec) for s in range(62000,62016)],
            'test':[history(s,rec) for s in range(63000,63032)]}
    qsel=np.array([r['id'] for r in rec if r['pool']=='selection']);q=np.array([r['id'] for r in rec if r['pool']=='test'])
    cases=[(repr,name) for repr in REPRS for name in MODEL_METHODS]+[('last_30',name) for name in CONTROLS]
    tuning={};chosen={};development={}
    for representation,name in cases:
        key=representation+'/'+name;F=fm[representation];Q=qm[representation];D=dm[representation]
        tuning[key]=[]
        for cfg in configurations(name):
            scores=[]
            for H in groups['selection']:
                st=train(name,cfg,H,rec,F,Q,skill)[-1]
                p=predict(name,cfg,st,qsel,F,Q,skill,D)
                scores.append(accuracy(p,labels(H,rec,qsel,flip0=True)))
            tuning[key].append({'configuration':cfg,'selection_final_accuracy':interval(scores)})
        best=sorted(tuning[key],key=lambda x:(-x['selection_final_accuracy']['mean'],json.dumps(x['configuration'],sort_keys=True)))[0]
        cfg=best['configuration'];chosen[key]=best
        ds=[]
        for H in groups['development']:
            st=train(name,cfg,H,rec,F,Q,skill)[-1]
            ds.append(accuracy(predict(name,cfg,st,qsel,F,Q,skill,D),labels(H,rec,qsel,flip0=True)))
        development[key]=interval(ds)
        print(json.dumps({'selected':key,'config':cfg,'accuracy':best['selection_final_accuracy']['mean']}),flush=True)
    chosen_repr={}
    for name in MODEL_METHODS:
        chosen_repr[name]=sorted(REPRS,key=lambda r:(-chosen[r+'/'+name]['selection_final_accuracy']['mean'],r))[0]
    selection={'choices':chosen,'chosen_representation_by_method':chosen_repr,'all_selection_candidates':tuning,
               'development':development,'script_sha256':sha(__file__),'protocol_sha256':sha(ROOT/'representation_PROTOCOL.md')}
    # Persist every choice before final labels/outcomes are evaluated.
    (ROOT/'representation_selection.json').write_text(json.dumps(selection,indent=2,sort_keys=True)+'\n')
    results={};decisions={};qskill=skill[q];s0=qskill==0;s1=~s0
    for representation,name in cases:
        key=representation+'/'+name;cfg=chosen[key]['configuration'];F=fm[representation];Q=qm[representation];D=dm[representation]
        rows=[];outputs=[]
        for H in groups['test']:
            states=train(name,cfg,H,rec,F,Q,skill)
            pp=[predict(name,cfg,st,q,F,Q,skill,D) for st in states]
            orig=labels(H,rec,q);final=labels(H,rec,q,flip0=True)
            rows.append({'seed':H['seed'],'final_mean':accuracy(pp[2],final),
              'skill0_initial':accuracy(pp[0][s0],orig[s0]),'skill0_after_skill1':accuracy(pp[1][s0],orig[s0]),
              'skill0_final_changed':accuracy(pp[2][s0],final[s0]),
              'skill1_after_learning':accuracy(pp[1][s1],orig[s1]),'skill1_final_retained':accuracy(pp[2][s1],orig[s1]),
              'skill0_interference_loss':accuracy(pp[0][s0],orig[s0])-accuracy(pp[1][s0],orig[s0]),
              'skill1_interference_loss':accuracy(pp[1][s1],orig[s1])-accuracy(pp[2][s1],orig[s1])})
            outputs.append({'seed':H['seed'],'phase_predictions':[p.tolist() for p in pp],
                            'initial_targets':orig.tolist(),'final_targets':final.tolist()})
        results[key]={'representation':representation,'method':name,'configuration':cfg,
          'selected_representation_for_method':chosen_repr.get(name,'last_30')==representation,
          'metrics':{k:interval([r[k] for r in rows]) for k in rows[0] if k!='seed'},'per_history':rows}
        decisions[key]=outputs
    paired={}
    for name in MODEL_METHODS:
        r=chosen_repr[name];baseline=results['last_30/'+name]['per_history'];candidate=results[r+'/'+name]['per_history']
        paired[name+' selected vs last_30']=interval([a['final_mean']-b['final_mean'] for a,b in zip(candidate,baseline)])
    for routed in ['shared','routed']:
        a='model_lms_'+routed;b='model_knn_'+routed
        xa=results[chosen_repr[a]+'/'+a]['per_history'];xb=results[chosen_repr[b]+'/'+b]['per_history']
        paired['selected '+a+' vs selected '+b]=interval([u['final_mean']-v['final_mean'] for u,v in zip(xa,xb)])
    result={'scope':'plaintext fixed pretrained representations and synthetic surface transfer; no security or recovery tests',
      'results':results,'chosen_representation_by_method':chosen_repr,'paired_history_differences':paired,
      'feature_dimensions':{r:{k:v.shape[1] for k,v in F.items()} for r,F in fm.items()},'feature_scales':scales,
      'quantization_clipping_counts':{r:{k:int(np.count_nonzero(np.rint(F[k]*127)!=qm[r][k])) for k in F} for r,F in fm.items()},
      'runtime_seconds':time.perf_counter()-began,'script_sha256':sha(__file__),'protocol_sha256':sha(ROOT/'representation_PROTOCOL.md'),
      'selection_sha256':sha(ROOT/'representation_selection.json')}
    (ROOT/'representation_results.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    (ROOT/'representation_histories.json').write_text(json.dumps({'groups':groups,'query_ids':q.tolist()},indent=2,sort_keys=True)+'\n')
    (ROOT/'representation_decisions.json').write_text(json.dumps(decisions,separators=(',',':'),sort_keys=True)+'\n')
    print(json.dumps({'complete':True,'runtime_seconds':result['runtime_seconds'],'selected_representations':chosen_repr,
      'selected_test_accuracy':{n:results[r+'/'+n]['metrics']['final_mean']['mean'] for n,r in chosen_repr.items()}}),flush=True)

if __name__=='__main__':main()
