"""Text transfer, ordered updates, and interference; no protected computation."""
import itertools,json,time
from pathlib import Path
import numpy as np
from run_controls import sha,sign,interval
from text_transfer_data import features,history,labels
ROOT=Path(__file__).resolve().parent
ETAS=[.03,.1,.3,1.];RHOS=[1.,.995,.98,.95]
METHODS={
 'no_memory':('none',False,'model'),
 'model_knn_shared':('knn',False,'model'),'model_knn_routed':('knn',True,'model'),
 'model_lms_shared':('lms',False,'model'),'model_lms_routed':('lms',True,'model'),
 'lexical_knn_routed':('knn',True,'lexical'),'lexical_lms_routed':('lms',True,'lexical'),
 'attribute_lms_8':('lms',False,'attribute')}

def configs(name):
    typ,routed,feature=METHODS[name]
    if typ=='lms':return [dict(eta=e,rho=r) for e,r in itertools.product(ETAS,RHOS)]
    if typ=='knn':return [dict(k=k,capacity=m) for k,m in itertools.product([1,3,7],[32,64,128])]
    return [{}]

def train(name,cfg,H,records,maps,skill,reverse=False):
    typ,routed,feature=METHODS[name];F=maps[feature]
    if typ=='none':return [None,None,None]
    if typ=='lms':state=np.zeros((2 if routed else 1,F.shape[1]))
    else:state=[[] for _ in range(2 if routed else 1)]
    snapshots=[]
    for phase,ids in enumerate(H['phases']):
        y=labels(H,records,ids,flip0=(phase==2)^reverse)
        for j,v in zip(ids,y):
            route=int(skill[j]) if routed else 0
            if typ=='lms':
                x=F[j];m=state[route]
                state[route]=cfg['rho']*m+cfg['eta']*(v-m@x)*x
            else:
                state[route].append((int(j),int(v)))
                cap=cfg['capacity']//2 if routed else cfg['capacity']
                state[route]=state[route][-cap:]
        snapshots.append(state.copy() if typ=='lms' else [list(buf) for buf in state])
    return snapshots

def predict(name,cfg,state,query,maps,skill,distance):
    typ,routed,feature=METHODS[name]
    if typ=='none':return np.ones(len(query),dtype=int)
    pred=[]
    for i in query:
        route=int(skill[i]) if routed else 0
        if typ=='lms':v=state[route]@maps[feature][i]
        else:
            buf=state[route]
            if not buf:pred.append(1);continue
            ids=np.array([j for j,y in buf]);ys=np.array([y for j,y in buf])
            nearest=np.argsort(distance[feature][i,ids],kind='stable')[:cfg['k']]
            v=ys[nearest].sum()
        pred.append(1 if v>=0 else -1)
    return np.array(pred)

def accuracy(p,y):return float(np.mean(p==y))

def main():
    start=time.perf_counter();records=json.loads((ROOT/'text_transfer_records.json').read_text())
    hidden=np.load(ROOT/'text_transfer_features.npz')['hidden']
    maps,skill,vocab,scales=features(records,hidden)
    distance={}
    for name in ['model','lexical']:
        F=maps[name];norm=np.sum(F*F,axis=1);distance[name]=np.maximum(0,norm[:,None]+norm[None,:]-2*F@F.T)
    queries={pool:np.array([r['id'] for r in records if r['pool']==pool]) for pool in ['selection','test']}
    groups={'development':[history(s,records) for s in range(51000,51008)],
            'selection':[history(s,records) for s in range(52000,52016)],
            'test':[history(s,records) for s in range(53000,53032)]}
    tuning={};selected={};development={}
    for name in METHODS:
        tuning[name]=[]
        for cfg in configs(name):
            scores=[]
            for H in groups['selection']:
                st=train(name,cfg,H,records,maps,skill)[-1]
                q=queries['selection'];p=predict(name,cfg,st,q,maps,skill,distance)
                scores.append(accuracy(p,labels(H,records,q,flip0=True)))
            tuning[name].append({'config':cfg,'final_accuracy':interval(scores)})
        best=sorted(tuning[name],key=lambda x:(-x['final_accuracy']['mean'],json.dumps(x['config'],sort_keys=True)))[0]
        cfg=best['config'];selected[name]=cfg;scores=[]
        for H in groups['development']:
            q=queries['selection'];st=train(name,cfg,H,records,maps,skill)[-1]
            scores.append(accuracy(predict(name,cfg,st,q,maps,skill,distance),labels(H,records,q,flip0=True)))
        development[name]=interval(scores)
        print(json.dumps({'selected':name,'config':cfg,'selection_accuracy':best['final_accuracy']['mean']}),flush=True)
    (ROOT/'text_transfer_selection.json').write_text(json.dumps({'selected':selected,'tuning':tuning,'development':development},indent=2,sort_keys=True)+'\n')
    results={};decisions={};allstates={};q=queries['test'];q0=q[skill[q]==0];q1=q[skill[q]==1]
    for name in METHODS:
        cfg=selected[name];learned=[train(name,cfg,H,records,maps,skill) for H in groups['test']]
        rows=[];outs=[]
        for i,H in enumerate(groups['test']):
            st=learned[i]
            phases=[predict(name,cfg,m,q,maps,skill,distance) for m in st]
            reverse=train(name,cfg,H,records,maps,skill,reverse=True)[-1]
            rev=predict(name,cfg,reverse,q,maps,skill,distance)
            swap=predict(name,cfg,learned[(i+1)%len(learned)][-1],q,maps,skill,distance)
            orig=labels(H,records,q);target=labels(H,records,q,flip0=True)
            s0=skill[q]==0;s1=~s0
            metrics={'seed':H['seed'],'final_mean':accuracy(phases[-1],target),
              'skill0_after_initial_learning':accuracy(phases[0][s0],orig[s0]),
              'skill0_after_skill1_learning':accuracy(phases[1][s0],orig[s0]),
              'skill0_final_changed':accuracy(phases[2][s0],target[s0]),
              'skill1_after_learning':accuracy(phases[1][s1],orig[s1]),
              'skill1_final_retained':accuracy(phases[2][s1],orig[s1]),
              'skill0_interference_loss':accuracy(phases[0][s0],orig[s0])-accuracy(phases[1][s0],orig[s0]),
              'skill1_interference_loss':accuracy(phases[1][s1],orig[s1])-accuracy(phases[2][s1],orig[s1]),
              'order_disagreement_skill0':float(np.mean(phases[2][s0]!=rev[s0])),
              'order_disagreement_skill1':float(np.mean(phases[2][s1]!=rev[s1])),
              'reset':accuracy(np.ones(len(q)),target),'swap':accuracy(swap,target)}
            rows.append(metrics);outs.append({'seed':H['seed'],'phase_predictions':[p.tolist() for p in phases],
               'original_targets':orig.tolist(),'final_targets':target.tolist(),'reverse_predictions':rev.tolist(),'swapped_predictions':swap.tolist()})
            if METHODS[name][0]=='lms':allstates[name+f'_s{H["seed"]}']=st[-1]
        results[name]={'config':cfg,'metrics':{k:interval([r[k] for r in rows]) for k in rows[0] if k!='seed'},'per_history':rows}
        decisions[name]=outs
    pairs={}
    for a,b in [('model_lms_routed','model_knn_routed'),('model_lms_routed','model_lms_shared'),
                 ('model_knn_routed','lexical_knn_routed'),('model_lms_routed','lexical_lms_routed')]:
        pairs[a+' minus '+b]=interval([x['final_mean']-y['final_mean'] for x,y in zip(results[a]['per_history'],results[b]['per_history'])])
    out={'scope':'plaintext synthetic text transfer and readout interference; frozen actual model',
      'feature_dimensions':{k:v.shape[1] for k,v in maps.items()},'model_feature_scales':scales,
      'lexical_teacher_vocabulary':vocab,'query_count_per_skill':len(q0),'teaching_events_per_history':192,
      'results':results,'paired_history_differences':pairs,'runtime_seconds':time.perf_counter()-start,
      'script_sha256':sha(__file__),'data_script_sha256':sha(ROOT/'text_transfer_data.py'),
      'protocol_sha256':sha(ROOT/'TEXT_TRANSFER_PROTOCOL.md'),'selection_sha256':sha(ROOT/'text_transfer_selection.json')}
    np.savez(ROOT/'text_transfer_states.npz',**allstates)
    (ROOT/'text_transfer_results.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    (ROOT/'text_transfer_histories.json').write_text(json.dumps({'groups':groups,'query_ids':q.tolist()},indent=2,sort_keys=True)+'\n')
    (ROOT/'text_transfer_decisions.json').write_text(json.dumps(decisions,separators=(',',':'),sort_keys=True)+'\n')
    print(json.dumps({'complete':True,'runtime_seconds':out['runtime_seconds'],
                     'final_mean':{n:x['metrics']['final_mean']['mean'] for n,x in results.items()}}),flush=True)

if __name__=='__main__':main()
