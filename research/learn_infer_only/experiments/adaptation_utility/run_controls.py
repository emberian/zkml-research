"""Plaintext utility controls. Real backbone features are produced separately."""
import hashlib, itertools, json, math, time
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parent
ETAS=[0.03,0.1,0.3,1.0]; RHOS=[1.0,0.995,0.98,0.95]
KS=[1,3,7,15]; CAPS=[32,64,192]

def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def sign(v): return np.where(np.asarray(v)>=0,1,-1)

def setup():
    z=np.load(ROOT/'features.npz'); xy=z['xy']; h=z['hidden'].astype(np.float64)
    split=np.random.default_rng(7357).permutation(len(xy)); teach=split[:192]; test=split[192:]
    center=h[teach].mean(0); centered=h-center
    projection=np.random.default_rng(91913).choice([-1.0,1.0],size=(576,64))/8
    x,y=xy.T/8
    poly=np.stack([np.ones(len(x)),x,y,x*y,x*x,y*y],axis=1)
    maps={'smol_lms_576':np.column_stack([centered,np.ones(len(x))]),
          'smol_lms_64':np.column_stack([centered@projection,np.ones(len(x))]),
          'quadratic_lms_6':poly.copy()}
    scales={}
    for k,v in maps.items():
        scales[k]=float(np.linalg.norm(v[teach],axis=1).max());maps[k]=v/scales[k]
    distances={}
    for name,features in [('knn_smol',centered),('knn_xy',xy/8)]:
        distances[name]=np.sum((features[:,None,:]-features[None,:,:])**2,axis=-1)
    base=sign(z['selected_logits'][:,0]-z['selected_logits'][:,1])
    return xy,teach,test,poly,maps,distances,base,scales

def history(seed,teach,poly):
    rng=np.random.default_rng(seed)
    for attempt in range(1000):
        w=rng.normal(size=6); w[:3]*=.5
        labels=sign(poly@w)
        if .2 <= np.mean(labels==1) <= .8:break
    else: raise RuntimeError('nonvacuous concept generation failed')
    obs=rng.choice(teach,size=96,replace=False)
    return {'seed':seed,'w':w.tolist(),'obs':obs.tolist(),'labels':labels.tolist(),
            'positive_fraction':float(np.mean(labels==1)),'attempt':attempt}

def lms_run(phi,obs,y,eta,rho):
    m=np.zeros(phi.shape[1]);mid=None
    for i,(j,label) in enumerate(zip(obs,y)):
        v=phi[j]; m=rho*m+eta*(label-np.dot(m,v))*v
        if i==95:mid=m.copy()
    return m,mid

def state_for(name,cfg,H,maps,reverse=False):
    ids=np.array(H['obs']); lab=np.array(H['labels'])[ids]
    if reverse:lab=-lab
    ids=np.tile(ids,2); y=np.r_[lab,-lab]
    if 'lms' in name:return lms_run(maps[name],ids,y,**cfg)
    if name=='fading_mean':
        m=0.;mid=None
        for i,v in enumerate(y):
            m=cfg['rho']*m+v
            if i==95:mid=m
        return m,mid
    if name.startswith('knn'):
        n=cfg['capacity'];return (ids[-n:],y[-n:]),(ids[:96][-n:],y[:96][-n:])
    return None,None

def predict(name,cfg,state,queries,maps,distances,base):
    if 'lms' in name:return sign(maps[name][queries]@state)
    if name=='fading_mean':return np.full(len(queries),int(sign(state)))
    if name.startswith('knn'):
        ids,y=state
        # Stable sort pins ties by stored-event order.
        ix=np.argsort(distances[name][queries][:,ids],axis=1,kind='stable')[:,:cfg['k']]
        return sign(y[ix].sum(1))
    if name=='frozen_lm_ab':return base[queries]
    if name=='no_memory':return np.ones(len(queries),dtype=int)
    raise ValueError(name)

def candidates(name):
    if 'lms' in name:return [dict(eta=e,rho=r) for e,r in itertools.product(ETAS,RHOS)]
    if name.startswith('knn'):return [dict(k=k,capacity=n) for k,n in itertools.product(KS,CAPS)]
    if name=='fading_mean':return [dict(rho=r) for r in RHOS]
    return [{}]

def acc(pred,target):return float(np.mean(pred==target))
def interval(values):
    a=np.array(values);n=len(a); se=float(a.std(ddof=1)/math.sqrt(n)) if n>1 else None
    return {'mean':float(a.mean()),'history_sd':float(a.std(ddof=1)) if n>1 else None,
      'normal_95_half_width':1.96*se if se is not None else None,'n_histories':n,
      'min':float(a.min()),'max':float(a.max())}

def main():
    started=time.perf_counter()
    xy,teach,queries,poly,maps,distances,base,scales=setup()
    groups={'development':[history(i,teach,poly) for i in range(11000,11008)],
            'selection':[history(i,teach,poly) for i in range(22000,22008)],
            'test':[history(i,teach,poly) for i in range(33000,33032)]}
    assert len(set(teach)&set(queries))==0
    assert len({h['seed'] for hs in groups.values() for h in hs})==48
    names=['frozen_lm_ab','no_memory','fading_mean','knn_smol','knn_xy',
           'smol_lms_576','smol_lms_64','quadratic_lms_6']
    selections={};tuning={};development={}
    for name in names:
        tuning[name]=[]
        for cfg in candidates(name):
            scores=[]
            for H in groups['selection']:
                st,_=state_for(name,cfg,H,maps)
                p=predict(name,cfg,st,queries,maps,distances,base)
                scores.append(acc(p,-np.array(H['labels'])[queries]))
            tuning[name].append({'config':cfg,'post_change_accuracy':interval(scores)})
        # Explicit deterministic selection: score descending, serialized configuration ascending.
        selected=sorted(tuning[name],key=lambda z:(-z['post_change_accuracy']['mean'],json.dumps(z['config'],sort_keys=True)))[0]
        cfg=selected['config'];selections[name]=cfg
        ds=[]
        for H in groups['development']:
            st,_=state_for(name,cfg,H,maps)
            ds.append(acc(predict(name,cfg,st,queries,maps,distances,base),-np.array(H['labels'])[queries]))
        development[name]=interval(ds)
        print(json.dumps({'selected':name,'config':cfg,'selection_accuracy':selected['post_change_accuracy']['mean']}),flush=True)
    # Selection choices persisted before any held-out evaluation begins.
    (ROOT/'selection.json').write_text(json.dumps({'choices':selections,'tuning':tuning,'development':development},indent=2,sort_keys=True)+'\n')
    results={};per_query={}
    for name in names:
        cfg=selections[name]; states=[state_for(name,cfg,H,maps) for H in groups['test']]
        rows=[];decisions=[]
        for i,H in enumerate(groups['test']):
            st,mid=states[i]; original=np.array(H['labels'])[queries];current=-original
            p=predict(name,cfg,st,queries,maps,distances,base)
            before=predict(name,cfg,mid,queries,maps,distances,base)
            reverse,_=state_for(name,cfg,H,maps,reverse=True)
            rev=predict(name,cfg,reverse,queries,maps,distances,base)
            swapped=predict(name,cfg,states[(i+1)%len(states)][0],queries,maps,distances,base)
            if 'lms' in name:reset=np.zeros_like(st)
            elif name=='fading_mean':reset=0.
            elif name.startswith('knn'):reset=None
            else:reset=st
            rp=np.ones(len(queries),dtype=int) if name.startswith('knn') else predict(name,cfg,reset,queries,maps,distances,base)
            rows.append({'seed':H['seed'],'before_change':acc(before,original),'after_change':acc(p,current),
               'old_rule_retention':acc(p,original),'reset':acc(rp,current),'swapped':acc(swapped,current),
               'order_disagreement':float(np.mean(p!=rev)),'reversed_current_accuracy':acc(rev,original),
               'vs_reset_disagreement':float(np.mean(p!=rp)),'vs_swap_disagreement':float(np.mean(p!=swapped))})
            decisions.append({'seed':H['seed'],'current_target':current.tolist(),'after_change':p.tolist(),
              'before_change':before.tolist(),'reverse':rev.tolist(),'reset':rp.tolist(),'swapped':swapped.tolist()})
        results[name]={'config':cfg,'metrics':{k:interval([r[k] for r in rows]) for k in rows[0] if k!='seed'},'per_history':rows}
        per_query[name]=decisions
    # Paired history effects use histories as the unit.
    paired={}
    for left,right in [('smol_lms_576','knn_smol'),('smol_lms_64','knn_smol'),
                        ('quadratic_lms_6','knn_xy'),('smol_lms_576','no_memory')]:
        paired[left+' minus '+right]=interval([l['after_change']-r['after_change']
            for l,r in zip(results[left]['per_history'],results[right]['per_history'])])
    output={'protocol_version':1,'scope':'plaintext actual frozen pretrained model features + learned/task readout; no encryption',
      'seed_groups':{k:[h['seed'] for h in v] for k,v in groups.items()},'teaching_coordinate_count':len(teach),
      'query_coordinate_count':len(queries),'teaching_events_per_history':192,'readout_dimensions':{k:v.shape[1] for k,v in maps.items()},
      'feature_scales':scales,'results':results,'paired_history_effects':paired,
      'runtime_seconds':time.perf_counter()-started,'numpy':np.__version__,
      'script_sha256':sha(__file__),'protocol_sha256':sha(ROOT/'PROTOCOL.md'),
      'features_sha256':sha(ROOT/'features.npz'),'selection_sha256':sha(ROOT/'selection.json')}
    (ROOT/'results.json').write_text(json.dumps(output,indent=2,sort_keys=True)+'\n')
    (ROOT/'histories.json').write_text(json.dumps({'groups':groups,'teach_indices':teach.tolist(),
      'query_indices':queries.tolist(),'coordinate_domain':xy.tolist()},indent=2,sort_keys=True)+'\n')
    (ROOT/'decisions.json').write_text(json.dumps(per_query,separators=(',',':'),sort_keys=True)+'\n')
    print(json.dumps({'complete':True,'runtime_seconds':output['runtime_seconds'],
                     'post_change':{k:v['metrics']['after_change']['mean'] for k,v in results.items()}}),flush=True)

if __name__=='__main__':main()
