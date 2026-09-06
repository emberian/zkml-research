"""Exact bounded int64 readout vs Python-bigint reference and frozen floating control."""
import hashlib,json,time
from pathlib import Path
import numpy as np
import run_controls as base
ROOT=Path(__file__).resolve().parent

def round_div(n,q):return (n+q//2)//q

def step_np(M,P,y,R,q):
    dot=int(M@P);s=round_div(dot,q);e=q*int(y)-s
    numer=R*M+e*P+q//2
    candidate=numer//q; new=np.clip(candidate,-16*q,16*q)
    metrics={'clipped':int(np.count_nonzero(candidate!=new)),'dot_abs':abs(dot),
             'numerator_abs':int(np.max(np.abs(numer))),'state_abs':int(np.max(np.abs(new)))}
    return new,metrics

def step_big(M,P,y,R,q):
    s=round_div(sum(int(m)*int(p) for m,p in zip(M,P)),q);e=q*int(y)-s
    return [max(-16*q,min(16*q,round_div(R*int(m)+e*int(p),q))) for m,p in zip(M,P)]

def test_exact():
    rng=np.random.default_rng(66721);cases=0;ties=[]
    for bits in (8,12,16):
        q=1<<bits
        for sign in (-1,1):
            for k in range(-5,6):
                n=k*q+q//2
                assert round_div(n,q)==k+1
                ties.append([bits,n,round_div(n,q)])
        for dim in (6,65,577):
            bound=(16*dim+17)*q*q+3*q//2
            assert bound<2**63 and 16*dim*q*q+q//2<2**63
            for j in range(12):
                M=rng.integers(-16*q,16*q+1,size=dim,dtype=np.int64)
                P=rng.integers(-q,q+1,size=dim,dtype=np.int64)
                if j<4:
                    M.fill((-1 if j&1 else 1)*16*q);P.fill((-1 if j&2 else 1)*q)
                R=int(rng.integers(0,q+1));y=int(rng.choice([-1,1]))
                v,metrics=step_np(M,P,y,R,q);ref=step_big(M,P,y,R,q)
                assert np.array_equal(v,ref)
                assert np.all(np.abs(v)<=16*q)
                assert metrics['numerator_abs']<=bound
                cases+=1
    return {'reference_agreement_cases':cases,'rounding_ties':ties,
            'largest_universal_numerator_bound':(16*577+17)*65536**2+3*65536//2}

def train(P,H,rho,q):
    R=int(np.rint(rho*q));M=np.zeros(P.shape[1],dtype=np.int64)
    obs=np.array(H['obs']);y=np.array(H['labels'])[obs];metrics={'clipped':0,'dot_abs':0,'numerator_abs':0,'state_abs':0}
    mid=None
    for i,(j,label) in enumerate(zip(np.tile(obs,2),np.r_[y,-y])):
        M,row=step_np(M,P[j],label,R,q)
        for k in metrics:metrics[k]=metrics[k]+row[k] if k=='clipped' else max(metrics[k],row[k])
        if i==95:mid=M.copy()
    return M,mid,metrics

def main():
    began=time.perf_counter();exact=test_exact()
    xy,teach,query,poly,maps,dist,prior,scales=base.setup()
    selected=json.loads((ROOT/'selection.json').read_text())['choices']
    histories=[base.history(i,teach,poly) for i in range(44000,44032)]
    results={};quantized={};states_saved={}
    for name,phi in maps.items():
        cfg=selected[name];assert cfg['eta']==1.0
        floating=[base.state_for(name,cfg,H,maps)[0] for H in histories]
        results[name]={}
        for bits in (8,12,16):
            q=1<<bits;pre=np.rint(phi*q);P=np.clip(pre,-q,q).astype(np.int64)
            quantized[name+f'_q{bits}']=P
            learned=[train(P,H,cfg['rho'],q) for H in histories];rows=[]
            for i,(H,(M,mid,counts)) in enumerate(zip(histories,learned)):
                original=np.array(H['labels'])[query];target=-original
                pred=base.sign(P[query]@M);fp=base.sign(phi[query]@floating[i])
                swap=base.sign(P[query]@learned[(i+1)%len(learned)][0])
                rows.append({'seed':H['seed'],'accuracy':base.acc(pred,target),
                  'float_accuracy':base.acc(fp,target),'float_agreement':base.acc(pred,fp),
                  'before_change':base.acc(base.sign(P[query]@mid),original),
                  'reset':base.acc(np.ones(len(query)),target),'swap':base.acc(swap,target),**counts})
                states_saved[name+f'_q{bits}_s{H["seed"]}']=M
            results[name][str(bits)]={'rho_integer':int(np.rint(cfg['rho']*q)),
              'feature_clipping_count':int(np.count_nonzero(P!=pre)),
              'metrics':{k:base.interval([row[k] for row in rows]) for k in rows[0] if k!='seed'},'per_history':rows}
            print(json.dumps({'name':name,'bits':bits,'accuracy':results[name][str(bits)]['metrics']['accuracy']['mean'],
               'float_agreement':results[name][str(bits)]['metrics']['float_agreement']['mean']}),flush=True)
    np.savez(ROOT/'fixed_point_arrays.npz',**quantized,**states_saved)
    out={'scope':'plaintext exact bounded integer readout; float pretrained feature extraction unrefined',
      'seeds':[h['seed'] for h in histories],'results':results,'exact_checks':exact,
      'runtime_seconds':time.perf_counter()-began,'script_sha256':base.sha(__file__),
      'protocol_sha256':base.sha(ROOT/'FIXED_POINT_PROTOCOL.md'),'arrays_sha256':base.sha(ROOT/'fixed_point_arrays.npz')}
    (ROOT/'fixed_point_results.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'complete':True,'runtime_seconds':out['runtime_seconds'],'exact_checks':exact['reference_agreement_cases']}),flush=True)

if __name__=='__main__':main()
