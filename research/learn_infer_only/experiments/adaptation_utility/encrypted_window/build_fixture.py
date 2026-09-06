"""Issue pinned cached-feature fixtures; no model runtime or HE outcomes here."""
import hashlib, json, sys
from collections import deque
from pathlib import Path
import numpy as np

HERE = Path(__file__).resolve().parent
BASE = HERE.parent
sys.path.insert(0, str(BASE))
from text_transfer_data import features, labels
from representation_controls import train, predict

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    prereg = HERE / 'PREREGISTRATION.md'
    assert sha(prereg) == '1d6c88d6e42adba24240fd6450fffed93f1b739fea89ef14cd920fcfc85b35e7'
    records = json.loads((BASE/'representation_records.json').read_text())
    groups = json.loads((BASE/'representation_histories.json').read_text())['groups']
    selected = json.loads((BASE/'representation_selection.json').read_text())
    method = 'model_window_routed'
    assert selected['chosen_representation_by_method'][method] == 'mean_10'
    cfg = selected['choices']['mean_10/'+method]['configuration']
    assert cfg == {'capacity': 64}
    hidden = np.load(BASE/'representation_features.npz')['mean_10']
    F, skill, _, scales = features(records, hidden)
    Q = {k: np.clip(np.rint(v*127), -127, 127).astype(np.int8) for k,v in F.items()}
    vectors = Q['model']
    assert vectors.shape == (384,577)
    queries = sorted(i for s in [0,1] for a in [0,1] for b in [0,1]
        for i in sorted(r['id'] for r in records if r['pool']=='test'
                        and (r['skill'],r['a'],r['b']) == (s,a,b))[:2])
    assert len(queries) == 16
    output = ['Q83_WINDOW_V1 577 32 2']
    histories = []
    max_state = max_score = max_contribution = max_query = 0
    for seed, coins in [(63000,201),(63001,202)]:
        H = next(h for h in groups['test'] if h['seed']==seed)
        assert list(map(len,H['phases'])) == [64,64,64]
        states = train(method,cfg,H,records,F,Q,skill)
        queues = [deque(),deque()]
        state = [[0]*577 for _ in range(2)]
        output.append(f'H {seed} {coins}')
        saved = {'seed':seed,'test_coin_byte':coins,'rules':H['rules'],'checkpoints':[]}
        for phase, ids in enumerate(H['phases'],1):
            ys = labels(H,records,ids,flip0=phase==3)
            for local,(rid,y) in enumerate(zip(ids,ys),1):
                route = int(skill[rid]); y=int(y)
                z = [y*int(v) for v in vectors[rid]]
                assert all(-127<=v<=127 for v in z)
                max_contribution=max(max_contribution,max(map(abs,z)))
                queues[route].append(z)
                state[route]=[a+b for a,b in zip(state[route],z)]
                if len(queues[route])>32:
                    old=queues[route].popleft()
                    state[route]=[a-b for a,b in zip(state[route],old)]
                output.append(' '.join(map(str,['L',phase,(phase-1)*64+local,route,rid,y,*z])))
            assert np.array_equal(np.array(state),states[phase-1])
            for route in [0,1]:
                max_state=max(max_state,max(map(abs,state[route])))
                output.append(' '.join(map(str,['P',phase,route,len(queues[route]),*state[route]])))
            targets=labels(H,records,queries,flip0=phase==3).tolist()
            scores=[]
            for rid,target in zip(queries,targets):
                route=int(skill[rid]); q=list(map(int,vectors[rid]))
                score=sum(a*b for a,b in zip(state[route],q))
                max_score=max(max_score,abs(score));max_query=max(max_query,max(map(abs,q)))
                scores.append(score)
                output.append(' '.join(map(str,['Q',phase,rid,route,score,target,*q])))
            pred=[1 if v>=0 else -1 for v in scores]
            assert pred==predict(method,cfg,states[phase-1],queries,F,Q,skill,None).tolist()
            saved['checkpoints'].append({'phase':phase,'steps':phase*64,'queue_counts':list(map(len,queues)),
                'scores':scores,'predictions':pred,'targets':targets})
        output.append('END')
        histories.append(saved)
    payload='\n'.join(output)+'\n'
    (HERE/'fixture.txt').write_text(payload)
    sources = ['representation_records.json','representation_histories.json','representation_selection.json',
        'representation_features.npz','representation_model_manifest.json','model_manifest.json',
        'text_transfer_data.py','representation_controls.py','requirements-lock.txt']
    he=BASE.parent/'he_closure_costs'/'sliding_window_83_probe'
    provenance={str(BASE/name):sha(BASE/name) for name in sources}
    provenance.update({str(he/name):sha(he/name) for name in ['Cargo.toml','Cargo.lock','src/main.rs']})
    result={'scope':'plaintext issuer and exact integer oracle; actual encrypted outcomes are separate',
        'preregistration_sha256':sha(prereg),'generator_sha256':sha(__file__),
        'fixture_sha256':sha(HERE/'fixture.txt'),'method':method,'representation':'mean_10',
        'capacity_total':64,'capacity_per_route':32,'dimension':577,'query_ids':queries,
        'query_metadata':[{k:records[i][k] for k in ['id','skill','a','b','entity','template']} for i in queries],
        'histories':histories,'teacher_only_scales':scales,'source_sha256':provenance,
        'bounds':{'actual_max_abs_contribution':max_contribution,'actual_max_abs_query':max_query,
            'actual_checkpoint_max_abs_state':max_state,'actual_max_abs_score':max_score,
            'declared_max_abs_state':32*127,'declared_max_abs_score':577*32*127*127,
            'plaintext_modulus':4294828033,'signed_half_modulus_floor':4294828033//2},
        'checks':{'original_train_snapshots_equal':True,'original_predict_signs_equal':True,
            'learn_events':384,'checkpoint_routes':12,'queries':96,'model_executed':False}}
    (HERE/'fixture_manifest.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'fixture_sha256':result['fixture_sha256'],'query_ids':queries,'checks':result['checks'],
                      'bounds':result['bounds']},sort_keys=True))

if __name__=='__main__': main()
