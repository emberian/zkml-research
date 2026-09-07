"""Independent Python-integer replay and complete-denominator audit; no model."""
import hashlib,json,math,sys,time
from pathlib import Path
sys.dont_write_bytecode=True
import numpy as np
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
    t=time.perf_counter();R=load(ROOT/'results.json');records=load(ROOT/'records.json')
    Hs=load(ROOT/'histories.json')['histories'];features=np.load(ROOT/'features.npz')
    for p,digest in load(ROOT/'freeze.json')['source_sha256'].items():assert sha(p)==digest,p
    assert R['selection_sha256']==sha(ROOT/'selection.json')
    assert load(ROOT/'extraction.json')['selection_sha256']==sha(ROOT/'selection.json')
    assert R['features_sha256']==sha(ROOT/'features.npz')
    count=0;final=0;correct={};retention=0
    for name,method in R['results'].items():
        correct[name]={k:0 for k in ['phase1','phase2','phase3']}
        assert len(method['per_history'])==64
        for H,row in zip(Hs,method['per_history']):
            assert H['seed']==row['seed'];assert row['query_ids']==list(range(256,384))
            for phase in range(3):
                assert len(row['scores'][phase])==len(row['targets'][phase])==len(row['predictions'][phase])==128
                for rid,score,pred,target in zip(row['query_ids'],row['scores'][phase],row['predictions'][phase],row['targets'][phase]):
                    record=records[rid];s=record['skill'];gold=H['rules'][s][2*record['a']+record['b']]
                    if phase==2 and s==0:gold=-gold
                    assert gold==target;assert pred==(1 if score>=0 else -1)
                    count+=1;final+=int(phase==2);correct[name][f'phase{phase+1}']+=int(pred==gold)
                assert sum(target==1 for target in row['targets'][phase])==64
            assert row['predictions'][0][:64]==row['predictions'][1][:64]
            assert row['predictions'][1][64:]==row['predictions'][2][64:];retention+=2
        assert correct[name]['phase3']/8192==method['metrics']['final_mean']['mean']
    assert count==122880 and final==40960 and retention==640
    primary=features['calibrated_soft8'];integer_scores=0;vectors=0;max_abs_score=0
    # Independent implementation keeps integer lists, slices the latest32,
    # recomputes sums from retained contributions, and never imports run.py.
    for H,row in zip(Hs,R['results']['calibrated_soft8']['per_history']):
        queues=[[],[]];prior=None
        for phase,ids in enumerate(H['phases']):
            for rid in ids:
                r=records[rid];s=r['skill'];y=H['rules'][s][2*r['a']+r['b']]
                if phase==2 and s==0:y=-y
                vector=[y*int(x) for x in primary[rid,:8]]
                assert all(-127<=x<=127 for x in vector)
                queues[s]=(queues[s]+[vector])[-32:]
            states=[[sum(v[j] for v in q) for j in range(8)] for q in queues];vectors+=2
            assert all(abs(x)<=4064 for state in states for x in state)
            if phase==1:assert states[0]==prior[0]
            if phase==2:assert states[1]==prior[1]
            for rid,want in zip(row['query_ids'],row['scores'][phase]):
                score=sum(a*int(b) for a,b in zip(states[records[rid]['skill']],primary[rid,:8]))
                assert score==want;integer_scores+=1;max_abs_score=max(max_abs_score,abs(score))
            prior=states
    assert integer_scores==24576 and vectors==384
    # Full zero padding, public coefficient ranges, and route-slot support.
    for name,Q in features.items():
        assert Q.shape==(384,577) and int(Q.min())>=-127 and int(Q.max())<=127
        if name in ['calibrated_soft8','calibrated_hard8','attribute8']:
            assert not np.any(Q[:,8:])
            for r in records:
                assert not np.any(Q[r['id'],4*(1-r['skill']):4*(1-r['skill'])+4])
    # Gold test attribute metadata is not accepted by the feature API.
    import run as protocol
    h=np.concatenate([np.load(protocol.BASE/'representation_features.npz')['mean_10'][:256],np.load(ROOT/'new_features.npz')['mean_10']]).astype(float)
    routes=np.array([r['skill'] for r in records]);rebuilt,_,_=protocol.feature_arrays(h,routes)
    for name,Q in rebuilt.items():assert np.array_equal(Q,features[name])
    paired={}
    for method in ['calibrated_soft8','calibrated_hard8']:
        paired[method]={}
        for ref in ['original577','quadratic8']:
            gains=[]
            for a,b in zip(R['results'][method]['per_history'],R['results'][ref]['per_history']):
                ca=sum(x==y for x,y in zip(a['predictions'][2],a['targets'][2]));cb=sum(x==y for x,y in zip(b['predictions'][2],b['targets'][2]));gains.append((ca-cb)/128)
            mean=sum(gains)/64;sd=math.sqrt(sum((x-mean)**2 for x in gains)/63)
            assert mean==R['paired_final'][method][ref]['mean']
            assert abs(1.96*sd/8-R['paired_final'][method][ref]['normal95_half_width'])<1e-14
            paired[method][ref]={'net_additional_final_correct':int(mean*8192),'paired_histories':64}
    attr=load(ROOT/'attribute_predictions.json');attribute_correct={}
    for s in [0,1]:
        for template in [0,1]:
            rows=[a for a in attr if a['route']==s and records[a['record_id']]['template']==template]
            attribute_correct[f'route{s}_template{template}']={'texts':len(rows),
              'attribute_a_correct':sum((a['predicted_probabilities'][0]>=.5)==bool(a['gold_attributes'][0]) for a in rows),
              'attribute_b_correct':sum((a['predicted_probabilities'][1]>=.5)==bool(a['gold_attributes'][1]) for a in rows)}
    result={'passed':True,'all_prediction_records':count,'all_final_prediction_records':final,
      'primary_independent_python_integer_scores':integer_scores,'primary_independent_checkpoint_vectors':vectors,
      'primary_max_abs_score_observed':max_abs_score,'correct_counts_by_phase':correct,
      'paired_counts':paired,'state_and_output_retention_equalities':retention,
      'four_model_derived_feature_arrays_rebuilt_without_gold_attribute_arguments':True,
      'attribute_accuracy_by_all_route_template_cells':attribute_correct,
      'sha256':{'audit.py':sha(__file__),'results.json':sha(ROOT/'results.json')},'wall_seconds':time.perf_counter()-t}
    (ROOT/'audit.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n');print(json.dumps(result,indent=2))
if __name__=='__main__':main()
