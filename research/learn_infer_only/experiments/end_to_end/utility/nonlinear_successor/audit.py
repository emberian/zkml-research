"""Audit retained predictions, denominators, hashes and the frozen decision rule."""
from pathlib import Path
import hashlib,json,math
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parents[2]/'adaptation_utility'
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def main():
    result=load(ROOT/'results.json');selection=load(ROOT/'selection.json');prep=load(ROOT/'preparation.json')
    Hs={h['seed']:h for h in load(ROOT/'histories.json')['histories']};records=load(BASE/'representation_records.json')
    assert set(Hs)==set(range(64000,64064))
    original=load(BASE/'representation_histories.json')['groups']
    assert set(Hs).isdisjoint(h['seed'] for group in original.values() for h in group)
    for path,h in prep['source_sha256'].items():assert sha(path)==h
    for name,field in [('features.npz','features_sha256'),('parameters.npz','parameters_sha256'),('histories.json','histories_sha256')]:assert sha(ROOT/name)==prep[field]
    assert sha(ROOT/'selection.json')==result['selection_sha256']
    assert sha(ROOT/'PREREGISTRATION.md')==result['preregistration_sha256']==selection['preregistration_sha256']==prep['preregistration_sha256']
    assert sha(ROOT/'run.py')==result['script_sha256']==selection['script_sha256']==prep['script_sha256']
    assert (ROOT/'histories.json').stat().st_mtime_ns <= (ROOT/'selection.json').stat().st_mtime_ns <= (ROOT/'results.json').stat().st_mtime_ns
    for family in ['linear','quadratic']:
        expected=max([8,16,32],key=lambda k:(selection['selection'][f'{family}{k}']['final_mean']['mean'],-k))
        assert selection['chosen_k'][family]==expected
    count=0;metric_rows=0
    for name,out in result['results'].items():
        assert [r['seed'] for r in out['per_history']]==list(range(64000,64064))
        for row in out['per_history']:
            H=Hs[row['seed']];query=row['query_ids']
            assert query==[r['id'] for r in records if r['pool']=='test'] and len(query)==128
            accuracy={}
            for phase in [1,2,3]:
                correct={0:0,1:0}
                for j,rid in enumerate(query):
                    r=records[rid];label=H['rules'][r['skill']][2*r['a']+r['b']]
                    if phase==3 and r['skill']==0:label=-label
                    assert row['targets'][phase-1][j]==label
                    pred=1 if row['scores'][phase-1][j]>=0 else -1
                    assert row['predictions'][phase-1][j]==pred
                    correct[r['skill']]+=pred==label;count+=1
                accuracy[phase]={s:correct[s]/64 for s in [0,1]}
            metrics={'plant_initial':accuracy[1][0],'plant_after_letters':accuracy[2][0],
              'letter_after_learning':accuracy[2][1],'plant_changed':accuracy[3][0],
              'letter_retained':accuracy[3][1],'final_mean':(accuracy[3][0]+accuracy[3][1])/2}
            assert row['metrics']==metrics;metric_rows+=1
        for metric,s in out['metrics'].items():
            vals=[r['metrics'][metric] for r in out['per_history']]
            mean=sum(vals)/len(vals);sd=math.sqrt(sum((x-mean)**2 for x in vals)/(len(vals)-1))
            assert abs(s['mean']-mean)<1e-12 and abs(s['normal95_half_width']-1.96*sd/math.sqrt(len(vals)))<1e-12
        assert sum(s['count'] for s in out['joint_strata'].values())==64
    assert count==98304 and metric_rows==256
    paired=result['paired_quadratic_minus_original'];q=result['results'][result['selected_quadratic']]
    expected={'final_mean_at_least_60pct':q['metrics']['final_mean']['mean']>=.60,
      'paired_gain_at_least_5points':paired['mean']>=.05,
      'paired_descriptive_lower_bound_positive':paired['mean']-paired['normal95_half_width']>0,
      'nonlinear_gain_at_least_10points':result['nonlinear_gain']>=.10}
    assert result['acceptance']==expected and result['useful_successor']==all(expected.values())
    assert sha(BASE/'encrypted_window/fixture.txt')=='41978a10b974a3e8b7f30d5f9c66f7d396fdf7df83b723b3f14dc00359cdb4c0'
    report={'passed':True,'prediction_label_checks':count,'recomputed_history_method_rows':metric_rows,
      'all_histories_retained':64,'fresh_history_seed_disjointness':True,'reused_text_surfaces':True,
      'selection_precedes_test_retained_mtime':True,'frozen_hashes_agree':True,
      'old_e2e_fixture_unchanged':True,'useful_successor':result['useful_successor'],'script_sha256':sha(__file__)}
    (ROOT/'audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))

if __name__=='__main__':main()
