"""Separate scalar/subsequence replay: does not import evaluator or call a model."""
import math
import time
from common import ROOT, PRIOR, load, save, sha, verify_freeze, cell, stats

def main():
    start=time.perf_counter();pins=verify_freeze()
    result=load(ROOT/'results.json')
    for n,row in result['files'].items(): assert sha(ROOT/n)==row['sha256'],n
    histories=load(PRIOR/'histories.json')['histories']
    records=load(PRIOR/'records.json')
    bits={p['record_id']:(p['a'],p['b']) for name in ['teacher_predictions.json','test_predictions.json'] for p in load(PRIOR/name)}
    queries=load(ROOT/'query_scores.json');steps=load(ROOT/'transitions.json')
    qmap={(r['seed'],r['phase'],r['record_id']):r for r in queries}
    tmap={(r['seed'],r['learn_step']):r for r in steps}
    saved=load(PRIOR/'results.json')['results']
    checkpoints=load(ROOT/'checkpoint_states.json')
    arithmetic_cases=0
    for s in range(-120,121):
        for u in [-120,120]:
            delta=math.floor((u-s)/8)
            assert s+delta==(7*s+u)//8 and -120<=s+delta<=120
            arithmetic_cases+=1
    assert (7*0+120)//8==15 and (7*15-120)//8==-2
    assert int((7*15-120)/8)==-1 # Truncation is a different learner.
    score_checks=state_cell_checks=transition_checks=0
    for hi,h in enumerate(histories):
        history_prefix=[]
        for phase,ids in enumerate(h['phases'],1):
            for rid in ids:
                rr=records[rid];route=rr['skill'];a,b=bits[rid]
                y=h['rules'][route][2*rr['a']+rr['b']]*(-1 if phase==3 and route==0 else 1)
                history_prefix.append((route,2*a+b,120*y))
                # Re-fold all per-bin subsequences afresh, avoiding the evaluator's selected-write loop.
                state=[]
                for r in [0,1]:
                    registers=[]
                    for address in range(4):
                        z=0
                        for rr,bb,u in history_prefix:
                            if (rr,bb)==(r,address): z+=math.floor((u-z)/8)
                        registers.append(z)
                    state.append(registers)
                tr=tmap[h['seed'],len(history_prefix)]
                assert tr['state_after']==state and tr['u']==120*y and tr['record_id']==rid
                transition_checks+=1
            assert checkpoints[hi]['seed']==h['seed'] and checkpoints[hi]['checkpoint_states'][phase-1]==state
            state_cell_checks+=8
            for rid in range(256,384):
                rr=records[rid];route=rr['skill'];a,b=bits[rid];address=2*a+b
                target=h['rules'][route][2*rr['a']+rr['b']]*(-1 if phase==3 and route==0 else 1)
                q=qmap[h['seed'],phase,rid]
                assert q['target']==target and q['bin']==address
                assert q['ema_score']==state[route][address]
                assert q['ema_prediction']==(-1 if state[route][address]<0 else 1)
                routed=[e for e in history_prefix if e[0]==route][-32:]
                window=16129*sum(u//120 for r,bb,u in routed if bb==address)
                assert q['window_score']==window
                for method,key in [('semantic577','window'),('original577','original'),('attribute8','gold_window')]:
                    prior=saved[method]['per_history'][hi]
                    assert q[key+'_score']==prior['scores'][phase-1][rid-256]
                    assert q[key+'_prediction']==prior['predictions'][phase-1][rid-256]
                    assert prior['targets'][phase-1][rid-256]==target
                score_checks+=1
    final=[q for q in queries if q['phase']==3]
    for name in result['final']:assert result['final'][name]==cell(final,name+'_prediction')
    for phase in [1,2,3]:
        for route in [0,1]:
            rr=[q for q in queries if q['phase']==phase and q['route']==route]
            for name,c in result['phase_route'][f'phase{phase}.route{route}'].items():assert c==cell(rr,name+'_prediction')
    for h in result['per_history']:
        rr=[q for q in final if q['seed']==h['seed']]
        for name in result['final']: assert h[name]==cell(rr,name+'_prediction')
    for method,s in result['paired_ema_minus'].items():
        assert s==stats([h['ema']['accuracy']-h[method]['accuracy'] for h in result['per_history']])
    fixture=load(ROOT/'materialized_fixture.json');original=load(PRIOR/'materialized/fixture.json')
    assert len(fixture['events'])==len(original['events'])==480
    for event,prior in zip(fixture['events'],original['events']):
        for k in ['event_id','event_ordinal','history_id','history_index','kind','learn_step','phase','route','record_id']:
            assert event[k]==prior[k]
        if event['kind']=='Learn':
            tr=tmap[event['history_id'],event['learn_step']]
            assert event['state_after']==tr['state_after'] and event['u']==tr['u'] and event['bin']==tr['bin']
        else:
            q=qmap[event['history_id'],event['phase'],event['record_id']]
            for k in ['bin','ema_score','ema_prediction','target','window_score','window_prediction']:assert event[k]==q[k]
    out={'passed':True,'audit_kind':'independent implementation, same author; not independent human review',
         'complete_ema_query_score_checks':score_checks,'prior_window_comparator_score_checks':3*score_checks,
         'subsequence_refold_transition_checks':transition_checks,'checkpoint_register_checks':state_cell_checks,
         'exhaustive_range_recurrence_cases':arithmetic_cases,'floor_truncation_falsifier':{'floor':-2,'truncation':-1},
         'materialized_event_checks':len(fixture['events']),'frozen_files_before_and_after':pins,
         'results_sha256':sha(ROOT/'results.json'),'audit_wall_seconds':time.perf_counter()-start,
         'new_model_calls':0,'encrypted_operations':0,'web_searches':0,'scry_sql':0,'scry_schema':0}
    verify_freeze();save(ROOT/'audit.json',out);print(out)

if __name__=='__main__':main()
