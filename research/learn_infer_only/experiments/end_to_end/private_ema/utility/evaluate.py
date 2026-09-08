"""One evaluation of the frozen law on all saved observations and query scores."""
import copy
import csv
import sys
import time
from collections import deque
import numpy as np
from common import ROOT, PRIOR, load, save, sha, verify_freeze, stats, cell

def main():
    started = time.perf_counter()
    assert not (ROOT / 'results.json').exists(), 'Preserve the first evaluation'
    pins = verify_freeze()
    records = load(PRIOR / 'records.json')
    histories = load(PRIOR / 'histories.json')['histories']
    saved = load(PRIOR / 'results.json')['results']
    features = np.load(PRIOR / 'features.npz')['semantic577']
    predictions = load(PRIOR / 'teacher_predictions.json') + load(PRIOR / 'test_predictions.json')
    predicted = {p['record_id']: p for p in predictions}
    assert [h['seed'] for h in histories] == list(range(67000, 67064))
    bins = {}
    for rid in list(range(128)) + list(range(256, 384)):
        r, p = records[rid], predicted[rid]
        assert r['id'] == rid
        active = np.flatnonzero(features[rid]).tolist()
        address = 2*p['a'] + p['b']
        assert active == [4*r['skill'] + address] and int(features[rid, active[0]]) == 127
        bins[rid] = address

    def label(h, rid, phase):
        r = records[rid]
        y = h['rules'][r['skill']][2*r['a'] + r['b']]
        return -y if r['skill'] == 0 and phase == 3 else y

    all_rows, transitions, states = [], [], []
    retained_state_checks = retained_output_checks = window_checks = 0
    per_history = []
    for hi, h in enumerate(histories):
        state = [[0]*4 for _ in range(2)]
        queues = [deque(), deque()]
        checkpoints = []
        history_rows = []
        for phase, ids in enumerate(h['phases'], 1):
            for step, rid in enumerate(ids, 1):
                route, b, y = records[rid]['skill'], bins[rid], label(h, rid, phase)
                before = copy.deepcopy(state)
                state[route][b] = (7*state[route][b] + 120*y)//8
                assert all(-120 <= s <= 120 for rr in state for s in rr)
                assert all(state[r][j] == before[r][j] for r in range(2) for j in range(4) if (r,j)!=(route,b))
                transitions.append({'seed': h['seed'], 'phase': phase, 'learn_step': 64*(phase-1)+step,
                                    'record_id': rid, 'route': route, 'bin': b, 'label': y,
                                    'u': 120*y, 'state_before': before, 'state_after': copy.deepcopy(state)})
                queues[route].append((b, y))
                if len(queues[route]) > 32:
                    queues[route].popleft()
            checkpoints.append(copy.deepcopy(state))
            for rid in range(256, 384):
                r, route, b = records[rid], records[rid]['skill'], bins[rid]
                qidx, target = rid-256, label(h, rid, phase)
                score = state[route][b]
                window_score = 127**2 * sum(y for address,y in queues[route] if address == b)
                comparators = {}
                for name in ['semantic577','original577','attribute8']:
                    old = saved[name]['per_history'][hi]
                    assert old['seed'] == h['seed'] and old['query_ids'][qidx] == rid
                    assert old['targets'][phase-1][qidx] == target
                    oldscore = old['scores'][phase-1][qidx]
                    oldpred = old['predictions'][phase-1][qidx]
                    assert oldpred == (1 if oldscore >= 0 else -1)
                    comparators[name] = {'score': oldscore, 'prediction': oldpred}
                assert window_score == comparators['semantic577']['score']
                window_checks += 1
                rule = h['rules'][route]
                row = {'seed': h['seed'], 'phase': phase, 'record_id': rid, 'route': route,
                       'bin': b, 'gold_pair': [r['a'], r['b']], 'target': target,
                       'rule_type': 'nonlinear' if rule[0]==rule[3] and rule[1]==rule[2] else 'linear',
                       'joint_rule_stratum': saved['semantic577']['per_history'][hi]['joint_stratum'],
                       'ema_score': score, 'ema_prediction': 1 if score>=0 else -1,
                       'window_score': window_score, 'window_prediction': comparators['semantic577']['prediction'],
                       'original_score': comparators['original577']['score'],
                       'original_prediction': comparators['original577']['prediction'],
                       'gold_window_score': comparators['attribute8']['score'],
                       'gold_window_prediction': comparators['attribute8']['prediction']}
                all_rows.append(row); history_rows.append(row)
        assert checkpoints[0][0] == checkpoints[1][0] and checkpoints[1][1] == checkpoints[2][1]
        retained_state_checks += 2
        for route, p1, p2 in [(0,1,2),(1,2,3)]:
            left = [(r['ema_score'],r['ema_prediction']) for r in history_rows if r['phase']==p1 and r['route']==route]
            right = [(r['ema_score'],r['ema_prediction']) for r in history_rows if r['phase']==p2 and r['route']==route]
            assert left == right
            retained_output_checks += len(left)
        final = [r for r in history_rows if r['phase']==3]
        per_history.append({'seed':h['seed'], 'ema':cell(final), 'window':cell(final,'window_prediction'),
                            'original':cell(final,'original_prediction'), 'gold_window':cell(final,'gold_window_prediction')})
        states.append({'seed':h['seed'],'checkpoint_states':checkpoints})

    methods = ['ema','window','original','gold_window']
    phases = {}
    for phase in [1,2,3]:
        for route in [0,1]:
            rr = [r for r in all_rows if r['phase']==phase and r['route']==route]
            phases[f'phase{phase}.route{route}'] = {m:cell(rr,m+'_prediction') for m in methods}
    final = [r for r in all_rows if r['phase']==3]
    strata = {}
    for field in ['rule_type','joint_rule_stratum']:
        strata[field] = {value:{m:cell([r for r in final if r[field]==value],m+'_prediction') for m in methods}
                         for value in sorted({r[field] for r in final})}
    strata['task_attribute'] = {f'route{route}.{a}{b}':{m:cell([r for r in final if r['route']==route and r['gold_pair']==[a,b]],m+'_prediction') for m in methods}
                               for route in [0,1] for a in [0,1] for b in [0,1]}

    # Reuse exact materialized event IDs/order and requests; do not resample.
    prior_fixture = load(PRIOR / 'materialized/fixture.json')
    byscore = {(r['seed'],r['phase'],r['record_id']):r for r in all_rows}
    bystep = {(r['seed'],r['learn_step']):r for r in transitions}
    compact = []
    for e in prior_fixture['events']:
        v = {k:e[k] for k in ['event_id','event_ordinal','history_id','history_index','kind','learn_step','phase','route','record_id']}
        if e['kind']=='Learn':
            tr = bystep[e['history_id'],e['learn_step']]
            old = prior_fixture['learn_vectors'][e['learn_vector_index']]
            assert tr['record_id']==e['record_id'] and tr['label']==old['signed_label']
            assert tr['bin']==2*old['predicted_pair'][0]+old['predicted_pair'][1]
            v.update({'bin':tr['bin'],'u':tr['u'],'state_after':tr['state_after']})
        else:
            rr = byscore[e['history_id'],e['phase'],e['record_id']]
            v.update({k:rr[k] for k in ['bin','ema_score','ema_prediction','target','window_score','window_prediction']})
        compact.append(v)
    assert len(compact)==480 and sum(e['kind']=='Learn' for e in compact)==384
    materialized_final = [e for e in compact if e['kind']=='Infer' and e['phase']==3]
    materialized = {'exposure':'PUBLIC reused synthetic fixture and test oracle; never a host clear-input file',
                    'schema':'ema-semantic-fixture-v1','source_fixture_sha256':sha(PRIOR/'materialized/fixture.json'),
                    'history_seeds':[67000,67001], 'events':compact,
                    'counts':{'Learn':384,'Infer':96,'expiry':0},
                    'final':{m:cell(materialized_final,m+'_prediction') for m in ['ema','window']}}
    save(ROOT/'materialized_fixture.json',materialized)
    save(ROOT/'query_scores.json',all_rows)
    save(ROOT/'transitions.json',transitions)
    save(ROOT/'checkpoint_states.json',states)
    out = {'execution_passed':True, 'scope':'reused-data exploratory, not a new heldout estimate',
           'denominators':{'reused_teacher_texts':128,'reused_query_texts':128,'histories':64,'checkpoints':3,
                           'Learn':len(transitions),'EMA_query_scores':len(all_rows),'final_queries':len(final)},
           'final':{m:cell(final,m+'_prediction') for m in methods}, 'phase_route':phases,'strata':strata,
           'per_history':per_history,
           'paired_ema_minus':{m:stats([h['ema']['accuracy']-h[m]['accuracy'] for h in per_history]) for m in methods[1:]},
           'paired_label_changes_vs_window':{'all_checkpoints':sum(r['ema_prediction']!=r['window_prediction'] for r in all_rows),
                     'final':sum(r['ema_prediction']!=r['window_prediction'] for r in final),
                     'final_improved':sum(r['ema_prediction']==r['target'] and r['window_prediction']!=r['target'] for r in final),
                     'final_regressed':sum(r['ema_prediction']!=r['target'] and r['window_prediction']==r['target'] for r in final)},
           'controls':{'semantic_window_scores_recomputed':window_checks,'untouched_route_state_checks':retained_state_checks,
                       'untouched_route_score_and_sign_checks':retained_output_checks,'source_feature_rows_checked':len(bins),
                       'minimum_state':min(s for tr in transitions for route in tr['state_after'] for s in route),
                       'maximum_state':max(s for tr in transitions for route in tr['state_after'] for s in route)},
           'materialized_counts':materialized['counts'],'materialized_final':materialized['final'],
           'frozen_source_files_verified':pins, 'freeze_sha256':sha(ROOT/'freeze.json'),
           'new_model_calls':0,'encrypted_operations':0,'web_searches':0,'scry_sql':0,'scry_schema':0,
           'evaluation_wall_seconds':time.perf_counter()-started,'python':sys.version}
    out['files'] = {n:{'sha256':sha(ROOT/n),'bytes':(ROOT/n).stat().st_size} for n in
                    ['query_scores.json','transitions.json','checkpoint_states.json','materialized_fixture.json']}
    verify_freeze()
    save(ROOT/'results.json',out)
    with (ROOT/'per_history.csv').open('w',newline='') as f:
        writer=csv.DictWriter(f,fieldnames=['seed']+[m+'_correct' for m in methods]+['final_queries']);writer.writeheader()
        for h in per_history:writer.writerow({'seed':h['seed'],**{m+'_correct':h[m]['correct'] for m in methods},'final_queries':128})
    print({k:out[k] for k in ['execution_passed','scope','denominators','final','paired_ema_minus','controls','materialized_final','evaluation_wall_seconds']})

if __name__=='__main__':
    main()
