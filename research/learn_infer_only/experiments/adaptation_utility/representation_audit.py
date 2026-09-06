"""Recompute study metrics/selection and derive feature/memory cost rows."""
import csv,json
from pathlib import Path
import numpy as np
from representation_data import make_records
from text_transfer_data import labels
from run_controls import sha,interval
ROOT=Path(__file__).resolve().parent

def main():
    r=json.loads((ROOT/'representation_results.json').read_text())
    s=json.loads((ROOT/'representation_selection.json').read_text())
    m=json.loads((ROOT/'representation_model_manifest.json').read_text())
    h=json.loads((ROOT/'representation_histories.json').read_text())
    rec=json.loads((ROOT/'representation_records.json').read_text())
    assert rec==make_records() # Includes disjointness checks against previous names/cues/templates.
    assert r['protocol_sha256']==m['protocol_sha256']==s['protocol_sha256']==sha(ROOT/'representation_PROTOCOL.md')
    allseeds={H['seed'] for hs in h['groups'].values() for H in hs};assert len(allseeds)==56
    old=json.loads((ROOT/'text_transfer_histories.json').read_text())
    assert allseeds.isdisjoint({H['seed'] for hs in old['groups'].values() for H in hs})
    q=np.array(h['query_ids']);assert all(rec[int(i)]['pool']=='test' for i in q)
    Hby={H['seed']:H for H in h['groups']['test']}
    checked=0;decisions=json.loads((ROOT/'representation_decisions.json').read_text())
    for case,outs in decisions.items():
        rows={x['seed']:x for x in r['results'][case]['per_history']}
        for out in outs:
            target=labels(Hby[out['seed']],rec,q,flip0=True)
            assert np.array_equal(target,out['final_targets'])
            assert np.mean(np.array(out['phase_predictions'][-1])==target)==rows[out['seed']]['final_mean']
            checked+=1
        best=sorted(s['all_selection_candidates'][case],key=lambda x:(-x['selection_final_accuracy']['mean'],json.dumps(x['configuration'],sort_keys=True)))[0]
        assert best==s['choices'][case]
    for method,repr in s['chosen_representation_by_method'].items():
        candidates=[key.split('/')[0] for key in s['choices'] if key.endswith('/'+method)]
        best=sorted(candidates,key=lambda rr:(-s['choices'][rr+'/'+method]['selection_final_accuracy']['mean'],rr))[0]
        assert repr==best
    table=[]
    for case,result in r['results'].items():
        v=result['metrics'];table.append({'case':case,'selected_representation':result['selected_representation_for_method'],
          'configuration':json.dumps(result['configuration'],sort_keys=True),
          'selection_accuracy':s['choices'][case]['selection_final_accuracy']['mean'],
          'test_accuracy':v['final_mean']['mean'],'history_normal_95_half_width':v['final_mean']['normal_95_half_width'],
          'changed_skill0':v['skill0_final_changed']['mean'],'retained_skill1':v['skill1_final_retained']['mean'],
          'skill0_interference_loss':v['skill0_interference_loss']['mean'],'skill1_interference_loss':v['skill1_interference_loss']['mean'],
          'status':'EXECUTED plaintext utility, fixed representation; no security/recovery experiments'})
    with open(ROOT/'representation_results.csv','w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=table[0]);w.writeheader();w.writerows(table)
    n=max(m['batch_padded_tokens']);costs=[]
    for repr in ['last_30','mean_10','mean_20','mean_30']:
        L=int(repr.split('_')[1]);d=576;kv=192;ff=1536
        costs.append({'representation':repr,'layers_required_by_feature_definition':L,'actual_run_layers':30,
          'n_for_count':n,'private_public_linear_products':L*n*(2*d*d+2*d*kv+3*d*ff),
          'private_private_attention_products':2*L*n*n*d,'private_gated_mlp_products':L*n*ff,
          'private_silu':L*n*ff,'private_rsqrt':(2*L+(1 if L==30 else 0))*n,
          'private_softmax_vectors_length_n':L*9*n,'pool_private_additions':d*(n-1) if repr.startswith('mean') else 0,
          'pool_public_length_scalings':d if repr.startswith('mean') else 0,
          'feature_dimension_with_bias':577,'shared_float64_readout_bytes':577*8,'routed_float64_readout_bytes':2*577*8,
          'privacy_condition':'source tokens private => all listed prefix/pooling work private; public length/skill declared; entitled plaintext issuer may encode fixed features',
          'status':'DERIVED scalar counts; actual extraction runs all30blocks; no measured prefix speedup or protected encoder'})
    with open(ROOT/'representation_costs.csv','w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=costs[0]);w.writeheader();w.writerows(costs)
    # Descriptive post-hoc task-family split; NOT used for selecting settings.
    family={};qskills=np.array([rec[int(i)]['skill'] for i in q])
    for method in ['model_lms_routed','model_window_routed']:
        case=s['chosen_representation_by_method'][method]+'/'+method;parts={}
        for skill in [0,1]:
            for typ in ['linear','xor']:
                values=[]
                for out in decisions[case]:
                    rule=Hby[out['seed']]['rules'][skill]
                    isxor=rule[0]==rule[3] and rule[1]==rule[2] and rule[0]!=rule[1]
                    if isxor!=(typ=='xor'):continue
                    p=np.array(out['phase_predictions'][-1]);y=np.array(out['final_targets']);take=qskills==skill
                    values.append(float(np.mean(p[take]==y[take])))
                parts[f'skill{skill}_{typ}']=interval(values)
        family[case]=parts
    audit={'passed':True,'accuracy_rows_recomputed':checked,'selection_rules_recomputed':len(s['choices']),
      'fresh_history_count':56,'query_count':len(q),'fresh_surface_checks':True,'max_padded_tokens':n,
      'posthoc_rule_family_description_not_used_for_selection':family,
      'hashes':{name:sha(ROOT/name) for name in ['representation_PROTOCOL.md','representation_data.py','representation_extract.py',
        'representation_controls.py','representation_selection.json','representation_results.json',
        'representation_results.csv','representation_costs.csv','representation_audit.py']}}
    (ROOT/'representation_audit.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n')
    print(json.dumps(audit,indent=2))

if __name__=='__main__':main()
