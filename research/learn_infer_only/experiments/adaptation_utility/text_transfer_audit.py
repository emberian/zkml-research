"""Audit saved text decisions, split provenance, and complete additive-memory role bill."""
import csv,json
from pathlib import Path
import numpy as np
from run_controls import sha
from text_transfer_data import NAMES,TEMPLATES,CUES,labels
ROOT=Path(__file__).resolve().parent

def main():
    rec=json.loads((ROOT/'text_transfer_records.json').read_text())
    hist=json.loads((ROOT/'text_transfer_histories.json').read_text())
    result=json.loads((ROOT/'text_transfer_results.json').read_text())
    window=json.loads((ROOT/'text_window_results.json').read_text())
    query=np.array(hist['query_ids']);byseed={h['seed']:h for h in hist['groups']['test']}
    assert len({h['seed'] for hs in hist['groups'].values() for h in hs})==56
    for s in [0,1]:
        for a,b in [('teach','selection'),('teach','test'),('selection','test')]:
            assert set(NAMES[a][s]).isdisjoint(NAMES[b][s])
            assert set(TEMPLATES[a][s]).isdisjoint(TEMPLATES[b][s])
            assert {v for cue in CUES[a][s] for v in cue}.isdisjoint({v for cue in CUES[b][s] for v in cue})
    assert all(rec[i]['pool']=='test' for i in query)
    for H in byseed.values():
        assert sorted(H['phases'][0])==sorted(H['phases'][2])
        assert all(rec[i]['pool']=='teach' for ids in H['phases'] for i in ids)
        for rule in H['rules']:assert sorted(rule)==[-1,-1,1,1]
    checked=0
    for source,summary in [('text_transfer_decisions.json',result),('text_window_decisions.json',window)]:
        decisions=json.loads((ROOT/source).read_text())
        for method,rows in decisions.items():
            metrics={r['seed']:r for r in summary['results'][method]['per_history']}
            for row in rows:
                target=labels(byseed[row['seed']],rec,query,flip0=True)
                assert np.array_equal(target,row['final_targets'])
                assert np.mean(np.array(row['phase_predictions'][-1])==target)==metrics[row['seed']]['final_mean']
                checked+=1
    rows=[]
    for method,v in window['results'].items():
        r=v['dimension'];routes=v['routes'];W=v['W'];cap=W//routes
        rows.append({'method':method,'r':r,'total_window':W,'routes':routes,
          'queue_plaintext_int8_bytes':W*r,'accumulator_plaintext_int32_bytes':4*routes*r,
          'additional_queue_metadata':'per-route head/count; public here; serialization/authentication unpriced',
          'resident_learn_private_add_sub':2*r,'issuer_private_feature_label_products':r,
          'issuer_feature_encoding':'raw-to-feature and rounding at entitled plaintext issuer; origin/feature consistency proof unimplemented',
          'resident_infer_public_feature_products':r,'resident_infer_adds':r-1,
          'resident_infer_private_sign':1,'state_bound':127*cap,'score_bound':r*cap*127**2,
          'private_compute_omissions':'ingress encryption, ciphertext queue storage, commitment/proof, release, freshness, continuity, oblivious access',
          'label':'DERIVED scalar counts; EXECUTED plaintext integer control; no ciphertext latency'})
    with open(ROOT/'text_window_costs.csv','w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
    m=json.loads((ROOT/'text_transfer_model_manifest.json').read_text())
    L=30;d=576;kv=192;ff=1536
    n=max(m['batch_padded_tokens'])
    audit={'passed':True,'decision_history_rows_recomputed':checked,
      'distinct_history_seeds':56,'disjoint_teacher_selection_test_names_templates_cues':True,
      'same_event_multiset_for_skill0_reversal':True,'balanced_rules_checked':True,
      'max_padded_tokens':n,'max_length_scalar_linear_products':L*n*(2*d*d+2*d*kv+3*d*ff),
      'max_length_scalar_attention_products':2*L*n*n*d,
      'text_window_largest_universal_score_bound':577*128*127**2,
      'hashes':{p:sha(ROOT/p) for p in ['TEXT_TRANSFER_PROTOCOL.md','TEXT_WINDOW_PROTOCOL.md',
        'text_transfer_data.py','extract_text_features.py','text_transfer_controls.py','text_window_controls.py',
        'text_transfer_results.json','text_window_results.json','text_window_costs.csv','text_transfer_audit.py']}}
    (ROOT/'text_transfer_audit.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n')
    print(json.dumps(audit,indent=2))

if __name__=='__main__':main()
