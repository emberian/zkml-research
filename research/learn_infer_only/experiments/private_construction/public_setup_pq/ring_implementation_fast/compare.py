#!/usr/bin/env python3
"""Compare two completed public reports; performs no cryptographic work."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
BASE=HERE.parent/'ring_implementation/results/candidate_full_001.json'
FAST=HERE/'results/candidate_full_fast_001.json'


def summary(report):
    run=report['run']; t=run['timings_seconds']; enc=run['encodes']
    return {
      'elapsed_seconds':report['elapsed_seconds'],
      'setup_including_cache_seconds':sum(t.get(k,0) for k in ['sampler_table_build','public_A','recipient_keygen_and_publish','missing_public_rows','recipient_batch_prepare']),
      'recipient_keygen_publish_seconds':t['recipient_keygen_and_publish'],
      'key_sampler_seconds':run['sampler']['33554432']['seconds'],
      'three_error_sampler_seconds':run['sampler']['1024']['seconds'],
      'mean_encode_seconds':sum(e['encode_seconds'] for e in enc)/len(enc),
      'mean_all_recipient_fresh_decode_seconds':sum(e['all_recipient_decode_seconds'] for e in enc)/len(enc),
      'mean_window_update_seconds':sum(e['window_update_seconds'] for e in enc)/len(enc),
      'signed_all_recipient_decode_seconds':t['signed_all_recipient_decode'],
      'peak_rss_bytes':run['peak_process_rss_native'],
      'gaussian_coefficients':sum(v['count'] for v in run['sampler'].values()),
      'matched_reads':sum(e['fresh_recipients_matched']+e['window_recipients_matched'] for e in enc)+run['signed_combination_recipients_matched']}


def main():
    a=json.loads(BASE.read_text()); b=json.loads(FAST.read_text())
    assert a['status']==b['status']=='PASS' and a['source_unchanged'] and b['source_unchanged']
    assert a['run']['parameters']==b['run']['parameters']
    assert a['run']['fresh_inputs_executed']==b['run']['fresh_inputs_executed']==3
    assert a['run']['actual_recipient_rows_generated']==b['run']['actual_recipient_rows_generated']==16
    assert a['run']['absent_recipient_rows_generated']==b['run']['absent_recipient_rows_generated']==0
    x,y=summary(a),summary(b)
    assert x['matched_reads']==y['matched_reads']==112
    assert x['gaussian_coefficients']==y['gaussian_coefficients']==19922944
    ratios={k:x[k]/y[k] for k in x if k.endswith('_seconds')}
    report={'status':'PASS','scope':'Matched synthetic workload, parameters and semantics; independent OS randomness; saved single runs on a shared machine',
            'baseline':x,'successor':y,'baseline_over_successor_time':ratios,
            'rss_successor_over_baseline':y['peak_rss_bytes']/x['peak_rss_bytes'],
            'inputs':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [BASE,FAST]},
            'new_crypto_runs':0}
    (HERE/'results/COMPARISON.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))


if __name__=='__main__':main()
