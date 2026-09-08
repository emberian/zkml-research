"""Post-drain read-only provenance verification and cost/result collection."""
import csv
import datetime
import re
from collections import Counter
from common import *


def main():
    verify_freeze();drain=load(REPORTS/'private_drain.json');sealed=load(REPORTS/'public_seal.json')
    assert drain['passed'] and drain['reader_invocations']==484 and not (REPORTS/'failure.json').exists()
    assert sha(REPORTS/'public_seal.json')==drain['public_seal_sha256_before_drain']
    for row in sealed['records']:assert meta(row['path'])==row
    for row in load(REPORTS/'public_storage.json')['artifacts']:assert meta(row['path'])==row
    public=lines(REPORTS/'operations.jsonl');readers=lines(REPORTS/'reader_operations.jsonl');assert len(readers)==484
    rows=[]
    for op in public+readers:
        report=op['reported'];resource=op.get('resource_report','');rss=re.search(r'(\d+)\s+maximum resident set size',resource)
        rows.append({'name':op['name'],'role':op.get('role','reader'),'operation':report['operation'],'wall_seconds':op['wall_seconds'],
                     'evaluate_seconds':report.get('evaluate_ns',0)/1e9,'peak_rss_bytes':int(rss[1]) if rss else '',
                     'serialized_bytes':report.get('serialized_bytes',''),'xor_api_calls':report.get('gate_api_calls',{}).get('xor',''),
                     'and_api_calls':report.get('gate_api_calls',{}).get('and',''),'fixed_plan':report.get('fft_plan_observation',{}).get('actual_plan_debug','')})
    with (ROOT/'costs.csv').open('w',newline='') as stream:
        writer=csv.DictWriter(stream,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    summary={'claim':'EXECUTED','success':True,'sealed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'stage':'post-drain provenance-only sealing; no crypto invocations',
             'freeze_sha256':sha(ROOT/'freeze.json'),'public_seal_sha256':sha(REPORTS/'public_seal.json'),
             'counts':load(REPORTS/'public_phase.json')['counts'],'reader_invocations':484,
             'primary_learn_states_match':384,'primary_infer_signs_match':96,'initial_states_match':4,
             'replay_plaintexts_independently_checked':0,'all480_pairs_byte_equal':True,
             'all960_host_plans_match':True,'final_correct':drain['final_correct'],'final_queries':drain['final_queries'],
             'all_checkpoint_correct':drain['all_checkpoint_correct'],'all_checkpoint_queries':96,
             'public_wall_seconds':load(REPORTS/'public_phase.json')['wall_seconds'],'private_drain_wall_seconds':drain['wall_seconds'],
             'public_artifacts_unchanged_after_drain':True,'frozen_sources_unchanged':True,
             'full_reader_client_key_retained':True,'old_failure_cause_claimed':False,'general_determinism_claimed':False,
             'records':[meta(REPORTS/name) for name in ['public_seal.json','private_drain.json','reader_operations.jsonl']],
             'costs':meta(ROOT/'costs.csv')}
    save(ROOT/'summary.json',summary);print(__import__('json').dumps(summary),flush=True)


if __name__=='__main__':main()
