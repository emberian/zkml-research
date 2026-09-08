#!/usr/bin/env python3
"""Summarize only retained public control records; no new host executions."""
from pathlib import Path
import csv
import json
import statistics
from prepare import HERE, metadata


def main():
    record_path = HERE/'reports/controls/results.json'
    result = json.loads(record_path.read_text())
    assert result['success'] is True and result['error'] is None
    assert len(result['operations']) == 10 and len(result['pairs']) == 5
    rows = []
    for operation in result['operations']:
        report = operation['reported']
        plan = report['fft_plan_observation']
        assert plan['expected_plan_matched'] is True
        rows.append({'case':operation['case'],'operation':operation['operation'],'role':operation['role'],
                     'wall_seconds':operation['wall_ns']/1e9,'evaluate_seconds':report['evaluate_ns']/1e9,
                     'read_seconds':report['read_ns']/1e9,'peak_rss_bytes':operation.get('peak_rss_bytes'),
                     'serialized_bytes':report['serialized_bytes'],'xor_api_calls':report['gate_api_calls']['xor'],
                     'and_api_calls':report['gate_api_calls']['and'],
                     'trivial_encrypt_api_calls':report['gate_api_calls']['trivial_encrypt'],
                     'actual_plan_debug':plan['actual_plan_debug'],'polynomial_size':plan['polynomial_size'],
                     'input_and_binary_hashes_stable':operation['public_inputs_and_binary_stable']})
    with (HERE/'costs.csv').open('w',newline='') as stream:
        writer=csv.DictWriter(stream,fieldnames=list(rows[0]));writer.writeheader();writer.writerows(rows)
    groups = {}
    for operation in ['learn','infer']:
        group=[r for r in rows if r['operation']==operation]
        groups[operation]={'processes':len(group),'wall_seconds_min':min(r['wall_seconds'] for r in group),
                           'wall_seconds_max':max(r['wall_seconds'] for r in group),
                           'wall_seconds_median':statistics.median(r['wall_seconds'] for r in group),
                           'evaluate_seconds_min':min(r['evaluate_seconds'] for r in group),
                           'evaluate_seconds_max':max(r['evaluate_seconds'] for r in group),
                           'peak_rss_bytes_max':max(r['peak_rss_bytes'] for r in group)}
    summary={'claim':'EXECUTED','success':True,'result_file':metadata(record_path),
             'freeze_sha256':result['freeze_sha256'],'pairs':len(result['pairs']),'host_processes':len(rows),
             'all_complete_byte_pairs_equal':all(p['complete_serialized_bytes_equal'] for p in result['pairs']),
             'all_read_input_and_binary_hashes_stable':all(r['input_and_binary_hashes_stable'] for r in rows),
             'all_observed_plans':sorted(set(r['actual_plan_debug'] for r in rows)),
             'all_observed_polynomial_sizes':sorted(set(r['polynomial_size'] for r in rows)),
             'pair_cases':[{'case':p['case'],'operation':p['operation'],'equal':p['complete_serialized_bytes_equal'],
                            'primary_sha256':p['primary']['sha256'],'replay_sha256':p['replay']['sha256']}
                           for p in result['pairs']],
             'cost_groups':groups,'platform':result['platform'],
             'scope':'five static public input tuples, fixed build and observed plan on one recorded platform',
             'private_reader_invocations':0,'old_failed_output_files_opened':False,
             'plaintext_correctness_tested':False,'old_failure_cause_claimed':False,
             'general_determinism_claimed':False,'long_workload_started':False}
    (HERE/'summary.json').write_text(json.dumps(summary,indent=2)+'\n')
    print(json.dumps(summary,indent=2))


if __name__=='__main__':
    main()
