#!/usr/bin/env python3
"""Execute only the five frozen public replay pairs, with no reader or retry."""
from pathlib import Path
import datetime
import json
import os
import platform
import re
import signal
import subprocess
import time
from prepare import HERE, metadata, sha


def main():
    frozen_path = HERE / 'freeze.json'
    frozen = json.loads(frozen_path.read_text())
    frozen_hash = sha(frozen_path)
    fixture = json.loads((HERE/'inputs.json').read_text())
    assert len(fixture['cases']) == frozen['host_pairs'] == 5
    report = HERE/'reports/controls'
    artifacts = report/'artifacts'
    report.mkdir(parents=True,exist_ok=False)
    artifacts.mkdir()
    binary = HERE/'target/release/resident-emitted-bool-runtime'
    known = {entry['path']:entry for entry in frozen['files']}
    result = {'schema':'fixed-fft-public-controls-v1','claim':'EXECUTED',
              'freeze_sha256':frozen_hash,'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'platform':{'system':platform.system(),'machine':platform.machine(),'release':platform.release()},
              'operations':[],'pairs':[],'integrity_checks':[],'success':False,'error':None,
              'runtime_environment':frozen['runtime_environment'],'host_concurrency':1,
              'private_reader_invocations':0,'private_key_reads_or_hashes':0,'old_failed_output_files_opened':False,
              'new_chained_trajectory':False,'old_failure_cause_claimed':False,
              'general_determinism_claimed':False,'plaintext_correctness_tested':False,
              'contention':'other root-coordinated work may run concurrently; wall time is a contended sample'}

    def save():
        (report/'results.json').write_text(json.dumps(result,indent=2)+'\n')

    def check_frozen(stage):
        assert sha(frozen_path) == frozen_hash, 'freeze manifest changed'
        for entry in frozen['files']:
            assert metadata(entry['path']) == entry, f'frozen file changed: {entry["path"]}'
        result['integrity_checks'].append({'stage':stage,'public_files_matched':len(frozen['files']),
                                           'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()})
        save()

    def execute(case, role):
        name = f'{case["case"]}.{role}'
        output = artifacts/f'{name}.ct'
        reads = [entry['path'] for entry in case['read_inputs']]
        measured = [str(binary),*reads]
        before = [metadata(path) for path in measured]
        assert all(known[entry['path']] == entry for entry in before), 'public inputs differ from freeze'
        argv = [str(binary),'host',*reads,str(output)]
        resource = report/f'{name}.time.txt'
        prefix = ['/usr/bin/time','-l' if platform.system()=='Darwin' else '-v','-o',str(resource)]
        env = os.environ.copy(); env.update(frozen['runtime_environment'])
        start = time.perf_counter_ns()
        process = subprocess.Popen(prefix+argv,cwd=HERE,env=env,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
        timed_out = False
        try:
            stdout,stderr = process.communicate(timeout=600)
        except subprocess.TimeoutExpired:
            timed_out = True; os.killpg(process.pid,signal.SIGKILL)
            stdout,stderr = process.communicate()
        wall_ns = time.perf_counter_ns()-start
        after = [metadata(path) for path in measured]
        (report/f'{name}.stdout.json').write_bytes(stdout)
        (report/f'{name}.stderr.txt').write_bytes(stderr)
        record = {'name':name,'case':case['case'],'operation':case['operation'],'role':role,
                  'argv':argv,'measurement_prefix':prefix,'wrapper_pid':process.pid,
                  'returncode':process.returncode,'timed_out':timed_out,'wall_ns':wall_ns,
                  'public_inputs_and_binary_before':before,'public_inputs_and_binary_after':after,
                  'public_inputs_and_binary_stable':before==after,'runtime_environment':frozen['runtime_environment']}
        if resource.exists():
            pattern = r'(\d+)\s+maximum resident set size' if platform.system()=='Darwin' else r'Maximum resident set size \(kbytes\):\s*(\d+)'
            match = re.search(pattern,resource.read_text())
            if match: record['peak_rss_bytes'] = int(match[1])*(1 if platform.system()=='Darwin' else 1024)
        if output.exists(): record['output'] = metadata(output)
        if process.returncode == 0: record['reported'] = json.loads(stdout)
        result['operations'].append(record); save()
        print(json.dumps({'completed':name,'returncode':process.returncode,'wall_seconds':wall_ns/1e9}),flush=True)
        assert process.returncode == 0 and not timed_out, f'{name} failed; no retry'
        assert before == after, f'{name} public input/binary changed; no retry'
        assert record['reported']['all_output_bits_encrypted'] is True
        plan = record['reported']['fft_plan_observation']
        assert plan['expected_plan_matched'] is True
        return record

    save()
    try:
        check_frozen('before_controls')
        for case in fixture['cases']:
            first = execute(case,'primary')
            second = execute(case,'replay')
            left,right = Path(first['output']['path']).read_bytes(),Path(second['output']['path']).read_bytes()
            same_inputs = first['public_inputs_and_binary_before'] == second['public_inputs_and_binary_before']
            same_plans = first['reported']['fft_plan_observation'] == second['reported']['fft_plan_observation']
            equal = left == right
            pair = {'case':case['case'],'operation':case['operation'],'complete_serialized_bytes_equal':equal,
                    'same_public_inputs_and_binary':same_inputs,'same_observed_plan':same_plans,
                    'actual_plan':first['reported']['fft_plan_observation'],
                    'primary':first['output'],'replay':second['output'],
                    'separate_wrapper_pids':[first['wrapper_pid'],second['wrapper_pid']]}
            if not equal:
                pair['first_difference_byte'] = next((i for i,(a,b) in enumerate(zip(left,right)) if a!=b),min(len(left),len(right)))
            result['pairs'].append(pair);save()
            assert equal and same_inputs and same_plans, f'{case["case"]} replay control failed; no retry'
        check_frozen('after_controls')
        result['success'] = True
    except Exception as error:
        result['error'] = str(error)
        raise
    finally:
        result['ended_utc'] = datetime.datetime.now(datetime.timezone.utc).isoformat()
        save()


if __name__ == '__main__':
    main()
