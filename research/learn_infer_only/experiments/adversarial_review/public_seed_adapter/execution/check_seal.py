"""Hash final public author seal and compare cost/launch claims to reviewed records."""
from pathlib import Path
from collections import Counter
import csv
import hashlib
import json

HERE = Path(__file__).resolve().parent
ADAPTER = HERE.parents[2] / 'private_construction/designated_span/public_coin_setup/public_seed/adapter'
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
assert sha(ADAPTER/'FINAL_MANIFEST.json') == 'e59b5c1734dd229fd9eaf38084f0efce977f9f49319c7057c067855deeaefff8'
manifest=json.loads((ADAPTER/'FINAL_MANIFEST.json').read_text())
assert len(manifest['files'])==167
names=[]
for item in manifest['files']:
    path=ADAPTER/item['path']
    assert path.resolve().is_relative_to(ADAPTER.resolve()) and '.private' not in path.parts and not path.is_symlink()
    assert path.stat().st_size==item['bytes'] and sha(path)==item['sha256']
    names.append(item['path'])
assert len(set(names))==len(names)
independent=json.loads((HERE/'public_results.json').read_text())
collection=json.loads((ADAPTER/'collection.json').read_text())
mapping={'public_files':'closed_public_files_including_seal','public_bytes':'closed_public_bytes_including_seal',
         'public_command_count':'public_commands','context_sha256':'context_id','transcript_sha256':'transcript_sha256',
         'public_closure_sha256':'public_closure_sha256','accepted_counter_histogram':'accepted_counter_histogram'}
for left,right in mapping.items():assert independent[left]==collection[right]
commands=[json.loads(line) for line in (ADAPTER/'reports/normal_001/public/commands.jsonl').read_text().splitlines()]
native=Counter()
for row in commands:
    if row['command'] is not None:native.update(row['result'].get('counts',{}))
assert dict(native)==collection['reported_native_counts_in_public_phase_logs']
assert native['native_modexp']==99382 and native['subgroup_checks']==41727
launch=json.loads((ADAPTER/'COMMAND.json').read_text())
assert launch['attempts']==1 and launch['retries']==0 and launch['exit_code']==0 and launch['overall_cap_seconds']==1200
assert launch['argv']==['python3','-B',str(ADAPTER/'driver.py'),'--root',str(ADAPTER/'reports/normal_001')]
assert launch['source_manifest_sha256']==manifest['source_manifest_sha256']==independent['source_pins_sha256']
assert Path(launch['stdout_path'])==ADAPTER/'reports/normal_001.stdout.log'
assert Path(launch['stderr_path'])==ADAPTER/'reports/normal_001.stderr.log'
expected={'setup_through_recipient_finalization':101459136291,'public_work_timer_before_sealing':340932174458,
          'public_closure_checkpoint':341002693166,'total_harness':342179553250,'public_processes':112,
          'closed_public_files_including_seal':139,'closed_public_bytes_including_seal':11296482,
          'context':342331,'transcript':724344,'state':148147,'recipient_output':691,'queried_hash_words':577,
          'native_modular_powers_in_public_logs':99382,'subgroup_checks_in_public_logs':41727}
costs=list(csv.DictReader((ADAPTER/'COSTS.csv').open()))
assert len(costs)==len(expected)+1
for row in costs:
    if row['metric']=='single_candidate_failure_bound':
        assert row['value']=='577/2^128' and row['classification']=='DERIVED' and 'ideal independent bits' in row['scope']
    else:
        assert int(row['value'])==expected[row['metric']] and row['classification']=='EXECUTED'
report={'ok':True,'author_final_manifest_sha256':sha(ADAPTER/'FINAL_MANIFEST.json'),'author_files_rehashed':len(names),
        'author_report_sha256':sha(ADAPTER/'REPORT.md'),'collection_sha256':sha(ADAPTER/'collection.json'),
        'launch_record_sha256':sha(ADAPTER/'COMMAND.json'),'cost_rows_checked':len(costs),
        'prelaunch_manifest_unchanged':sha(HERE.parent/'manifest.json')=='e3cdb34f400ea9d67574d91e32f5249cdfc4f40039f6ec2a8d5f1e0016283709',
        'private_paths_in_author_manifest':0,'private_file_reads':0,'crypto_or_sampling_operations':0,
        'scope':'Final author hash/cost/launch record consistency; launch timestamp/exit and private matches retain stated author attribution.'}
(HERE/'seal_results.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
print(json.dumps(report,indent=2,sort_keys=True))
