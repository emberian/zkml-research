"""Independent standard-library public provenance/byte/integer audit. No crypto.

Only explicit package/freeze/source-evidence files and current public ciphertexts
are read. Private argv strings are inspected as strings, never followed.
"""
import collections
import csv
import datetime
import hashlib
import json
import re
import statistics
from pathlib import Path

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
BASE = REPO / 'research/learn_infer_only/experiments/end_to_end/private_ema'
AUTHOR = BASE / 'emitted_long_run'
REPORTS = AUTHOR / 'reports/run001'
PUBLIC = AUTHOR / 'runtime/run001/public'
EXPECTED = {
    'PACKAGE.json': '0a9a15b6ca0784b3f6de03df83b77873469ef26f59164a5663882fe2065b6ba4',
    'REPORT.md': '0bfcfc46d5d469d4b113c1179f0147664207a0e3c5b511c4c87e98344d8e934a',
    'freeze.json': '6cc20a07b75330c2fb7aaa19a2021c6b495096c6b477b1554eb4a2a14c7943e8',
    'summary.json': '581d4d9fd602f63658bd3ad46feea58845f1d021863af812bf4bec2147686e5a',
    'collection.json': 'e536a7027fd89bf849d86edda20fd72cd8396e1dc69cdc737cea17f455a3e16f',
    'reports/run001/public_seal.json': 'b2f972552b5383d05207737939ddb2fe81e0c9ff68077104e13939f786dee566',
}
cache = {}
pins = {}

def read(path):
    p = Path(path).resolve()
    assert 'private' not in p.parts, 'private path forbidden'
    assert 'client_key.bin' != p.name, 'private key forbidden'
    if 'runtime' in p.parts:
        assert p.parent == PUBLIC, 'only this completed run public runtime is permitted'
    if p not in cache:
        cache[p] = p.read_bytes()
        pins[str(p)] = {'path': str(p), 'bytes': len(cache[p]), 'sha256': hashlib.sha256(cache[p]).hexdigest()}
    return cache[p]

def meta(path):
    read(path)
    return pins[str(Path(path).resolve())]

def check_meta(row):
    got = meta(row['path'])
    assert all(got[k] == row[k] for k in ['path', 'bytes', 'sha256']), row['path']
    return got

def load(path):
    return json.loads(read(path))

def lines(path):
    return [json.loads(x) for x in read(path).splitlines()]

def time(value):
    return datetime.datetime.fromisoformat(value)

for name, digest in EXPECTED.items():
    assert meta(AUTHOR/name)['sha256'] == digest, name
package = load(AUTHOR/'PACKAGE.json')
assert package['file_count'] == len(package['files']) == 49
for row in package['files']:
    assert Path(row['path']) == AUTHOR/row['relative_path']
    assert 'runtime' not in Path(row['relative_path']).parts
    check_meta(row)
assert sum(x['bytes'] for x in package['files']) == package['total_bytes'] == 10616637
freeze = load(AUTHOR/'freeze.json')
assert len(freeze['files']) == 39
for path, row in freeze['files'].items():
    assert path == row['path']
    check_meta(row)
build = load(BASE/'emitted_fixed_fft/build_pins.json')
assert build['compiler_tfhe_artifact']['features'] == ['boolean', 'experimental-force_fft_algo_dif4']
for row in build['source_evidence']:
    check_meta(row)
assert len(build['source_evidence']) == 4
check_meta(build['binary'])

phase = load(REPORTS/'public_phase.json')
seal = load(REPORTS/'public_seal.json')
verification = load(REPORTS/'public_verification.json')
storage = load(REPORTS/'public_storage.json')
drain = load(REPORTS/'private_drain.json') # Public aggregate only.
summary = load(AUTHOR/'summary.json')
collection = load(AUTHOR/'collection.json')
pipeline = load(AUTHOR/'pipeline.json')
for row in list(phase['transcripts'].values()) + seal['records'] + summary['records'] + [summary['costs']]:
    check_meta(row)
for obj in [phase, seal, summary]:
    assert obj['freeze_sha256'] == EXPECTED['freeze.json']
assert summary['public_seal_sha256'] == drain['public_seal_sha256_before_drain'] == EXPECTED['reports/run001/public_seal.json']
assert verification['public_phase_sha256'] == meta(REPORTS/'public_phase.json')['sha256']
assert phase['completed'] and seal['public_complete_and_verified'] and verification['passed'] and summary['success']
assert phase['reader_invocations'] == seal['reader_invocations'] == verification['reader_invocations'] == 0
assert not (REPORTS/'failure.json').exists()

artifacts = {x['path']: check_meta(x) for x in storage['artifacts']}
assert len(artifacts) == storage['artifact_count'] == 1364
assert set(artifacts) == {str(p) for p in PUBLIC.iterdir()}
assert sum(x['bytes'] for x in artifacts.values()) == 97500084
envelopes = {}
for path in artifacts:
    data = read(path)
    assert data[:8] == b'PEMA0001'
    assert int.from_bytes(data[9:17], 'little') == len(data)-17
    kind, bits = data[8], int.from_bytes(data[17:25], 'little')
    assert (kind, bits) in [(1,32),(2,10),(3,2),(4,1)]
    envelopes[path] = (kind, bits)

ops = lines(REPORTS/'operations.jsonl')
events = lines(REPORTS/'events.jsonl')
pairs = lines(REPORTS/'replays.jsonl')
readers = lines(REPORTS/'reader_operations.jsonl')
assert (len(ops),len(events),len(pairs),len(readers)) == (1364,480,480,484)
HOST = str(BASE/'emitted_fixed_fft/target/release/resident-emitted-bool-runtime')
ISSUER = str(BASE/'target/release/issuer')
READER = str(BASE/'target/release/reader')
PK = str(BASE/'runs/run_001/public/keys/public_key.bin')
SK = str(BASE/'runs/run_001/public/keys/server_key.bin')
FORMAL = REPO/'research/learn_infer_only/formal/private_address_ema/emitted_schedule/artifacts'
PLAN = 'Plan { base_algo: Dif4, base_size: 512, fft_size: 512 }'
roles = collections.Counter()
gates = collections.Counter()
seen_outputs = set()
for index, op in enumerate(ops):
    assert op['index'] == index and op['returncode'] == 0 and op['timed_out'] is False
    assert json.loads(op['stdout']) == op['reported'] and op['stderr'] == ''
    assert op['runtime_environment'] == {'RAYON_NUM_THREADS':'1'}
    assert op['binary_before'] == op['binary_after'] == meta(op['command'][0])
    assert op['public_inputs_before'] == op['public_inputs_after']
    for row in op['public_inputs_before']: check_meta(row)
    check_meta(op['output'])
    assert op['output']['path'] not in seen_outputs
    seen_outputs.add(op['output']['path'])
    cmd, report = op['command'], op['reported']
    role, operation = op['role'], report['operation']
    roles[role,operation] += 1
    assert cmd[-1] == op['output']['path']
    if role == 'host':
        assert len(cmd) == 7 and cmd[:2] == [HOST,'host']
        assert cmd[2] == str(FORMAL/f'{operation}.json') and cmd[3] == SK
        assert [x['path'] for x in op['public_inputs_before']] == cmd[2:6]
        assert all('private' not in Path(x).parts for x in cmd)
        observed = report['fft_plan_observation']
        assert observed['actual_plan_debug'] == PLAN and observed['expected_plan_matched']
        assert (observed['polynomial_size'],observed['fourier_size']) == (1024,512)
        assert observed['source_feature'] == 'experimental-force_fft_algo_dif4'
        assert report['all_output_bits_encrypted'] and report['client_key_read'] is False
        assert report['bootstrap_count_instrumented'] is False
        expected = {'xor':342,'and':196,'trivial_encrypt':2} if operation == 'learn' else {'xor':6,'and':3,'trivial_encrypt':2}
        assert report['gate_api_calls'] == expected
        gates.update(expected)
        assert envelopes[cmd[-1]] == ((1,32) if operation == 'learn' else (4,1))
    else:
        assert role == 'issuer' and len(cmd) == 5 and cmd[:3] == [ISSUER,operation,PK]
        assert [x['path'] for x in op['public_inputs_before']] == [PK]
        assert envelopes[cmd[-1]] == {'init':(1,32),'learn':(2,10),'query':(3,2)}[operation]
    assert report['serialized_bytes'] == op['output']['bytes']
assert roles == {('host','learn'):768,('host','infer'):192,('issuer','init'):4,('issuer','learn'):384,('issuer','query'):16}
assert seen_outputs == set(artifacts)
assert gates == {'xor':263808,'and':151104,'trivial_encrypt':1920}

fixture = load(BASE/'utility/materialized_fixture.json')
assert fixture['counts'] == {'Learn':384,'Infer':96,'expiry':0}
descriptors = {op:load(FORMAL/f'{op}.json') for op in ['learn','infer']}
def word_bits(word,width):
    return [bool((word >> i)&1) for i in range(width)]
def clear_descriptor(operation,selected,address,u=None):
    # Public fixture integers only; no encrypted values are decoded here.
    d=descriptors[operation]
    inputs=[bit for word in selected for bit in word_bits(word,8)]+word_bits(address,2)
    if operation=='learn': inputs+=word_bits(u,8)
    assert d['operation']==operation and d['schema']=='private-address-ema-bool-schedule-v1'
    assert len(inputs)==d['nInputs'] and len(d['outputs'])==(32 if operation=='learn' else 1)
    wires=dict(enumerate(inputs));last=d['nInputs']-1
    def ref(r):
        assert set(r) in [{'w'},{'c'}]
        return wires[r['w']] if 'w' in r else r['c']
    for g in d['gates']:
        assert last<g['out']<d['nWires'] and g['op'] in ['xor','and']
        a,b=ref(g['a']),ref(g['b'])
        wires[g['out']]=(a^b) if g['op']=='xor' else (a and b)
        last=g['out']
    return [ref(r) for r in d['outputs']]
initials = {(x['history_id'],str(x['route'])):x['state'] for x in phase['initials']}
assert set(initials) == {(hid,str(route)) for hid in [67000,67001] for route in [0,1]}
query_uses = collections.Counter()
history_counts = collections.defaultdict(collections.Counter)
states = {hid:[[0]*4 for _ in range(2)] for hid in [67000,67001]}
parents = {}
current_history = None
all_correct = final_correct = 0
checkpoints = []
used_host_indices = []
for event, pair, expected in zip(events,pairs,fixture['events'],strict=True):
    for key in ['event_id','event_ordinal','history_id','history_index','kind','learn_step','phase','route','record_id']:
        assert event[key] == expected[key], (expected['event_id'],key)
    hid, route, address = expected['history_id'], str(expected['route']), expected['bin']
    learn = expected['kind'] == 'Learn'
    assert address in range(4) and route in ['0','1']
    history_counts[hid][expected['kind']] += 1
    if hid != current_history:
        parents = {r:initials[hid,r] for r in ['0','1']}; current_history = hid
    assert event['parents_before'] == parents
    assert pair['event_id'] == event['event_id'] and pair['kind'] == expected['kind']
    left, right = (ops[pair[k]] for k in ['primary_operation','replay_operation'])
    used_host_indices.extend([pair['primary_operation'],pair['replay_operation']])
    assert pair['replay_operation'] == pair['primary_operation']+1
    assert left['name'] == event['event_id']+'.primary' and right['name'] == event['event_id']+'.replay'
    assert left['command'][:-1] == right['command'][:-1]
    assert left['public_inputs_before'] == right['public_inputs_before']
    assert left['wrapper_pid'] == pair['primary_process'] != pair['replay_process'] == right['wrapper_pid']
    assert all(pair[k] for k in ['complete_output_bytes_equal','inputs_equal_across_invocations','same_observed_plan'])
    assert left['command'][4] == parents[route]['path']
    assert pair['primary'] == left['output'] == event['output']
    assert pair['replay'] == right['output']
    assert read(pair['primary']['path']) == read(pair['replay']['path'])
    request = meta(PUBLIC/f'{event["event_id"]}.input.ct') if learn else phase['query_artifacts'][str(expected['record_id'])]
    assert event['request'] == request and left['command'][5] == request['path']
    if learn:
        assert expected['u'] in [-120,120]
        state = states[hid][int(route)]
        out=clear_descriptor('learn',state,address,expected['u'])
        encoded=[sum(int(bit)<<i for i,bit in enumerate(out[j:j+8])) for j in range(0,32,8)]
        clear_result=[x-256 if x>=128 else x for x in encoded]
        state[address] = (7*state[address]+expected['u'])//8
        assert clear_result==state
        assert states[hid] == expected['state_after']
        parents[route] = event['output']
        if expected['learn_step'] in [64,128,192]:
            checkpoints.append({'history_id':hid,'phase':expected['phase'],'states':dict(parents)})
    else:
        query_uses[expected['record_id']] += 1
        score = states[hid][int(route)][address]
        assert clear_descriptor('infer',states[hid][int(route)],address)==[score<0]
        assert score == expected['ema_score'] and expected['ema_prediction'] == (-1 if score<0 else 1)
        correct = expected['ema_prediction'] == expected['target']
        all_correct += correct
        if expected['phase'] == 3: final_correct += correct
    assert event['parents_after'] == parents
assert checkpoints == phase['checkpoints']
assert set(used_host_indices) == {x['index'] for x in ops if x['role']=='host'} and len(set(used_host_indices)) == 960
assert all(x == {'Learn':192,'Infer':48} for x in history_counts.values())
assert len(query_uses) == 16 and set(query_uses.values()) == {6}
assert (all_correct,final_correct) == (76,28)
assert fixture['final']['ema']['correct'] == fixture['final']['window']['correct'] == 28

expected_opens = [(f'initial_{x["history_id"]}_{x["route"]}','state',x['state']) for x in phase['initials']]
expected_opens += [(e['event_id'],'state' if e['kind']=='Learn' else 'output',e['output']) for e in events]
for op, (name,kind,ct) in zip(readers,expected_opens,strict=True):
    assert op['name']==name and op['ciphertext']==ct
    assert op['returncode']==0 and op['timed_out'] is False and op['stderr']==''
    assert json.loads(op['stdout'])==op['reported']
    cmd = op['command']
    assert len(cmd)==5 and cmd[:2]==[READER,kind] and cmd[3]==ct['path']
    # Private paths inspected as strings only; no stat/hash/read performed.
    assert cmd[2] == str(BASE/'runs/run_001/private/reader/client_key.bin')
    assert cmd[4] == str(AUTHOR/f'runtime/run001/private/audit/{name}.json')
    assert op['reported']['decrypted_bits']==(32 if kind=='state' else 1)
    assert op['reported']['plaintext_report_private'] and op['reported']['read_all_client_key_retained']
assert drain['passed'] and drain['all_match'] and drain['reader_invocations']==484
assert drain['independent_replay_plaintext_checks']==0
assert all(x['matches'] for x in drain['initial_checks']) and len(drain['initial_checks'])==4
assert drain['event_checks'] == [{'event_id':e['event_id'],'kind':e['kind'],'primary_only':True,'matches_frozen_oracle':True} for e in events]

times = [phase['closed_utc'], verification['verified_utc'], seal['sealed_utc'], drain['started_utc'], drain['finished_utc'], summary['sealed_utc']]
assert all(time(a)<time(b) for a,b in zip(times,times[1:]))
stages = pipeline['stages']
assert pipeline['completed'] and [s['stage'] for s in stages] == ['run_public','verify_public','drain','seal']
for stage in stages:
    assert stage['returncode']==0 and time(stage['started_utc'])<time(stage['ended_utc'])
    assert stage['argv'][1]==str(AUTHOR/(stage['stage']+'.py'))
for left,right in zip(stages,stages[1:]): assert time(left['ended_utc'])<time(right['started_utc'])
for i, stamp in [(0,phase['closed_utc']),(1,seal['sealed_utc']),(2,drain['started_utc']),(2,drain['finished_utc']),(3,summary['sealed_utc'])]:
    assert time(stages[i]['started_utc'])<time(stamp)<time(stages[i]['ended_utc'])
started = load(REPORTS/'started.json')
assert time(started['cutoff_utc']) == min(time(started['started_utc'])+datetime.timedelta(hours=6),datetime.datetime(2026,9,8,15,tzinfo=datetime.timezone.utc))
assert time(summary['sealed_utc'])<time(started['cutoff_utc'])
progress = load(REPORTS/'progress.json')
assert progress['phase']=='public_closed' and progress['public_phase_closed'] is False and progress['reader_invocations']==0
assert (progress['completed_events'],progress['complete_replay_pairs'],progress['operations']) == (480,480,1364)

csv_rows = list(csv.DictReader(read(AUTHOR/'costs.csv').decode().splitlines()))
assert len(csv_rows)==1848
groups = collections.defaultdict(list)
for row,op in zip(csv_rows,ops+readers,strict=True):
    r=op['reported'];rss=re.search(r'(\d+)\s+maximum resident set size',op.get('resource_report',''))
    expected={'name':op['name'],'role':op.get('role','reader'),'operation':r['operation'],'wall_seconds':op['wall_seconds'],
      'evaluate_seconds':r.get('evaluate_ns',0)/1e9,'peak_rss_bytes':int(rss[1]) if rss else '',
      'serialized_bytes':r.get('serialized_bytes',''),'xor_api_calls':r.get('gate_api_calls',{}).get('xor',''),
      'and_api_calls':r.get('gate_api_calls',{}).get('and',''),'fixed_plan':r.get('fft_plan_observation',{}).get('actual_plan_debug','')}
    assert row == {k:str(v) for k,v in expected.items()}
    groups[expected['role'],expected['operation']].append(expected)
rebuilt=[]
for (role,operation),rows in sorted(groups.items()):
    walls=[x['wall_seconds'] for x in rows];rss=[x['peak_rss_bytes'] for x in rows if x['peak_rss_bytes']!='']
    rebuilt.append({'role':role,'operation':operation,'processes':len(rows),'wall_seconds_min':min(walls),
      'wall_seconds_median':statistics.median(walls),'wall_seconds_max':max(walls),'wall_seconds_sum':sum(walls),
      'maximum_recorded_rss_bytes':max(rss) if rss else None})
assert rebuilt == collection['cost_groups']

# Rehash every read input after all checks; no recursive metadata links followed.
for path,row in pins.items():
    p=Path(path);data=p.read_bytes()
    assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256'], path
result={'claim':'EXECUTED independent public-only audit','success':True,'checked_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'package_files':49,'original_frozen_files':39,'cached_primary_source_files':4,'input_files_rehashed':len(pins),
 'public_ciphertexts':len(artifacts),'public_ciphertext_bytes':97500084,'complete_byte_pairs_recompared':480,
 'host_invocations':960,'issuer_invocations':404,'fixture_events':480,'fixture_integer_transitions_recomputed':384,
 'public_descriptor_clear_evaluations':480,
 'public_reader_records_checked':484,'private_plaintext_matches':'REPORTED by original drain; source and public index bindings checked only',
 'private_files_read_or_hashed':0,'new_crypto_invocations':0,'old_failed_runtime_files_read':0,'new_lean_builds':0,
 'cost_rows_rebuilt':1848,'gate_api_calls':dict(gates),'phase_times_utc':times,'cost_groups':rebuilt,
 'oracle_target_agreement':{'all_checkpoints':[76,96],'final_subset':[28,32]},
 'preserved_progress_reporting_inconsistency':{'phase':progress['phase'],'public_phase_closed':False,'reader_invocations':0},
 'author_files_unchanged':True,'inputs':list(pins.values())}
(HERE/'results.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
print(json.dumps({k:v for k,v in result.items() if k not in ['inputs','cost_groups']},indent=2,sort_keys=True))
