#!/usr/bin/env python3
"""Review only frozen public sources, saved outputs, and successful ciphertext bytes.
No Rust binary or cryptographic operation is executed; no private file is opened.
"""
from pathlib import Path
from collections import Counter
import gzip
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[2]
FORMAL = BASE / 'formal/private_address_ema/emitted_schedule'
RUNTIME = BASE / 'experiments/end_to_end/private_ema/emitted_runtime'
READS = {}

def public_bytes(path):
    path = Path(path)
    assert 'private' not in path.parts, path
    data = path.read_bytes()
    READS[str(path)] = hashlib.sha256(data).hexdigest()
    return data

def obj(path):
    return json.loads(public_bytes(path))

def digest(data):
    return hashlib.sha256(data).hexdigest()

def compact(x):
    return json.dumps(x, separators=(',', ':')).encode()

verification = obj(FORMAL / 'results/verification.json')
for path, sha in verification['inputs'].items():
    assert digest(public_bytes(path)) == sha
lean = public_bytes(FORMAL / 'Compiler/PrivateAddressEmaSchedule.lean').decode()
theorems = re.findall(r'^theorem\s+(\w+)', lean, re.M)
pins = re.findall(r'^#guard_msgs[^\n]*#print axioms Minidregg\.Compiler\.PrivateAddressEmaSchedule\.(\w+)', lean, re.M)
assert len(theorems) == 46 and theorems == pins
assert not re.search(r'^\s*(?:axiom|opaque)\s|\bsorry\b|\bnative_decide\b', lean, re.M)

# Structural validation of the exact physical JSON, including sparse numbering.
inventory = {}
for operation, dims in [('learn', (42, 32)), ('infer', (34, 1))]:
    path = FORMAL / f'artifacts/{operation}.json'
    raw = public_bytes(path)
    d = json.loads(raw)
    assert set(d) == {'schema', 'operation', 'nInputs', 'nWires', 'gates', 'outputs'}
    assert d['schema'] == 'private-address-ema-bool-schedule-v1' and d['operation'] == operation
    assert (d['nInputs'], len(d['outputs'])) == dims
    initialized = set(range(d['nInputs']))
    previous = d['nInputs'] - 1
    def valid_ref(ref):
        assert isinstance(ref, dict)
        if set(ref) == {'w'}:
            assert type(ref['w']) is int and 0 <= ref['w'] < d['nWires']
            assert ref['w'] in initialized
        else:
            assert set(ref) == {'c'} and type(ref['c']) is bool
    for g in d['gates']:
        assert set(g) == {'op', 'a', 'b', 'out'} and g['op'] in ['xor', 'and']
        assert type(g['out']) is int and previous < g['out'] < d['nWires']
        assert g['out'] not in initialized
        valid_ref(g['a']); valid_ref(g['b'])
        initialized.add(g['out']); previous = g['out']
    for ref in d['outputs']: valid_ref(ref)
    counts = Counter(g['op'] for g in d['gates'])
    inventory[operation] = {'sha256': digest(raw), 'bytes': len(raw), 'nInputs': d['nInputs'],
        'nWires': d['nWires'], 'nGates': len(d['gates']), 'nOutputs': len(d['outputs']),
        'xor': counts['xor'], 'and': counts['and'],
        'unusedWireSlots': d['nWires'] - len(initialized),
        'output_references': d['outputs'], 'all_outputs_are_wire_references': all('w' in r for r in d['outputs'])}

# Reconstruct the public fixture order and independent floor oracle; inspect saved stdout only.
plain_summary = obj(RUNTIME / 'reports/plain/summary.json')
for path, sha in plain_summary['source_pins'].items(): assert digest(public_bytes(path)) == sha
transitions = obj(RUNTIME.parent / 'utility/transitions.json')
inputs = {'learn': [], 'infer': []}
expected = {'learn': [], 'infer': []}

def word_bits(x, width):
    return [bool((x % (1 << width)) & (1 << i)) for i in range(width)]

def state_bits(state):
    return [bit for value in state for bit in word_bits(value, 8)]

def append_update(state, address, label):
    nxt = [value if j != address else divmod(7 * value + label, 8)[0]
           for j, value in enumerate(state)]
    inputs['learn'].append(state_bits(state) + word_bits(address, 2) + word_bits(label, 8))
    expected['learn'].append(state_bits(nxt))
    return nxt

for row in transitions:
    route = row['route']
    after = append_update(row['state_before'][route], row['bin'], row['u'])
    assert after == row['state_after'][route]
    for address in range(4):
        inputs['infer'].append(state_bits(after) + word_bits(address, 2))
        expected['infer'].append([after[address] < 0])
for selected in range(-128, 128):
    for address in range(4):
        state = [(selected + 73 * j + 128) % 256 - 128 for j in range(4)]
        state[address] = selected
        for label in [-120, 120]: append_update(state, address, label)
for selected in [-128, -127, -121, -120, -1, 0, 1, 119, 120, 126, 127]:
    for address in range(4):
        state = [(selected + 73 * j + 128) % 256 - 128 for j in range(4)]
        state[address] = selected
        for label in range(-128, 128): append_update(state, address, label)

saved_plain = {}
for operation in ['learn', 'infer']:
    recorded = plain_summary['results'][operation]
    payload = compact(inputs[operation]) + b'\n'
    assert digest(payload) == recorded['input_sha256'] and len(payload) == recorded['input_bytes']
    assert digest(compact(expected[operation])) == recorded['expected_sha256']
    metadata = obj(RUNTIME / f'reports/plain/{operation}.command.json')
    stdout = gzip.decompress(public_bytes(RUNTIME / f'reports/plain/{operation}.stdout.json.gz'))
    assert len(stdout) == metadata['stdout_bytes'] and digest(stdout) == metadata['stdout_sha256']
    assert metadata['returncode'] == 0 and metadata['argv'][1] == 'clear'
    assert public_bytes(RUNTIME / f'reports/plain/{operation}.stderr.txt') == b''
    actual = json.loads(stdout)['outputs']
    assert len(actual) == len(expected[operation]) == recorded['rows']
    assert actual == expected[operation]
    assert all(len(row) == recorded['output_bits_per_row'] and all(type(b) is bool for b in row) for row in actual)
    saved_plain[operation] = {'rows': len(actual), 'saved_outputs_match_reconstructed_oracle': True,
        'reconstructed_input_sha256': digest(payload), 'saved_stdout_sha256': digest(stdout),
        'true_output_bits': sum(sum(row) for row in actual)}
    validation_meta = obj(RUNTIME / f'reports/plain/validate_{operation}.command.json')
    validation_raw = gzip.decompress(public_bytes(RUNTIME / f'reports/plain/validate_{operation}.stdout.json.gz'))
    assert digest(validation_raw) == validation_meta['stdout_sha256'] and validation_meta['returncode'] == 0
    validation = json.loads(validation_raw)
    assert validation == plain_summary['validation'][operation]
    for k in ['nInputs', 'nWires', 'nGates', 'nOutputs', 'xor', 'and', 'unusedWireSlots']:
        assert validation['schedule'][k] == inventory[operation][k]

# Recheck only the successful, public smoke bytes. Private audit booleans remain reported.
freeze_raw = public_bytes(RUNTIME / 'freeze.json')
freeze = json.loads(freeze_raw)
for entry in freeze['files']:
    data = public_bytes(entry['path'])
    assert len(data) == entry['bytes'] and digest(data) == entry['sha256']
smoke = obj(RUNTIME / 'reports/smoke/results.json')
summary = obj(RUNTIME / 'summary.json')
assert digest(freeze_raw) == smoke['freeze_sha256'] == summary['freeze_sha256']
assert smoke['success'] and smoke['error'] is None
names = [r['name'] for r in smoke['operations']]
assert names == ['learn_001', 'learn_001_replay', 'infer_001', 'infer_001_replay',
    'learn_002', 'learn_002_replay', 'infer_002', 'infer_002_replay',
    'reader_state_001', 'reader_output_001', 'reader_state_002', 'reader_output_002']
operations = {r['name']: r for r in smoke['operations']}
for name in names[:8]:
    r = operations[name]
    assert r['returncode'] == 0 and not r['timed_out']
    actual = obj(RUNTIME / f'reports/smoke/{name}.stdout.json')
    assert actual == r['reported']
    assert public_bytes(RUNTIME / f'reports/smoke/{name}.stderr.txt') == b''
    op = actual['operation']
    assert actual['gate_api_calls'] == {'xor':inventory[op]['xor'],'and':inventory[op]['and'],'trivial_encrypt':2}
    assert actual['all_output_bits_encrypted'] and actual['output_bits'] == inventory[op]['nOutputs']
    assert r['argv'][1] == 'host'
    assert digest(public_bytes(r['argv'][2])) == inventory[op]['sha256']
pairs=[]
for pair in smoke['replays']:
    op, step = pair['operation'], pair['step']
    first, replay = operations[f'{op}_{step}'], operations[f'{op}_{step}_replay']
    assert first['argv'][1:-1] == replay['argv'][1:-1]
    assert first['wrapper_pid'] != replay['wrapper_pid']
    assert pair['separate_wrapper_pids'] == [first['wrapper_pid'],replay['wrapper_pid']]
    assert pair['complete_serialized_bytes_equal'] and pair['input_hashes_unchanged_after_pair']
    data=[]
    for prefix in ['first', 'replay']:
        archived = RUNTIME / 'reports/smoke/artifacts' / Path(pair[f'{prefix}_path']).name
        value = public_bytes(archived)
        assert len(value) == pair['bytes'] and digest(value) == pair[f'{prefix}_sha256']
        data.append(value)
    assert data[0] == data[1]
    for path, sha in pair['input_hashes'].items(): assert digest(public_bytes(path)) == sha
    pairs.append({'operation':op,'step':step,'archived_complete_bytes_equal':True,'bytes':len(data[0])})
assert len(pairs)==4 and Counter(p['operation'] for p in pairs)=={'learn':2,'infer':2}
assert smoke['public_execution_complete_before_private_audit'] and smoke['all_public_result_hashes_rechecked_before_private_audit']
assert smoke['public_hash_checks'][-1]['stage']=='after_private_audit'
assert len(smoke['private_audits'])==2 and smoke['private_audits']==summary['private_oracle_audits']

result={'decision':'accept scoped frozen proof/runtime correspondence; no concrete mismatch found',
    'formal_theorems':len(theorems),'formal_pins':len(pins),
    'inventory':inventory,'saved_plain_comparison':saved_plain,'smoke_public_pairs':pairs,
    'public_freeze_files_rechecked':len(freeze['files']),
    'private_oracle_results':'Reported by saved author record only; no private audit opened',
    'ordering_deviation':'Final after_private_audit integrity recheck retained, beyond literal all-checks-before wording',
    'runtime_or_crypto_reruns':0,'private_files_opened':0,
    'general_ciphertext_determinism_established':False,
    'older_fourteenth_learn_failure':'Retained separate root-reported failure; no failed outputs inspected',
    'public_source_and_artifact_hashes':READS,
    'queries':{'web':0,'scry_sql':0,'scry_schema':0,'kagi':0},'all_checks_passed':True}
(HERE/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='public_source_and_artifact_hashes'},indent=2))
