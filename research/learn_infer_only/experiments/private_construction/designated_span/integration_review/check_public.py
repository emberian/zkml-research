"""Independent normal public-evidence/provenance audit. No runtime/crypto imports.

Read only the explicitly frozen integration packet, its public source originals,
and the public native dependency. Never follow a logged private/runtime path.
"""
from pathlib import Path
from collections import Counter, defaultdict
import ast
import copy
import hashlib
import json

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent / 'integration'
E = ROOT / 'evidence/normal_001'


def canonical(x):
    return json.dumps(x, sort_keys=True, separators=(',', ':'), ensure_ascii=True,
                      allow_nan=False).encode()


def sha(x):
    return hashlib.sha256(x).hexdigest()


def digest(x):
    return sha(canonical(x))


def load(path):
    return json.loads(path.read_bytes())


def rows(name):
    return [json.loads(x) for x in (E / name).read_text().splitlines() if x.strip()]


package = load(ROOT / 'EVIDENCE_MANIFEST.json')
assert sha((ROOT / 'EVIDENCE_MANIFEST.json').read_bytes()) == '36d8fdb7ef23e73e48ba2fb6d6d0f498fe999b933cf0aa76a5e3ea1f2109c6c5'
inventory = {}
for name, expected in package['files'].items():
    assert not {'.private', 'runtime'}.intersection(Path(name).parts)
    path = ROOT / name
    actual = {'sha256': sha(path.read_bytes()), 'bytes': path.stat().st_size}
    assert actual == expected, name
    inventory[name] = actual
manifest = load(E / 'MANIFEST.json')
for name, expected in manifest['files_sha256'].items():
    assert not {'.private', 'runtime'}.intersection(Path(name).parts)
    assert sha((E / name).read_bytes()) == expected, name
for name, expected in manifest['source_sha256'].items():
    assert name.startswith('source/') and '.private' not in Path(name).parts
    assert sha((ROOT / name).read_bytes()) == expected, name

protocol = HERE.parent / 'PROTOCOL_PRIVACY.md'
assert sha(protocol.read_bytes()) == 'aa7b096e5ff44b4c72ef72f005a363897e06a8fb94d0351bfa15856f3564fec0'
g = load(E / 'genesis.json')
report, replay, costs = [load(E / n) for n in ['report.json', 'replay.json', 'PUBLIC_COSTS.json']]
assert digest(g) == report['genesis'] == replay['genesis']
for name, expected in g['journal_sources'].items():
    assert sha((ROOT / 'source/journal' / name).read_bytes()) == expected
assert len(g['journal_sources']) == 8
for name, expected in g['crypto_sources'].items():
    assert sha((ROOT / 'source/crypto' / name).read_bytes()) == expected
assert len(g['crypto_sources']) == 4
old = load(ROOT / 'SOURCE_FREEZE.json')
for name, expected in old['copied_files_sha256'].items():
    path = Path(name)
    assert sha(path.read_bytes()) == expected
    copy_path = ROOT / 'source_original' / path.parent.name / path.name
    assert sha(copy_path.read_bytes()) == expected
crypto_freeze = load(ROOT / 'CRYPTO_FREEZE.json')
for name, expected in crypto_freeze['files_sha256'].items():
    assert sha((Path(crypto_freeze['source_directory']) / name).read_bytes()) == expected
native = g['native_dependency']
assert sha(Path(native['path']).read_bytes()) == native['sha256']

context_raw = (E / 'public_context.json').read_bytes()
context = json.loads(context_raw)
assert canonical(context) == context_raw
assert sha(context_raw) == g['context_id'] == g['key_id'] == g['public_key_sha256']
validation = load(E / 'context_validation.json')
assert sha((E / 'context_validation.json').read_bytes()) == g['context_validation_sha256']
assert validation['validated'] and validation['context_id'] == g['context_id']
assert validation['source_sha256'] == g['crypto_sources']
param_body = {k: v for k, v in g['crypto'].items()
              if k not in {'params_id', 'program_id', 'counts', 'process_work_ns'}}
assert digest(param_body) == g['crypto']['params_id'] == context['params_id']
assert digest({'semantics': param_body['program_semantics'],
               'params_id': g['crypto']['params_id']}) == g['crypto']['program_id']
assert param_body['state_bytes'] == 179 + 578 * 256 == 148147
assert param_body['output_bytes'] == 179 + 2 * 256 == 691
assert param_body['recipient_key_bytes'] == 179 + 256 == 435
ys = load(ROOT / 'source/crypto/rows.json')
assert ys == context['rows'] and len(ys) == 16
assert g['crypto']['row_signed_score_bounds'] == [32 * 127 * sum(map(abs, y)) for y in ys]
assert len(set(map(digest, ys))) == 16
assert all(len(y) == 577 and all(type(v) is int and -127 <= v <= 127 for v in y) for y in ys)
assert int(param_body['q_hex'], 16) > 2 * max(param_body['row_signed_score_bounds'])
assert context['setup_id'] == digest({'schema': 'resident-designated-bootstrap-v1',
    'params_id': g['crypto']['params_id'], 'rows': ys, 'h': context['h']})
for i, r in enumerate(context['recipients']):
    assert r['recipient_id'] == digest({'domain': 'dedicated-designated-recipient-v1',
        'setup_id': context['setup_id'], 'row_id': i, 'row_sha256': digest(ys[i]), 'A': r['A']})
    assert r['token_sha256'] == digest({k: v for k, v in r.items() if k != 'token_sha256'})
queries = {}
for i, path in enumerate(sorted((E / 'queries').glob('*.json'))):
    raw = path.read_bytes(); query = json.loads(raw)
    assert canonical(query) == raw
    h = sha(raw); queries[h] = query
    r = context['recipients'][i]
    assert query['row_id'] == i and query['coefficients'] == ys[i]
    assert query['context_id'] == g['context_id']
    assert query['row_sha256'] == digest(ys[i])
    for k in ['row_id', 'row_sha256', 'recipient_id', 'token_sha256']:
        assert query[k] == r[k]
    assert {k: query[k] for k in g['query_bindings'][h]} == g['query_bindings'][h]
    assert {'query_ct': h, 'route': 0} in g['query_policy']
assert len(queries) == 16

events = rows('events.jsonl')
assert len(events) == 46 and len(replay['journal_rows']) == 44
state = {'schema': 'resident-window-state-v1', 'params_id': g['crypto']['params_id'],
         'key_id': g['key_id'], 'genesis': digest(g),
         'routes': {str(r): {'queue': [], 'acc_ct': g['zero_ct_sha256'], 'admissions': 0} for r in g['routes']}}
initial = copy.deepcopy(state)
ids, nonces, records_seen, known = set(), set(), set(), {}
expected_calls = []
learns = infers = expiries = 0
for rev, (event, saved) in enumerate(zip(events[:44], replay['journal_rows'], strict=True), 1):
    reply = event['reply']; envelope = reply['envelope']; p = envelope['payload']
    req = p['request']; a = req['action']; proposal = req['proposal']; delta = p['delta']
    assert canonical(envelope) == canonical(saved['envelope'])
    assert reply['ok'] and reply['status'] == 'accepted'
    assert p['revision'] == rev and a['parent_revision'] == rev - 1
    assert a['parent_state'] == p['parent_state'] == digest(state)
    assert event['request_sha256'] == p['request_sha256'] == digest(req)
    assert canonical(req['authorization']['payload']) == canonical(a)
    assert a['request_id'] == event['request_id'] and a['request_id'] not in ids
    assert a['nonce'] not in nonces
    ids.add(a['request_id']); nonces.add(a['nonce']); known[a['request_id']] = envelope
    for key, value in {'genesis': digest(g), 'params_id': g['crypto']['params_id'],
                       'program_id': g['crypto']['program_id'], 'program_version': 1,
                       'key_id': g['key_id'], 'public_key_sha256': g['public_key_sha256'],
                       'context_id': g['context_id']}.items():
        assert a[key] == value
    assert type(a['route']) is int and a['route'] == 0
    route = state['routes']['0']; before_acc = route['acc_ct']
    if a['kind'] == 'Learn':
        learns += 1
        assert a['record_id'] not in records_seen; records_seen.add(a['record_id'])
        assert a['recipient'] == g['recipient']
        assert canonical(a['range_assertion']) == b'[-127,127]'
        fresh = {'record_id': a['record_id'], 'ct_sha256': a['fresh_ct']}
        old_entry = route['queue'][0] if len(route['queue']) == 32 else None
        assert delta == {'kind': 'Learn', 'route': 0, 'fresh': fresh,
                         'expired': old_entry, 'acc_ct': proposal['result_ct']}
        assert proposal['expired_ct'] == (old_entry['ct_sha256'] if old_entry else None)
        assert p['output_ct'] is None
        expected_calls.append({'command': 'host-learn', 'acc': before_acc, 'fresh': a['fresh_ct'],
                               'old': proposal['expired_ct'], 'result': proposal['result_ct']})
        route['queue'].append(fresh)
        if old_entry:
            route['queue'].pop(0); expiries += 1
        route['acc_ct'] = proposal['result_ct']; route['admissions'] += 1
        assert reply['delivery']['status'] == 'verified_not_a_release'
    else:
        infers += 1; assert a['kind'] == 'Infer' and learns == infers * 10
        q = queries[a['query_ct']]
        assert a['row_id'] == infers - 1
        for key in ['row_id', 'row_sha256', 'token_sha256']:
            assert a[key] == q[key]
        assert a['recipient'] == q['recipient_id']
        assert delta == {'kind': 'Infer', 'route': 0, 'query_ct': a['query_ct'], 'output_ct': proposal['result_ct']}
        assert p['output_ct'] == proposal['result_ct'] and proposal['expired_ct'] is None
        expected_calls.append({'command': 'host-infer', 'acc': before_acc,
                               'query': a['query_ct'], 'result': proposal['result_ct']})
        assert reply['delivery']['status'] == 'acknowledged'
        assert reply['delivery']['reader']['status'] == 'ciphertextAccepted'
        assert reply['delivery']['reader']['envelope_sha256'] == digest(envelope)
    v = reply['delivery']['verification']
    assert v['status'] == 'verified' and v['revision'] == rev
    assert v['state_digest'] == p['next_state'] == proposal['next_state'] == digest(state)
    assert v['envelope_sha256'] == digest(envelope)
    if rev == 22:
        assert load(E / 'checkpoint.json')['state_digest'] == digest(state)
assert (learns, infers, expiries) == (40, 4, 8)
assert state == replay['head']['state'] and digest(state) == replay['state_digest']
assert replay['revision'] == replay['head']['revision'] == 44
assert state['routes']['1'] == initial['routes']['1']
assert [x['record_id'] for x in state['routes']['0']['queue']] == [f'record-learn-{i:02d}' for i in range(9, 41)]
for event in events[44:]:
    assert event['reply']['status'] == 'replayed'
    assert canonical(event['reply']['envelope']) == canonical(known[event['request_id']])
    assert event['reply']['delivery']['verification']['status'] == 'verifiedReplay'
assert [x['request_id'] for x in events[44:]] == ['learn-01', 'infer-10']
assert events[-1]['reply']['delivery']['reader']['status'] == 'replayed'

commands = rows('commands.jsonl')
durations = defaultdict(list); topcounts = Counter(); role_outputs = defaultdict(list)
for call in commands:
    cmd = call['command'][1]
    assert call['exit_code'] == 0 and call['private_output_omitted'] is False
    assert cmd not in ['reader-decrypt', 'inspect-recipient']
    payload = json.loads(call['stdout']); assert call['stderr'] == ''
    durations[call['role'], cmd].append(call['elapsed_ns'])
    topcounts.update(payload.get('counts', {}))
    if cmd == 'keygen': keygen = payload
    if cmd == 'validate-context':
        assert '--validated-context-sha256' not in call['command']
        assert canonical(payload) == canonical(validation)
    elif cmd not in ['params', 'keygen']:
        index = call['command'].index('--validated-context-sha256')
        assert call['command'][index + 1] == g['context_id']
    if cmd in ['host-learn', 'host-infer']:
        argv = call['command']; flags = dict(zip(argv[2::2], argv[3::2], strict=True))
        item = {'command': cmd, 'acc': Path(flags['--acc']).name, 'result': payload['sha256']}
        if cmd == 'host-learn':
            item.update(fresh=Path(flags['--fresh']).name,
                        old=Path(flags['--old']).name if '--old' in flags else None)
            assert payload['expired_exact_supplied_original'] == ('--old' in flags)
        else: item['query'] = Path(flags['--query']).name
        role_outputs[call['role']].append(item)
for role in ['host', 'authority', 'reader', 'independent_public_replay']:
    assert role_outputs[role] == expected_calls, role
assert set(role_outputs) == {'host', 'authority', 'reader', 'independent_public_replay'}
childcounts = Counter()
for phase in keygen['phases']: childcounts.update(phase.get('counts', {}))
assert len(keygen['phases']) == 33
assert dict(topcounts) == costs['top_level_cli_native_counts']
assert dict(childcounts) == costs['setup_child_native_counts']
assert dict(topcounts + childcounts) == costs['public_total_native_counts_including_setup_children']
assert len(commands) == costs['public_cli_calls'] == 1630
assert len(commands) + len(keygen['phases']) == costs['crypto_processes_including_setup_children'] == 1663
role_totals = defaultdict(lambda: {'calls': 0, 'elapsed_ns': 0})
for spec in costs['role_commands']:
    xs = durations.pop((spec['role'], spec['command']))
    assert (len(xs), sum(xs), min(xs), max(xs)) == (spec['count'], spec['total_ns'], spec['min_ns'], spec['max_ns'])
    role_totals[spec['role']]['calls'] += len(xs)
    role_totals[spec['role']]['elapsed_ns'] += sum(xs)
assert not durations
assert report['public_event_phase_elapsed_ns'] is None
assert report['public_progress_after_40_learn_4_infer_ns'] == load(E / 'progress.json')['public_elapsed_ns'] == 2020574594500

log_stats = Counter(); private_fields = {'signed_score', 'sign', 'answer', 'decode_elapsed_ns'}
def walk(x):
    if isinstance(x, dict):
        assert not private_fields.intersection(x)
        if 'row_signed_score_bounds' in x: log_stats['public_bounds_metadata_fields'] += 1
        argv = x.get('command')
        assert not (isinstance(argv, list) and len(argv) > 1 and argv[1] == 'reader-decrypt')
        assert x.get('private_output_omitted') is not True
        for k, v in x.items():
            if k in ['stdout', 'stderr'] and isinstance(v, str) and v.strip():
                nested = json.loads(v); log_stats['nested_stdout_documents'] += 1; walk(nested)
            else: walk(v)
    elif isinstance(x, list):
        for v in x: walk(v)
for path in sorted(E.glob('*.jsonl')):
    log_stats['log_files'] += 1
    for line in path.read_text().splitlines():
        if line.strip(): log_stats['json_records'] += 1; walk(json.loads(line))
audit = load(E / 'public_log_audit.json')
assert all(audit[k] == v for k, v in log_stats.items())
assert 'signed_score' in (E / 'commands.jsonl').read_text()
assert log_stats['public_bounds_metadata_fields'] == 1
old_driver = ROOT / 'source_original/normal_flow.before_guard_fix.py'
new_driver = ROOT / 'normal_flow.py'
old_ast = ast.parse(old_driver.read_text()); new_ast = ast.parse(new_driver.read_text())
# All eight core modules plus copied runtime are parseable, without importing them.
parsed = []
for name in manifest['source_sha256']:
    if name.endswith('.py'):
        ast.parse((ROOT / name).read_text()); parsed.append(name)

out = {'schema': 'designated-integration-independent-public-review-v1', 'passed': True,
       'script_sha256': sha(Path(__file__).read_bytes()), 'package_manifest_sha256': sha((ROOT / 'EVIDENCE_MANIFEST.json').read_bytes()),
       'accepted_protocol_sha256': sha(protocol.read_bytes()), 'package_file_count': len(inventory),
       'package_bytes': sum(x['bytes'] for x in inventory.values()), 'package_files': inventory,
       'exported_evidence_files': len(manifest['files_sha256']), 'genesis_core_sources': len(g['journal_sources']),
       'genesis_crypto_sources': len(g['crypto_sources']), 'unchanged_original_sources_and_copies': len(old['copied_files_sha256']),
       'native_dependency_hash_matches': True, 'ast_parsed_modules': parsed,
       'canonical_queries_checked': len(queries), 'context_cached_identity_chain_checked_without_algebra': True,
       'ledger_transitions_checked': 44, 'learns': learns, 'infers': infers, 'exact_original_expiries': expiries,
       'public_final_state_digest': digest(state), 'final_queue_length': len(state['routes']['0']['queue']),
       'historical_retries': 2, 'matching_logged_transition_call_sequences': {r: len(v) for r, v in role_outputs.items()},
       'public_cli_calls': len(commands), 'crypto_processes_including_setup_children': 1663,
       'public_role_totals': dict(role_totals), 'public_cli_elapsed_ns_sum': sum(v['elapsed_ns'] for v in role_totals.values()),
       'public_native_counters': dict(topcounts + childcounts), 'public_log_exact_field_check': dict(log_stats),
       'private_files_opened_or_hashed': 0, 'reviewer_crypto_calls': 0, 'new_adversarial_tests': 0,
       'scope': 'Only retained public ledger/metadata/hash accounting; no independent group arithmetic, signature verification, private integer comparison, DB inventory or timing run.'}
(HERE / 'public_check.json').write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({k: v for k, v in out.items() if k not in {'package_files', 'ast_parsed_modules'}}, indent=2))
