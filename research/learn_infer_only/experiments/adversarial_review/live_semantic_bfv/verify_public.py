"""Check retained normal-run public hashes and journal structure, without crypto or private access."""
import collections
import copy
import gzip
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
LIVE = HERE.parents[1] / 'end_to_end/utility/semantic_axis_successor/encrypted_bfv/live_successor'
REPORTS = LIVE / 'reports/run001'
reads = {}

def read(path):
    path = Path(path)
    assert '.private' not in path.parts and not path.name.endswith('.sqlite3')
    raw = path.read_bytes()
    reads[str(path)] = hashlib.sha256(raw).hexdigest()
    return raw

def sha(path):
    read(path)
    return reads[str(Path(path))]

def load(path):
    raw = read(path)
    if str(path).endswith('.gz'):
        raw = gzip.decompress(raw)
    return json.loads(raw)

def rows(path):
    raw = read(path)
    if str(path).endswith('.gz'):
        raw = gzip.decompress(raw)
    return [json.loads(line) for line in raw.splitlines()]

def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(',', ':'), ensure_ascii=True, allow_nan=False).encode()).hexdigest()

def main():
    freeze = load(LIVE / 'freeze.json')
    review = load(HERE / 'source_review.json')
    assert review['accepted'] and review['freeze_sha256'] == sha(LIVE / 'freeze.json')
    for p, expected in freeze['public_source_dependencies'].items():
        assert sha(p) == expected, p
    for name, expected in freeze['snapshot_source_pins'].items():
        assert sha(Path(freeze['runtime']) / 'e2e' / name) == expected, name
    for name, expected in freeze['query_vector_pins'].items():
        assert sha(Path(freeze['runtime']) / 'public_query_inputs' / name) == expected, name
    phases = load(REPORTS / 'phase_commands.json')
    assert [r['phase'] for r in phases] == ['public_phase', 'public_verify', 'private_drain', 'validate']
    assert all(r['returncode'] == 0 and r['process_group_absent'] and not r['timed_out'] for r in phases)
    started = load(LIVE / 'run_started.json')
    command = load(LIVE / 'run.command.json')
    assert started['attempt'] == 1 and started['review_sha256'] == sha(HERE / 'source_review.json')
    assert started['freeze_sha256'] == review['freeze_sha256']
    assert command['returncode'] == 0 and command['phases'] == phases and command['source_snapshot_and_model_bytes_unchanged']
    phase = load(REPORTS / 'public_phase.json')
    gate = load(REPORTS / 'public_verification.json')
    report = load(REPORTS / 'report.json')
    validation = load(REPORTS / 'validation.json')
    assert all(x['ok'] for x in [phase, gate, report, validation])
    assert phase['all_services_closed'] and phase['received_before_private_phase'] == phase['reader_decryptions'] == 0
    assert phase['events'] == phase['verified_revision'] == 3 and phase['registered_tickets'] == 2
    assert {r['role'] for r in phase['services']} == {'host', 'authority', 'verifier', 'baseline_reader'}
    assert gate['freeze_sha256'] == review['freeze_sha256']
    assert gate['public_phase_sha256'] == sha(REPORTS / 'public_phase.json')
    assert gate['accepted_envelopes_sha256'] == sha(REPORTS / 'accepted_envelopes.json')
    assert gate['verifier_sha256'] == sha(LIVE / 'public_verify.py')
    assert gate['events'] == gate['independent_arithmetic_transitions'] == 3
    assert gate['received_before_private_phase'] == gate['private_decryptions'] == 0
    assert gate['authority_pending_infers'] == gate['registered_tickets'] == 2
    assert gate['all_service_pids_absent'] and gate['durable_journals_equal'] and gate['private_files_read'] is False
    assert gate['model_bytes_unchanged_before_private_drain']
    expected_models = {n: row['sha256'] for n, row in freeze['model_files'].items()}
    assert gate['model_files_after_public_phase'] == load(REPORTS / 'model_pins_after.json') == expected_models
    assert report['public_verification_sha256'] == sha(REPORTS / 'public_verification.json')
    assert report['learns'] == 1 and report['infers'] == 2 and report['events'] == 3 and report['expiries'] == 0
    assert report['public_phase_decryptions'] == report['baseline_decryptions'] == 0
    assert report['verified_decryptions_after_public_verification'] == report['oracle_comparisons'] == 2
    assert report['actual_model_forward_calls'] == 1 and report['actual_axis_examples'] == 2
    assert report['generated_tokens'] == report['weight_updates'] == 0 and report['cached_feature_substitution'] is False
    assert report['all_oracle_matches'] and report['same_durable_verified_journal'] and report['authority_outbox_still_pending']
    assert report['output_change_discloses_selected_score_under_fixed_mapping']
    assert type(report['output_changed_after_learning']) is bool
    assert validation['authority_pending_infers'] == 2 and validation['selected_score_secrecy_claim'] is False
    assert validation['source_model_query_and_parent_pins_match'] and validation['runtime_gitignored']
    assert not ({'predicted_bits', 'vector', 'vector_sha256', 'signed_score', 'answers', 'expected'} & set(report))

    genesis = load(REPORTS / 'genesis.json.gz')
    envelopes = load(REPORTS / 'accepted_envelopes.json')
    storage = load(REPORTS / 'public_storage.json')
    assert len(envelopes) == 3 and storage['verified_journal'] == envelopes
    assert storage['registered_tickets'] == 2 and storage['verified_records'] == 3 and storage['received'] == 0
    state = {'schema': 'resident-window-state-v1', 'params_id': genesis['crypto']['params_id'], 'key_id': genesis['key_id'], 'genesis': digest(genesis),
             'routes': {str(route): {'queue': [], 'acc_ct': genesis['zero_ct_sha256'], 'admissions': 0} for route in genesis['routes']}}
    requests, nonces, selected_queries, outputs = set(), set(), [], []
    identities = {'genesis': digest(genesis), 'params_id': genesis['crypto']['params_id'], 'program_id': genesis['crypto']['program_id'],
                  'program_version': 1, 'key_id': genesis['key_id'], 'public_key_sha256': genesis['public_key_sha256']}
    for rev, envelope in enumerate(envelopes, 1):
        payload = envelope['payload']
        request = payload['request']
        action = request['action']
        delta, proposal = payload['delta'], request['proposal']
        kind = ['Infer', 'Learn', 'Infer'][rev - 1]
        assert action['kind'] == delta['kind'] == kind and action['route'] == delta['route'] == 0
        assert action['recipient'] == genesis['recipient']
        assert all(action[k] == v for k, v in identities.items())
        assert request['authorization']['payload'] == action
        assert payload['request_sha256'] == digest(request)
        assert payload['revision'] == rev and action['parent_revision'] == rev - 1
        assert action['parent_state'] == payload['parent_state'] == digest(state)
        assert action['request_id'] not in requests and action['nonce'] not in nonces
        requests.add(action['request_id']); nonces.add(action['nonce'])
        if kind == 'Learn':
            route = state['routes']['0']
            assert delta['fresh'] == {'record_id': action['record_id'], 'ct_sha256': action['fresh_ct']}
            assert delta['expired'] is None and proposal['expired_ct'] is None
            assert route['queue'] == []
            route['queue'].append(copy.deepcopy(delta['fresh']))
            route['acc_ct'] = delta['acc_ct']; route['admissions'] += 1
            assert proposal['result_ct'] == delta['acc_ct'] and payload['output_ct'] is None
        else:
            assert {'query_ct': action['query_ct'], 'route': 0} in genesis['query_policy']
            assert delta['query_ct'] == action['query_ct']
            assert delta['output_ct'] == payload['output_ct'] == proposal['result_ct']
            assert proposal['expired_ct'] is None
            selected_queries.append(action['query_ct']); outputs.append(payload['output_ct'])
        assert payload['next_state'] == proposal['next_state'] == digest(state)
    assert selected_queries[0] == selected_queries[1] and phase['same_query_before_after']
    infer_envelopes = [envelopes[0], envelopes[2]]
    assert report['offline_receive_receipts'] == [
        {'ok': True, 'status': 'received', 'nonce': e['payload']['request']['action']['nonce'], 'envelope_sha256': digest(e)}
        for e in infer_envelopes
    ]
    assert storage['verified_state'] == state and gate['final_state_digest'] == digest(state)
    for files in gate['public_cas_files'].values():
        assert all(name == h for name, h in files.items())
        assert all(r['acc_ct'] in files for r in state['routes'].values())
        assert all(output in files for output in outputs)
    # These are public serialized query/CT blobs, never the private DB or configs.
    runtime_run = Path(freeze['runtime']) / 'run'
    assert sha(runtime_run / 'queries/q01.json') == selected_queries[0]
    assert load(runtime_run / 'queries/q01.json')['coefficients'] == [127] + [0] * 576
    public_cas_files = 0
    for directory, files in gate['public_cas_files'].items():
        assert directory in ['host_cas', 'authority/cas', 'verified_cas']
        for name, expected in files.items():
            assert len(name) == 64 and sha(runtime_run / directory / name) == expected
            public_cas_files += 1

    log_counts = {}
    command_counts = collections.Counter()
    for name in ['commands.jsonl.gz', 'verified_commands.jsonl.gz', 'independent_public_commands.jsonl']:
        commands = rows(REPORTS / name); log_counts[name] = len(commands)
        for row in commands:
            assert row['exit_code'] == 0 and row['command'][1] != 'reader-decrypt'
            command_counts[row['command'][1]] += 1
    private_commands = rows(REPORTS / 'private_receive_commands.jsonl.gz')
    log_counts['private_receive_commands.jsonl.gz'] = len(private_commands)
    decrypts = [r for r in private_commands if r['command'][1] == 'reader-decrypt']
    assert len(decrypts) == 2
    assert all(r['command'][1] in ['inspect', 'reader-decrypt'] and r['exit_code'] == 0 for r in private_commands)
    assert all(r['stdout'] is None and r['stderr'] is None and r['private_output_omitted'] for r in decrypts)
    for command, output in zip(decrypts, outputs):
        argv = command['command']
        assert Path(argv[argv.index('--ct') + 1]) == runtime_run / 'verified_cas' / output
    rpcs = load(REPORTS / 'verified_rpc.json')
    assert not any(r['op'] == 'receive' for r in rpcs)
    assert sum(r['op'] == 'sync' for r in rpcs) == 3
    hosts = rows(REPORTS / 'host_worker.jsonl.gz')
    assert len(hosts) == 3 and hosts[-1]['reply']['cumulative_stats'] == phase['host_worker']['stats']
    host_stats = phase['host_worker']['stats']
    assert host_stats['requests'] == 3 and host_stats['cas_get_calls'] == host_stats['full_blob_sha256_calls']
    replay = load(REPORTS / 'replay.json.gz')
    assert replay['public_recomputation'] and phase['public_replay']['public_recomputation']
    assert replay['revision'] == phase['public_replay']['revision'] == 3
    assert replay['state_digest'] == phase['public_replay']['state_digest'] == digest(state)
    assert replay['head']['state'] == state and replay['head']['revision'] == 3
    assert [row['envelope'] for row in replay['journal_rows']] == envelopes
    for name in ['admissions', 'queue_lengths']:
        assert replay[name] == phase['public_replay'][name] == {'0': 1, '1': 0}
    result = {'schema': 'live-semantic-independent-public-review-v1', 'ok': True,
              'freeze_sha256': review['freeze_sha256'], 'events': 3, 'learns': 1, 'infers': 2, 'expiries': 0,
              'public_phase_order': [r['phase'] for r in phases], 'process_groups_absent_after_phases': True,
              'authority_verified_exports_same_three_event_chain': True, 'same_q01': True,
              'public_cas_blobs_hashed': public_cas_files, 'public_command_counts': dict(command_counts), 'log_rows': log_counts,
              'logged_private_decryptions_after_public_gate': len(decrypts), 'private_decrypt_stdout_stderr_omitted': True,
              'author_reported_model_forwards': 1, 'author_reported_integer_comparisons': 2,
              'author_reported_all_integer_matches': True, 'author_reported_output_changed': report['output_changed_after_learning'],
              'selected_after_score_disclosed_by_boolean': True,
              'signature_and_ciphertext_arithmetic_review': 'Source inspected and author replay records checked; not re-executed by reviewer.',
              'private_integer_comparisons_review': 'Attributed to the retained author report and reviewed source; private values not read.',
              'private_file_reads': 0, 'model_or_crypto_imports': 0, 'source_sha256': sha(__file__), 'public_file_sha256': reads}
    (HERE / 'public_check.json').write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'public_file_sha256'}, sort_keys=True))

if __name__ == '__main__':
    main()
