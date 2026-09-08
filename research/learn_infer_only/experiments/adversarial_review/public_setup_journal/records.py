#!/usr/bin/env python3
"""Check frozen exported public records only; no crypto/source-runtime imports."""
from pathlib import Path
import collections
import gzip
import hashlib
import json

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[4]
AUTHOR = ROOT / 'research/learn_infer_only/experiments/private_construction/designated_span/public_coin_setup/journal'
REPORTS = AUTHOR / 'reports/normal_002'


def raw(name):
    path = REPORTS / name
    assert path.parent == REPORTS and '.private' not in path.parts
    return path.read_bytes()


def sha_bytes(data):
    return hashlib.sha256(data).hexdigest()


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(',', ':'), ensure_ascii=True,
                      allow_nan=False).encode()


def digest(obj):
    return sha_bytes(canonical(obj))


def doc(name):
    return json.loads(raw(name))


def lines(name):
    return [json.loads(line) for line in gzip.decompress(raw(name)).splitlines() if line]


def main():
    g = doc('genesis.json')
    gid = digest(g)
    public = doc('public_complete.json')
    final = doc('report.json')
    assert public['ok'] is True and final['ok'] is True
    assert final['public_complete_sha256'] == sha_bytes(raw('public_complete.json'))
    assert final['execution_pins_sha256'] == sha_bytes(raw('execution_pins.json'))
    assert public['genesis_sha256'] == final['genesis_sha256'] == gid
    assert final['context_id'] == public['context_id'] == g['context_id']
    accepted = doc('accepted_envelopes.json')
    replay = json.loads(gzip.decompress(raw('replay.json.gz')))
    assert [r['envelope'] for r in replay['journal_rows']] == accepted
    assert len(accepted) == 44 and replay['genesis'] == gid
    assert replay['public_recomputation'] is True
    state = {'schema': 'resident-window-state-v1', 'params_id': g['crypto']['params_id'],
             'key_id': g['key_id'], 'genesis': gid,
             'routes': {str(route): {'queue': [], 'acc_ct': g['zero_ct_sha256'], 'admissions': 0}
                        for route in g['routes']}}
    identities = dict(genesis=gid, params_id=g['crypto']['params_id'],
                      program_id=g['crypto']['program_id'], program_version=1,
                      key_id=g['key_id'], public_key_sha256=g['public_key_sha256'],
                      context_id=g['context_id'])
    fresh, ids, nonces, records, infer_indices, expired = [], set(), set(), set(), [], []
    requests = {}
    for revision, envelope in enumerate(accepted, 1):
        p = envelope['payload']
        request = p['request']
        action, delta, proposal = request['action'], p['delta'], request['proposal']
        assert envelope['domain'] == 'resident-authority-finalization-v1'
        assert p['request_sha256'] == digest(request)
        assert p['revision'] == revision and action['parent_revision'] == revision - 1
        assert p['parent_state'] == action['parent_state'] == digest(state)
        assert all(action[key] == value for key, value in identities.items())
        assert canonical(action) == canonical(request['authorization']['payload'])
        assert action['route'] == 0
        assert action['request_id'] not in ids and action['nonce'] not in nonces
        ids.add(action['request_id']); nonces.add(action['nonce'])
        requests[action['request_id']] = request
        route = state['routes']['0']
        if action['kind'] == 'Learn':
            assert action['record_id'] not in records
            records.add(action['record_id'])
            assert request['authorization']['domain'] == 'resident-issuer-v1'
            assert action['recipient'] == g['recipient']
            assert action['range_assertion'] == [-127, 127]
            old = route['queue'][0] if len(route['queue']) == g['capacity'] else None
            entry = {'record_id': action['record_id'], 'ct_sha256': action['fresh_ct']}
            assert delta['fresh'] == entry and delta['expired'] == old
            assert delta == {'kind': 'Learn', 'route': 0, 'fresh': entry,
                             'expired': old, 'acc_ct': proposal['result_ct']}
            assert proposal['expired_ct'] == (old['ct_sha256'] if old else None)
            assert delta['acc_ct'] == proposal['result_ct'] and p['output_ct'] is None
            if old:
                expired.append(old['ct_sha256'])
                route['queue'].pop(0)
            route['queue'].append(entry)
            route['acc_ct'] = proposal['result_ct']; route['admissions'] += 1
            fresh.append(action['fresh_ct'])
            assert action['request_id'] == f'learn-{len(fresh):02d}'
        else:
            assert action['kind'] == 'Infer' and len(fresh) in [10, 20, 30, 40]
            index = len(fresh) // 10 - 1
            assert action['request_id'] == f'infer-{len(fresh):02d}'
            assert action['row_id'] == index
            assert request['authorization']['domain'] == 'resident-query-authorization-v1'
            binding = g['query_bindings'][action['query_ct']]
            assert action['recipient'] == binding['recipient_id']
            assert all(action[key] == binding[key] for key in ['row_id', 'row_sha256', 'token_sha256'])
            assert {'query_ct': action['query_ct'], 'route': 0} in g['query_policy']
            assert delta == {'kind': 'Infer', 'route': 0, 'query_ct': action['query_ct'],
                             'output_ct': proposal['result_ct']}
            assert p['output_ct'] == proposal['result_ct'] and proposal['expired_ct'] is None
            infer_indices.append(index)
        assert digest(state) == proposal['next_state'] == p['next_state']
    assert len(fresh) == 40 and expired == fresh[:8] and infer_indices == [0, 1, 2, 3]
    assert [e['ct_sha256'] for e in state['routes']['0']['queue']] == fresh[8:]
    assert state['routes']['1'] == {'queue': [], 'acc_ct': g['zero_ct_sha256'], 'admissions': 0}
    assert replay['head']['state'] == state and replay['head']['revision'] == 44
    assert replay['head']['state_digest'] == replay['state_digest'] == digest(state)
    assert public['independent_replay']['state_digest'] == digest(state)

    events = lines('events.jsonl.gz')
    assert len(events) == 46
    assert [event['reply']['envelope'] for event in events[:44]] == accepted
    assert all(e['reply']['status'] == 'accepted' for e in events[:44])
    by_id = {e['payload']['request']['action']['request_id']: e for e in accepted}
    retry_ids = []
    for event in events[44:]:
        event_id = event['request_id']; retry_ids.append(event_id)
        assert event['reply']['status'] == 'replayed'
        assert event['reply']['envelope'] == by_id[event_id]
        assert event['request_sha256'] == digest(requests[event_id])
    assert retry_ids == ['learn-01', 'infer-10'] == public['authorized_historical_retries']
    assert events[-1]['reply']['delivery']['reader']['status'] == 'replayed'
    reopen = doc('orderly_reopen.json')
    assert reopen == public['orderly_reopen']
    assert reopen['revision'] == 22 and reopen['exact_head_preserved'] is True
    assert reopen['state_digest'] == accepted[21]['payload']['next_state']

    commands = lines('commands.jsonl.gz')
    counter = collections.Counter((c['role'], c['command'][1]) for c in commands)
    assert len(commands) == public['public_calls']
    assert not {'keygen', 'initializer', 'recipient-register', 'reader-decrypt', 'inspect-recipient'}.intersection(c['command'][1] for c in commands)
    assert [c['command'][1] for c in commands if c['role'] == 'honest_public_setup'] == (
        ['auth-init'] + ['recipient-init'] * 16 + ['public-build', 'verify-public'])
    assert counter['honest_setup', 'recipient-finalize'] == 16
    assert counter['honest_setup', 'validate-context'] == 1
    assert counter['honest_setup', 'encode-query'] == 16
    assert counter['issuer', 'issuer-encrypt'] == 40
    for role in ['host', 'authority', 'reader', 'independent_public_replay']:
        assert counter[role, 'host-learn'] == 40 and counter[role, 'host-infer'] == 4
    for c in commands:
        assert c['exit_code'] == 0 and c['private_output_omitted'] is False
        if c['role'] in ['host', 'authority', 'reader', 'independent_public_replay', 'public_transport']:
            assert c['command'][1] in ['inspect', 'host-learn', 'host-infer']
            assert '--sk' not in c['command'] and '--vector' not in c['command']

    hosts = lines('host_worker.jsonl.gz')
    servers = lines('server_processes.jsonl.gz')
    assert len(hosts) == public['host_worker']['requests'] == 44
    assert collections.Counter(x['role'] for x in servers) == {'authority': 2, 'reader': 2}
    assert all('--fault' not in item['argv'] for item in servers)
    assert all(h['request_stats']['cas_get_calls'] == h['request_stats']['full_blob_sha256_calls'] for h in hosts)
    assert public['host_worker']['clean_exit'] is True
    for key in ['all_public_replay_and_operations_before_private_drain',
                'all_public_workers_and_services_closed',
                'private_answer_db_absent_through_public_checks']:
        assert public[key] is True
    assert public['public_acceptor_has_recipient_key_paths'] is False
    assert final['all_public_operations_replay_and_services_close_before_any_private_drain'] is True

    # Exact schema-field audit of the named exported logs. Strings are decoded
    # only for complete JSON stdout/stderr; this is not a side-channel proof.
    forbidden = {'signed_score', 'sign', 'answer', 'decode_elapsed_ns'}
    counters = collections.Counter()
    def walk(obj):
        if isinstance(obj, dict):
            assert not forbidden.intersection(obj)
            for key, value in obj.items():
                if key in ['stdout', 'stderr'] and isinstance(value, str) and value.strip():
                    try:
                        parsed = json.loads(value)
                    except json.JSONDecodeError:
                        assert key == 'stderr'
                    else:
                        counters['nested_json'] += 1; walk(parsed)
                else:
                    walk(value)
        elif isinstance(obj, list):
            for value in obj:
                walk(value)
    exported_logs = [p.name for p in REPORTS.glob('*.jsonl.gz')]
    for name in exported_logs:
        for value in lines(name):
            counters['records'] += 1; walk(value)

    # Read only public aggregate outputs, never the private comparison values.
    assert final['all_private_integer_comparisons_match'] is True
    assert final['private_integer_comparisons'] == 4
    assert final['private_drain_retry_new_decodes'] == 0
    inventory = doc('public_ciphertext_inventory.json')
    for role, entries in inventory.items():
        assert len(entries) == public['retained_public_cas'][role]['objects']
        assert sum(e['bytes'] for e in entries) == public['retained_public_cas'][role]['bytes']
        assert all(len(e['sha256']) == 64 and e['bytes'] > 0 for e in entries)
    own = {'claim_kind': 'EXECUTED',
           'scope': 'Independent canonical hash/state/record controls on exported public artifacts; no cryptographic verification or private reads',
           'genesis': gid, 'final_state_digest': digest(state),
           'checks': {'finalized_envelopes': len(accepted), 'learns': len(fresh),
                      'infers': len(infer_indices), 'exact_fifo_expiries': len(expired),
                      'normal_historical_retries': len(retry_ids), 'reopen_revision': 22,
                      'public_command_records': len(commands),
                      'named_exported_logs': len(exported_logs),
                      'parsed_public_log_records': counters['records'],
                      'parsed_nested_stdout_documents': counters['nested_json'],
                      'host_requests': len(hosts), 'service_starts': len(servers)},
           'public_command_counts': [{'role': r, 'command': c, 'count': n} for (r, c), n in sorted(counter.items())],
           'author_reported_only': {'all_four_private_integer_comparisons_match': True,
                                    'private_retry_new_decodes': 0,
                                    'processes_closed_before_private_drain': 'source control-flow and public completion record; no private phase timing read'},
           'limitations': ['No group recomputation or signature verification in this reviewer',
                           'No private score, scalar, private file/hash or decoder execution',
                           'Hash chains and log schemas do not prove OS isolation or side-channel privacy'],
           'public_artifacts_sha256': {p.name: sha_bytes(p.read_bytes()) for p in sorted(REPORTS.iterdir())
                                      if p.is_file() and p.name not in ['checkpoint.json', 'stdout.jsonl', 'stderr.log']}}
    (BASE / 'record_review.json').write_text(json.dumps(own, indent=2) + '\n')
    print(json.dumps(own['checks'], indent=2))


if __name__ == '__main__':
    main()
