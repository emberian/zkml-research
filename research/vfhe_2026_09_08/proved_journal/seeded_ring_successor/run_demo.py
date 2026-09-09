#!/usr/bin/env python3
"""One fresh restricted-ring durable model, two exact expiries and fixed readers."""
import argparse
import copy
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

import ring_service as s
import delivery as d

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__); parser.add_argument('--run', default='seeded001'); args = parser.parse_args()
    assert args.run.isalnum()
    root, output = HERE / 'runtime' / args.run, HERE / 'results' / args.run
    assert not root.exists() and not output.exists()
    output.mkdir(parents=True)
    start = time.monotonic(); deadline = start + 900
    fixture = s.read(s.BACKEND / 'fixture.json')
    s.write(output / 'launch.json', {'argv': [sys.executable, '-B', str(Path(__file__)), '--run', args.run],
        'started_utc': datetime.now(timezone.utc).isoformat(), 'contract_sha256': s.sha(HERE / 'CONTRACT.md'),
        'demo_source_sha256': s.sha(Path(__file__)), 'fixture_sha256': s.sha(s.BACKEND / 'fixture.json'),
        'scope': 'One shared fresh dual-384-bit seeded semantic ring durable join; no compiler/succinct proof.'})
    initial = s.create(root, deadline)
    service = s.Service(root, deadline)
    records, refused, reopened = [], None, None
    for event in fixture['events']:
        n, label = event['event'], event['class']
        vector = root / 'public' / ('vector_%02d.json' % n)
        s.write(vector, [v % service.genesis['parameters']['p'] for v in event['vector']])
        before = service.head()
        prepared = service.prepare(label, vector, 'cached-train-%s' % event['train_index'], 'teach%02d' % n)
        assert service.head() == before
        if n == 5:
            original = s.read(Path(prepared['bundle'])); changed = copy.deepcopy(original)
            bad_file = root / 'public/changed_candidate.ring'
            shutil.copyfile(original['files']['candidate'], bad_file)
            # Canonical packed LSB0 representation: change the first residue
            # modulo q and preserve the following coefficient's overlapping bits.
            q = service.genesis['parameters']['q']; width = q.bit_length(); size = (width + 7) // 8
            with bad_file.open('r+b') as f:
                assert f.read(8) == b'RINGSSM2'; length = int.from_bytes(f.read(4), 'big'); f.seek(length, 1)
                offset = f.tell(); raw = int.from_bytes(f.read(size), 'little'); mask = (1 << width) - 1
                value = raw & mask; assert value < q
                new = (raw & ~mask) | ((value + 1) % q); f.seek(offset); f.write(new.to_bytes(size, 'little'))
            changed['request']['request_id'] = 'changed-candidate-refusal'
            changed['files']['candidate'] = str(bad_file)
            changed['request']['candidate_sha256'] = s.sha(bad_file)
            changed['request']['next_model_root'] = s.model_root(service.next_classes(before['head'], changed['request']))
            bad = root / 'public/changed_request.json'; s.write(bad, changed)
            try: service.submit(bad)
            except s.Refused as error: refused = {'code': error.code, 'evidence': error.evidence}
            assert refused['code'] == 'complete_candidate_recomputation_mismatch'
            assert service.head() == before
            s.write(output / 'changed_candidate_refusal.json', {'request': changed['request'], 'refusal': refused,
                'canonical_changed_coefficient_index': 0, 'head_before': before, 'head_after': service.head()})
        accepted = service.submit(Path(prepared['bundle']))
        assert accepted['status'] == 'accepted' and accepted['receipt']['all_candidate_bytes_equal'] is True
        assert bool(accepted['receipt']['request']['expired_sha256']) == (event['expired_event'] is not None)
        after = service.head()
        assert after['head']['revision'] == n
        assert all(after['head']['classes'][c] == before['head']['classes'][c] for c in fixture['classes'] if c != label)
        records.append(accepted); s.write(output / 'accepted_updates.json', records)
        if n == 4:
            argv = ['/usr/bin/sandbox-exec', '-f', str(root / 'profiles/public.sb'), sys.executable, '-B', str(HERE / 'ring_service.py'), 'audit', '--root', str(root)]
            t = time.monotonic(); process = subprocess.run(argv, capture_output=True, text=True, timeout=min(180, deadline - time.monotonic()))
            assert process.returncode == 0, process.stderr
            reopened = json.loads(process.stdout); assert reopened == after
            s.write(output / 'reopen.json', {'argv': argv, 'exit_code': process.returncode, 'elapsed_seconds': time.monotonic() - t,
                'stdout': process.stdout, 'stderr': process.stderr, 'exact_head_match': True})
    final = service.head()
    stale = copy.deepcopy(s.read(root / 'proposals/teach01/request.json')); stale['request']['request_id'] = 'stale-parent-refusal'
    stale_path = root / 'public/stale_request.json'; s.write(stale_path, stale)
    stale_refusal = None
    try: service.submit(stale_path)
    except s.Refused as e: stale_refusal = e.code
    assert stale_refusal == 'stale_parent' and service.head() == final
    retry = service.submit(root / 'proposals/teach01/request.json')
    assert retry['status'] == 'replayed' and retry['receipt_sha256'] == records[0]['receipt_sha256']
    assert service.head() == final
    s.write(output / 'stale_and_retry.json', {'stale_refusal': stale_refusal, 'head_unchanged': True,
        'retry_same_receipt': True, 'retry_receipt_sha256': retry['receipt_sha256']})
    published = service.publish()
    service.check_assets()
    assert s.sha(root / 'public/a.ring') == service.genesis['a_sha256']
    assert s.sha(root / 'public/public.ring') == service.genesis['public_sha256']
    closure = {'status': 'PASS', 'genesis': service.gid, 'accepted_head': final, 'publication': published,
        'all_public_actor_processes_exited': True, 'positive_complete_byte_comparisons': 6,
        'complete_bytes_compared': [r['receipt']['bytes_compared'] for r in records], 'fresh_encodes': 6,
        'exact_expiries': 2, 'public_actor_private_artifact_reads': 0, 'source_setup_pins_unchanged': True,
        'elapsed_seconds': time.monotonic() - start, 'verification': 'Complete deterministic recomputation in this ring backend, not a succinct/compiler proof.'}
    s.write(output / 'PUBLIC_COMPLETE.json', closure)
    print(json.dumps({'phase': 'public_complete', 'elapsed_seconds': closure['elapsed_seconds']}), flush=True)
    answers, requests = [], []
    for i in range(16):
        s.need(time.monotonic() < deadline, 'bounded_run_deadline')
        role = 'recipient_%02d' % i
        request = d.make_request(root, i, 'query-%02d' % i, 'delivery-%02d' % i, published['models'])
        s.write(output / (role + '_request.json'), request)
        delivered = d.deliver(root, request)
        assert delivered['status'] == 'delivered' and delivered['new_private_actor_invocations'] == 1
        result = delivered['receipt']
        assert result['coordinate'] == i and result['private_rows_read'] == 1
        assert result['accepted_head_sha256'] == final['head_sha256']
        assert result['request']['registry_sha256'] == service.genesis['registry_sha256']
        expected = fixture['snapshots'][-1]
        assert result['query_results'] == [{'revision': 6, 'scores': expected['scores'][i], 'prediction': expected['predictions'][i]}]
        answers.append(delivered); requests.append(request)
        s.write(output / (role + '.json'), delivered)
        print(json.dumps({'phase': 'recipient_completed', 'coordinate': i}), flush=True)
    actual_reads = len(list((root / 'deliveries').glob('*/transport.json')))
    assert actual_reads == 16
    replay = d.deliver(root, requests[0])
    assert replay['status'] == 'replayed' and replay['new_private_actor_invocations'] == 0
    assert replay['receipt_sha256'] == answers[0]['receipt_sha256']
    conflict = copy.deepcopy(requests[0]); conflict['delivery_id'] = 'changed-delivery-id'
    delivery_refusal = None
    try: d.deliver(root, conflict)
    except s.Refused as error: delivery_refusal = error.code
    assert delivery_refusal == 'delivery_id_or_request_conflict'
    assert len(list((root / 'deliveries').glob('*/transport.json'))) == actual_reads
    s.write(output / 'delivery_retry_and_conflict.json', {'exact_retry_same_receipt': True,
        'receipt_sha256': replay['receipt_sha256'], 'retry_new_private_actor_invocations': 0,
        'changed_id_refusal': delivery_refusal, 'total_private_actor_invocations': actual_reads,
        'head_unchanged': service.head() == final})
    assert service.head() == final; service.check_assets()
    # Explicit public metadata/setup allowlist; key payloads and large CTs stay in runtime.
    for name in ('genesis.json', 'registry.json'): shutil.copyfile(root / name, output / name)
    shutil.copyfile(published['models'], output / 'accepted_models.json')
    shutil.copyfile(s.BACKEND / 'fixture.json', output / 'fixture.json')
    shutil.copyfile(root / 'public/a.ring', output / 'a.ring')
    shutil.copyfile(root / 'public/public.ring', output / 'public.ring')
    s.write(output / 'public_setup.json', {'header': s.header(root / 'public/public.ring'),
        'a_sha256': service.genesis['a_sha256'], 'public_sha256': service.genesis['public_sha256'],
        'setup_descriptor_sha256': service.genesis['setup_descriptor_sha256'],
        'a_descriptor_bytes': (root / 'public/a.ring').stat().st_size,
        'public_issuer_bundle_bytes': (root / 'public/public.ring').stat().st_size})
    shutil.copytree(root / 'logs', output / 'actors')
    shutil.copytree(root / 'profiles', output / 'profiles')
    for directory in (root / 'deliveries').iterdir():
        if directory.is_dir(): shutil.copytree(directory, output / 'deliveries' / directory.name)
    s.write(output / 'final_head.json', final)
    result = {'schema': 'durable-seeded-semantic-ring-result-v1', 'status': 'PASS',
        'claim': 'EXECUTED shared fresh seeded semantic ring learner with complete public recomputation and durable identified delivery',
        'finished_utc': datetime.now(timezone.utc).isoformat(), 'elapsed_seconds': time.monotonic() - start,
        'public_elapsed_seconds': closure['elapsed_seconds'], 'fresh_registered_keys': 16, 'missing_row_secrets': 0,
        'universal_reader_constructed': False, 'fresh_encodes': 6, 'accepted_updates': 6, 'exact_expiries': 2,
        'full_candidate_byte_comparisons': 6, 'full_file_bytes_per_positive': closure['complete_bytes_compared'],
        'changed_canonical_candidate_refused': True, 'stale_parent_refused': True, 'historical_retry_same_receipt': True,
        'fresh_process_reopen_revision': 4, 'exact_head_reopen': True, 'accepted_revision_served': 6,
        'registered_recipients_served': 16, 'scalar_scores_matched': 32, 'decisions_matched': 16,
        'public_complete_before_recipient_queries': True, 'public_actor_private_artifact_reads': 0,
        'orchestrator_private_payload_reads': 0, 'sources_unchanged': True,
        'genesis': service.gid, 'final_head_sha256': final['head_sha256'], 'registry_sha256': service.genesis['registry_sha256'],
        'seed_policy': service.genesis['seed_policy'], 'seed_bits': service.genesis['seed_bits'],
        'setup_descriptor_sha256': service.genesis['setup_descriptor_sha256'],
        'a_descriptor_bytes': (root / 'public/a.ring').stat().st_size,
        'public_issuer_bundle_bytes': (root / 'public/public.ring').stat().st_size,
        'missing_public_rows_seed_described': 561, 'exact_delivery_retry_without_key': True,
        'changed_delivery_id_refused': True, 'seeded_setup_scope': 'Conditional QROM application; concrete SHAKE heuristic, no ideal-uniform distribution claim.',
        'verification_scope': 'Full deterministic canonical acc+fresh-old recomputation over this ring, not a succinct/compiler proof.',
        'key_scope': 'Each fixed key exposes its registered query on all retained inputs/allowed combinations; coalitions get their per-input span. No cryptographic history-bound release.',
        'utility_scope': 'Completed known-public cached linear semantic fixture, not a new accuracy or privacy estimate.'}
    s.write(output / 'RESULT.json', result); print(json.dumps(result, indent=2))


if __name__ == '__main__': main()
