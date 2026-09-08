#!/usr/bin/env python3
"""Actual event65 -> event66 multiclass public proof-gated sequence."""
from datetime import datetime, timezone
import argparse
import json
import os
from pathlib import Path
import selectors
import shutil
import subprocess
import sys
import tempfile
import time
import service as s

HERE = Path(__file__).resolve().parent
BASE = HERE.parent.parent
REPO = BASE.parent.parent
BINARY_SHA = 'dd41ec2eac52bf35ff8a9c6e736fa4dcb7cb4ae41cec6bace5cf593a3cf87cc6'
TEMPLATE_SHA = '1afc2b3a120f59fdd79d273c6d32887373c5718225cb6e94b82a7231010c3aa7'
PROOF65_SHA = 'acf747cf42eff8171b2b774abae5572e8d7bdb7ace144754c7605128c15e5ba6'
PROOF66_SHA = '365006cd229920b4cda7118fa51f89cc012124e8681eb2e7b75291e402407a01'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', default='sequence001')
    args = parser.parse_args()
    assert args.run.isalnum()
    output, runtime = HERE / 'results' / args.run, HERE / 'runtime' / args.run
    assert not output.exists() and not runtime.exists()
    output.mkdir(parents=True)
    runtime.mkdir(parents=True, mode=0o700)
    root = runtime / 'service'
    binary = BASE / 'proved_operation/target/release/vfhe-proved-operation'
    template = BASE / 'arithmetic_coverage/artifacts_expiry/template_ir2.json'
    case65 = BASE / 'proved_operation/results/learner_expiry001'
    origin66 = BASE / 'update_pipeline/cases/event66'
    rows66 = BASE / 'update_pipeline/runs/event66_fast/case/public_ntt_rows.json'
    proof65 = BASE / 'proved_operation/results/expiry_proof001/proof.bin'
    proof66 = BASE / 'update_pipeline/results/production/proof.bin'
    production = BASE / 'update_pipeline/results/production/result.json'
    operations = REPO / 'research/learn_infer_only/experiments/end_to_end/useful_learner_2026_09_08/models/bfv/operations.jsonl'
    started = time.monotonic_ns()
    commands, messages = [], []
    paths = [HERE / 'service.py', HERE / 'checkpoint_from_records.py', Path(__file__), binary, template, proof65, proof66,
        production, rows66, operations, HERE.parent / 'service.py', HERE.parent / 'results/demo001/RESULT.json']
    for case in (case65, origin66):
        paths.extend([case / (n + '.ct') for n in s.NAMES] + [case / 'source_event.json'])
    paths.append(case65 / 'public_ntt_rows.json')
    pins = {str(p): s.sha(p.read_bytes()) for p in paths}
    assert pins[str(binary)] == BINARY_SHA and pins[str(template)] == TEMPLATE_SHA
    assert pins[str(proof65)] == PROOF65_SHA and pins[str(proof66)] == PROOF66_SHA
    prod = s.read(production)
    assert prod['verified'] is True and prod['verification']['proof_sha256'] == PROOF66_SHA
    assert pins[str(rows66)] == prod['public_rows_sha256']
    s.write_json(output / 'source_pins.json', pins)
    case66 = runtime / 'event66'
    case66.mkdir()
    for name in [*(n + '.ct' for n in s.NAMES), 'source_event.json']:
        shutil.copyfile(origin66 / name, case66 / name)
    shutil.copyfile(rows66, case66 / 'public_ntt_rows.json')
    assert all(s.sha((case66 / (n + '.ct')).read_bytes()) == prod['inputs'][n + '.ct']['sha256'] for n in s.NAMES)

    def command(argv):
        before = time.monotonic_ns()
        p = subprocess.run([str(x) for x in argv], cwd=HERE, capture_output=True, timeout=40,
                           env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1', RAYON_NUM_THREADS='4'))
        record = {'argv': [str(x) for x in argv], 'exit_code': p.returncode,
                  'elapsed_ns': time.monotonic_ns() - before, 'stdout': p.stdout.decode(), 'stderr': p.stderr.decode()}
        commands.append(record)
        s.write_json(output / 'commands.json', commands)
        assert p.returncode == 0, record
        return s.parse(p.stdout)

    checkpoint, initial_files = output / 'checkpoint64.json', runtime / 'initial_files.json'
    imported = command([sys.executable, '-B', HERE / 'checkpoint_from_records.py', '--operations', operations,
        '--case', case65, '--case', case66, '--at', '64', '--out', checkpoint, '--initial-files', initial_files])
    assert imported['public_prefix_records'] == 64 and len(imported['selected_classes']) == 2
    cli = [sys.executable, '-B', HERE / 'service.py']
    initial = command([*cli, 'init', '--root', root, '--binary', binary, '--template', template,
        '--checkpoint', checkpoint, '--initial-files', initial_files, '--recipient', 'useful-learner-full-bfv-reader',
        '--expected-binary-sha256', BINARY_SHA, '--expected-template-sha256', TEMPLATE_SHA])
    bundle65, stale66 = runtime / 'event65.json', runtime / 'stale_event66.json'
    command([*cli, 'request', '--root', root, '--case', case65, '--proof', proof65,
             '--request-id', 'actual-learner-event-65', '--out', bundle65])
    command([*cli, 'request', '--root', root, '--case', case66, '--proof', proof66,
             '--request-id', 'stale-global-parent-event-66', '--out', stale66])
    with tempfile.TemporaryDirectory(prefix='vfhe-m-', dir='/tmp') as temporary:
        address = str(Path(temporary) / 'service.sock')
        child = None
        logs = []

        def start(number):
            nonlocal child
            argv = [str(x) for x in [*cli, 'serve', '--root', root, '--socket', address]]
            stderr = open(output / f'server{number}.stderr.txt', 'wb')
            logs.append(stderr)
            child = subprocess.Popen(argv, cwd=HERE, stdout=subprocess.PIPE, stderr=stderr,
                env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1', RAYON_NUM_THREADS='4'))
            with selectors.DefaultSelector() as selector:
                selector.register(child.stdout, selectors.EVENT_READ)
                assert selector.select(20), 'server readiness timeout'
                line = child.stdout.readline()
            ready = s.parse(line)
            assert ready['ready'] is True and ready['genesis'] == initial['genesis']
            messages.append({'action': 'start', 'process': number, 'pid': child.pid, 'argv': argv, 'ready': ready})

        def call(label, message):
            result = s.rpc(address, message)
            messages.append({'action': 'rpc', 'label': label, 'request': message, 'response': result})
            s.write_json(output / 'public_rpc.json', messages)
            return result

        def stop(number):
            nonlocal child
            child.terminate()
            result = child.wait(timeout=40)
            assert result == 0 and not Path(address).exists(), 'clean service shutdown'
            messages.append({'action': 'stop', 'process': number, 'exit_code': result, 'socket_absent': True})
            child.stdout.close()
            child = None

        def transition(before, after, accepted, label, event, proof_sha):
            assert accepted['ok'] is True and accepted['status'] == 'accepted' and accepted['proof_reexecuted'] is True
            b, a, receipt = before['head'], after['head'], accepted['receipt']
            assert a['revision'] == b['revision'] + 1 and a['learner_event'] == event
            assert set(a['classes']) == set(b['classes']) and a['model_root'] == s.model_root(a['classes'])
            assert receipt['previous_model_root'] == b['model_root'] and receipt['next_model_root'] == a['model_root']
            assert receipt['changed_class'] == label and receipt['proof_acceptance']['proof_sha256'] == proof_sha
            assert receipt['parent_checked_inside_commit'] is True
            assert a['classes'][label] == {'acc_sha256': receipt['request']['payloads']['out'], 'learner_event': event}
            assert all(a['classes'][key] == b['classes'][key] for key in a['classes'] if key != label)

        try:
            start(1)
            before = call('checkpoint_head', {'op': 'head'})
            assert before == initial and before['head']['learner_event'] == 64
            accepted65 = call('actual_event65_card_arrival', {'op': 'submit', 'bundle': str(bundle65)})
            after65 = call('model_after_event65', {'op': 'head'})
            transition(before, after65, accepted65, 'card_arrival', 65, PROOF65_SHA)
            refused = call('event66_with_stale_global_parent', {'op': 'submit', 'bundle': str(stale66)})
            assert refused['ok'] is False and refused['code'] == 'stale_parent'
            assert call('head_after_refusal', {'op': 'head'}) == after65
            bundle66 = runtime / 'event66.json'
            command([*cli, 'request', '--root', root, '--case', case66, '--proof', proof66,
                     '--request-id', 'actual-learner-event-66', '--out', bundle66])
            accepted66 = call('actual_event66_cash_withdrawal_charge', {'op': 'submit', 'bundle': str(bundle66)})
            after66 = call('model_after_event66', {'op': 'head'})
            transition(after65, after66, accepted66, 'cash_withdrawal_charge', 66, PROOF66_SHA)
            stop(1)
            start(2)
            reopened = call('reopened_model_head', {'op': 'head'})
            assert reopened == after66
            retry = call('historical_event65_retry', {'op': 'submit', 'bundle': str(bundle65)})
            assert retry['status'] == 'replayed' and retry['proof_reexecuted'] is False
            assert retry['receipt'] == accepted65['receipt'] and retry['receipt_sha256'] == accepted65['receipt_sha256']
            history = call('durable_history', {'op': 'history'})
            assert history['receipts'] == [accepted65['receipt'], accepted66['receipt']]
            assert call('head_after_retry', {'op': 'head'}) == reopened
            stop(2)
        finally:
            if child is not None and child.poll() is None:
                child.terminate()
                try:
                    child.wait(timeout=40)
                except subprocess.TimeoutExpired:
                    child.kill()
                    child.wait(timeout=10)
            for stream in logs:
                stream.close()
        s.write_json(output / 'public_rpc.json', messages)
    assert all(s.sha(Path(p).read_bytes()) == h for p, h in pins.items())
    for path in [bundle65, bundle66, stale66]:
        shutil.copyfile(path, output / path.name)
    shutil.copyfile(root / 'genesis.json', output / 'genesis.json')
    for name, value in [('receipt65', accepted65['receipt']), ('receipt66', accepted66['receipt']),
                        ('head64', before), ('head65', after65), ('head66', after66), ('history', history)]:
        s.write_json(output / (name + '.json'), value)
    result = {'schema': 'proved-multiclass-journal-demo-v1',
        'claim': 'EXECUTED consecutive actual learner updates in a durable global model journal',
        'completed_utc': datetime.now(timezone.utc).isoformat(), 'elapsed_ns': time.monotonic_ns() - started,
        'imported_checkpoint_event': 64, 'checkpoint_classes': sorted(before['head']['classes']),
        'imported_history_arithmetic_proved_here': False, 'accepted_learner_events': [65, 66],
        'accepted_updates': 2, 'native_proof_verifications': 2, 'rows_per_update': 8192,
        'rns_equations_per_update': 16384, 'journal_revision': 2, 'journal_receipts': 2,
        'exactly_one_class_changed_each_time': True, 'model_root_bound_each_receipt': True,
        'stale_global_parent_refused': True, 'refusal_preserved_head': True,
        'reopened_exact_global_head': True, 'historical_retry_same_receipt_without_proof_execution': True,
        'all_service_processes_closed': True, 'source_and_input_posthashes_match': True,
        'genesis': initial['genesis'], 'model_roots': [x['head']['model_root'] for x in [before, after65, after66]],
        'receipts': [accepted65['receipt_sha256'], accepted66['receipt_sha256']],
        'public_only': True, 'secret_key_reads': 0, 'private_comparisons': 0,
        'scope': 'Two-class imported checkpoint; earlier history is not proved. Arithmetic proof acceptance gates each class replacement and global parent commit under explicit parser/protocol TCB. Full BFV reader survives; no confidentiality claim.'}
    s.write_json(output / 'RESULT.json', result)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
