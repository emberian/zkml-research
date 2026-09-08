#!/usr/bin/env python3
"""Run the real event-65 public proof gate, refusal, process reopen and retry."""
from __future__ import annotations
import argparse
import copy
from datetime import datetime, timezone
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
BASE = HERE.parent
BINARY_SHA = 'dd41ec2eac52bf35ff8a9c6e736fa4dcb7cb4ae41cec6bace5cf593a3cf87cc6'
TEMPLATE_SHA = '1afc2b3a120f59fdd79d273c6d32887373c5718225cb6e94b82a7231010c3aa7'
PROOF_SHA = 'acf747cf42eff8171b2b774abae5572e8d7bdb7ace144754c7605128c15e5ba6'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', default='demo001')
    args = parser.parse_args()
    assert args.run.isalnum()
    output, runtime = HERE / 'results' / args.run, HERE / 'runtime' / args.run
    assert not output.exists() and not runtime.exists()
    output.mkdir(parents=True)
    runtime.mkdir(parents=True, mode=0o700)
    root = runtime / 'service'
    binary = BASE / 'proved_operation/target/release/vfhe-proved-operation'
    template = BASE / 'arithmetic_coverage/artifacts_expiry/template_ir2.json'
    case = BASE / 'proved_operation/results/learner_expiry001'
    proof = BASE / 'proved_operation/results/expiry_proof001/proof.bin'
    started = time.monotonic_ns()
    commands, messages = [], []
    source_pins = {str(p): s.sha(p.read_bytes()) for p in [HERE / 'service.py', Path(__file__), binary, template, proof,
        *[case / (n + '.ct') for n in s.NAMES], case / 'source_event.json', case / 'public_ntt_rows.json']}
    assert source_pins[str(binary)] == BINARY_SHA
    assert source_pins[str(template)] == TEMPLATE_SHA
    assert source_pins[str(proof)] == PROOF_SHA
    s.write_json(output / 'source_pins.json', source_pins)

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

    cli = [sys.executable, '-B', HERE / 'service.py']
    initial = command([*cli, 'init', '--root', root, '--binary', binary, '--template', template,
        '--initial', case / 'acc.ct', '--recipient', 'useful-learner-full-bfv-reader', '--learner-class', 'card_arrival',
        '--learner-event', '29', '--expected-binary-sha256', BINARY_SHA, '--expected-template-sha256', TEMPLATE_SHA])
    valid_bundle = runtime / 'valid_bundle.json'
    command([*cli, 'request', '--root', root, '--case', case, '--proof', proof,
             '--request-id', 'actual-learner-event-65', '--out', valid_bundle])
    # A canonical but different output, with matching candidate rows and metadata,
    # reaches the actual proof verifier rather than failing only a stale file hash.
    wrong = runtime / 'changed_output_candidate'
    wrong.mkdir()
    for name in s.NAMES:
        shutil.copyfile(case / (name + '.ct'), wrong / (name + '.ct'))
    shutil.copyfile(case / 'fresh.ct', wrong / 'out.ct')
    candidate = s.read(case / 'source_event.json')
    candidate['files']['out']['sha256'] = s.sha((wrong / 'out.ct').read_bytes())
    candidate['scope'] = 'Deliberately changed-output candidate for native proof refusal; not an authentic learner event.'
    s.write_json(wrong / 'source_event.json', candidate)
    command([binary, 'export-update-ntt', wrong])
    wrong_bundle = runtime / 'wrong_bundle.json'
    command([*cli, 'request', '--root', root, '--case', wrong, '--proof', proof,
             '--request-id', 'changed-output-refusal', '--out', wrong_bundle])
    for path in [valid_bundle, wrong_bundle]:
        shutil.copyfile(path, output / path.name)
    shutil.copyfile(wrong / 'source_event.json', output / 'changed_output_source_event.json')

    with tempfile.TemporaryDirectory(prefix='vfhe-j-', dir='/tmp') as temporary:
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

        try:
            start(1)
            before = call('initial_head', {'op': 'head'})
            assert before == initial
            refused = call('changed_output_with_original_proof', {'op': 'submit', 'bundle': str(wrong_bundle)})
            assert refused['ok'] is False and refused['code'] == 'native_proof_rejected', refused
            unchanged = call('head_after_refusal', {'op': 'head'})
            assert unchanged == before
            accepted = call('actual_event_65', {'op': 'submit', 'bundle': str(valid_bundle)})
            assert accepted['ok'] is True and accepted['status'] == 'accepted' and accepted['proof_reexecuted'] is True
            committed = call('committed_head', {'op': 'head'})
            assert committed['head']['revision'] == 1 and committed['head']['learner_event'] == 65
            assert committed['head']['acc_sha256'] == source_pins[str(case / 'out.ct')]
            # A distinct request cannot reuse the old parent after that commit.
            stale = copy.deepcopy(s.read(valid_bundle))
            stale['request']['request_id'] = 'old-parent-distinct-request'
            stale_bundle = runtime / 'stale_bundle.json'
            s.write_json(stale_bundle, stale)
            stale_result = call('stale_parent', {'op': 'submit', 'bundle': str(stale_bundle)})
            assert stale_result['ok'] is False and stale_result['code'] == 'stale_parent'
            stop(1)
            start(2)
            reopened = call('reopened_head', {'op': 'head'})
            assert reopened == committed
            retried = call('exact_retry_after_reopen', {'op': 'submit', 'bundle': str(valid_bundle)})
            assert retried['status'] == 'replayed' and retried['proof_reexecuted'] is False
            assert retried['receipt_sha256'] == accepted['receipt_sha256'] and retried['receipt'] == accepted['receipt']
            history = call('durable_history', {'op': 'history'})
            assert history['receipts'] == [accepted['receipt']]
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
    assert all(s.sha(Path(p).read_bytes()) == h for p, h in source_pins.items())
    shutil.copyfile(root / 'genesis.json', output / 'genesis.json')
    s.write_json(output / 'receipt.json', accepted['receipt'])
    s.write_json(output / 'final_head.json', reopened)
    s.write_json(output / 'history.json', history)
    result = {'schema': 'proved-journal-demo-v1', 'claim': 'EXECUTED public native proof gate and durable local journal',
        'completed_utc': datetime.now(timezone.utc).isoformat(), 'elapsed_ns': time.monotonic_ns() - started,
        'accepted_updates': 1, 'learner_event': 65, 'journal_revision': 1,
        'rows': 8192, 'rns_equations': 16384, 'proof_bytes': proof.stat().st_size,
        'changed_output_refused_by_actual_proof_verifier': True, 'refusal_preserved_head': True,
        'stale_parent_refused': True, 'process_reopen_exact_head': True,
        'retry_same_receipt_without_new_proof_execution': True, 'journal_receipts': len(history['receipts']),
        'all_service_processes_closed': True, 'source_and_public_input_posthashes_match': True,
        'genesis': initial['genesis'], 'receipt_sha256': accepted['receipt_sha256'],
        'public_only': True, 'secret_key_reads': 0, 'private_comparisons': 0,
        'scope': 'Fixed approved template and actual ciphertext relation. Metadata/authorization, canonical parsers and durable commit are protocol TCB. Full BFV reader survives. No confidentiality, FIFO/encoder proof or hostile-OS claim.'}
    s.write_json(output / 'RESULT.json', result)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
