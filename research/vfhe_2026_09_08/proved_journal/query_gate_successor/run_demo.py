#!/usr/bin/env python3
"""Two genuine classes, two fresh query proofs, then the first private receive."""
import argparse
import collections
import contextlib
import copy
from datetime import datetime, timezone
import json
from pathlib import Path
import shutil
import sys
import time

import gate
from gate import j

HERE = Path(__file__).resolve().parent
TEACHES = [
    ('card_arrival', 'My replacement bank card has still not arrived after three weeks.'),
    ('cash_withdrawal_charge', 'A cash machine charged an extra fee when I withdrew money from my account.'),
]
QUERY = 'Why was I charged a fee for taking cash out at an ATM?'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--run', default='gated001')
    args = parser.parse_args()
    assert args.run.isalnum()
    output, root = HERE / 'results' / args.run, HERE / 'runtime' / args.run
    assert not output.exists() and not root.exists()
    output.mkdir(parents=True)
    started = time.monotonic_ns()
    j.write_json(output / 'command.json', {'argv': [sys.executable, '-B', str(Path(__file__)), '--run', args.run],
        'teaches': [{'label': c, 'text': t} for c, t in TEACHES], 'query': QUERY,
        'source_sha256': j.sha(Path(__file__).read_bytes()), 'started_utc': datetime.now(timezone.utc).isoformat(),
        'historical_live001_scope': 'Already decrypted predecessor preserved; this is a fresh isolated query/state/key.'})
    gate.create(root, [c for c, _ in TEACHES])
    service = gate.QueryGate(root)
    teaches = []
    for i, (label, text) in enumerate(TEACHES):
        print(json.dumps({'phase': 'new-proved-teach', 'class': label}), file=sys.stderr, flush=True)
        teaches.append(service.model.teach(label, text, 'teach' + str(i)))
        j.write_json(output / 'teaches.json', teaches)
    committed = service.model.status()
    assert committed['head']['head']['revision'] == 2 and committed['counts'] == {c: 1 for c, _ in TEACHES}

    def operations():
        return [json.loads(line) for line in (service.model.root / 'issuer/operations.jsonl').read_text().splitlines()]

    def private_count():
        return sum(row['command'] == 'reader-decrypt' for row in operations())

    assert private_count() == 0
    prepared = service.prepare(QUERY, 'new-two-class-query')
    assert len(prepared['request']['active_classes']) == 2 and private_count() == 0
    j.write_json(output / 'prepared.json', prepared)
    bad = copy.deepcopy(j.read(Path(prepared['bundle'])))
    omitted = 'cash_withdrawal_charge'
    bad['request']['request_id'] = 'missing-active-class'
    bad['request']['active_classes'].remove(omitted)
    del bad['request']['classes'][omitted]
    del bad['request']['counts'][omitted]
    del bad['files'][omitted]
    bad_path = root / 'missing_active_class.json'
    j.write_json(bad_path, bad)
    refusal = None
    try:
        service.accept(bad_path)
    except j.Refused as e:
        refusal = {'ok': False, 'code': e.code}
    assert refusal == {'ok': False, 'code': 'active_class_coverage'}
    assert private_count() == 0 and service.model.status() == committed
    assert not (root / 'queries/missing-active-class/public_acceptance.json').exists()
    j.write_json(output / 'coverage_refusal.json', {'request': bad['request'], 'refusal': refusal,
        'head_unchanged': True, 'private_receive_calls': private_count(), 'public_acceptance_absent': True})
    accepted = service.accept(Path(prepared['bundle']))
    assert set(accepted['native_acceptances']) == {c for c, _ in TEACHES}
    assert private_count() == 0 and accepted['private_receive_calls'] == 0
    j.write_json(output / 'public_acceptance.json', accepted)
    print(json.dumps({'phase': 'all-active-proofs-accepted', 'private_receive_calls': 0}), file=sys.stderr, flush=True)
    answer = service.receive('new-two-class-query')
    assert private_count() == 2 and len(answer['answer']['ranking']) == 2
    assert answer['head'] == committed['head'] and answer['answer']['revision'] == 2
    # Independent integer computation is deliberately after private receipt.
    with contextlib.redirect_stdout(sys.stderr):
        vectors = service.model.encoder.encode([t for _, t in TEACHES] + [QUERY]).tolist()
    expected = {label: sum(a * b for a, b in zip(vector, vectors[-1]))
                for (label, _), vector in zip(TEACHES, vectors[:-1])}
    actual = {entry['label']: entry['sum_dot'] for entry in answer['answer']['ranking']}
    assert actual == expected
    expected_label = sorted(expected, key=lambda label: (-expected[label], label))[0]
    assert answer['answer']['label'] == expected_label
    assert service.model.encoder.stats['encoded_texts'] == 3
    reopened = gate.QueryGate(root).model.status()
    assert reopened == committed
    service.check_pins(); service.model.check_pins()
    query_dir = service.directory('new-two-class-query')
    for name, source in {'query_genesis.json': root / 'query_genesis.json',
        'model_config.json': service.model.root / 'config.json', 'model_checkpoint.json': service.model.root / 'checkpoint.json',
        'model_genesis.json': service.model.root / 'journal/genesis.json',
        'request.json': query_dir / 'request.json', 'query.json': query_dir / 'query.json',
        'public_operations.jsonl': service.model.root / 'issuer/operations.jsonl'}.items():
        shutil.copyfile(source, output / name)
    # Explicit public allowlist; no private keys/features or large witness traces.
    jobs = []
    for index, label in enumerate(prepared['request']['active_classes']):
        source = query_dir / ('proof' + str(index)); dest = output / ('class' + str(index)); dest.mkdir()
        for name in ('result.json', 'export.command.json', 'export.stdout', 'export.stderr', 'emit.command.json', 'emit.stdout', 'emit.stderr',
                     'prove.command.json', 'prove.stdout', 'prove.stderr', 'verify.command.json', 'verify.stdout', 'verify.stderr'):
            shutil.copyfile(source / name, dest / name)
        (dest / 'case').mkdir(); (dest / 'proof').mkdir()
        for name in ('acc.ct', 'query.json', 'out.ct', 'public_rows.json', 'operation.json', 'positive.poly', 'negative.poly'):
            shutil.copyfile(source / 'case' / name, dest / 'case' / name)
        for name in ('proof.bin', 'proof.json'):
            shutil.copyfile(source / 'proof' / name, dest / 'proof' / name)
        for prefix in ('pipeline', 'gate_export', 'gate_verify'):
            for suffix in ('.command.json', '.stdout', '.stderr'):
                shutil.copyfile(query_dir / (prefix + str(index) + suffix), dest / (prefix + suffix))
        result = j.read(source / 'result.json')
        jobs.append({'class': label, 'proof_sha256': j.sha((dest / 'proof/proof.bin').read_bytes()),
            'proof_bytes': (dest / 'proof/proof.bin').stat().st_size, 'pipeline_seconds': result['elapsed_seconds'],
            'native_verification': accepted['native_acceptances'][label], 'case_acc_sha256': j.sha((dest / 'case/acc.ct').read_bytes()),
            'out_sha256': j.sha((dest / 'case/out.ct').read_bytes())})
    # Retain both actual new teaching proof records establishing these heads.
    for index in range(2):
        source = service.model.root / 'proposals' / ('teach' + str(index))
        dest = output / ('teach' + str(index)); dest.mkdir()
        for name, path in {'committed.json': source / 'committed.json', 'source_event.json': source / 'candidate/source_event.json',
            'request.json': source / 'request.json', 'pipeline_command.json': source / 'pipeline_command.json',
            'pipeline_result.json': source / 'proved/result.json', 'proof.bin': source / 'proved/proof/proof.bin',
            'proof.json': source / 'proved/proof/proof.json'}.items():
            shutil.copyfile(path, dest / name)
    for name, value in [('answer', answer), ('committed_head', committed), ('model_history', service.model.service.dispatch({'op': 'history'})),
                        ('encoder_stats', service.model.encoder.stats), ('integer_comparison_after_receive', {'expected': expected, 'actual': actual, 'match': True})]:
        j.write_json(output / (name + '.json'), value)
    result = {'schema': 'two-active-class-query-gate-demo-v1', 'claim': 'EXECUTED fresh all-active-class query proof gate before private receive',
        'completed_utc': datetime.now(timezone.utc).isoformat(), 'elapsed_ns': time.monotonic_ns() - started,
        'fresh_isolated_instance': True, 'new_proved_teaches': 2, 'active_classes': 2, 'new_query_proofs': 2,
        'proof_jobs': jobs, 'all_active_classes_verified_before_receive': True,
        'private_receive_calls_before_public_acceptance': 0, 'private_receive_calls_after_acceptance': 2,
        'coverage_refusal': refusal['code'], 'coverage_refusal_preserved_head_and_no_receive': True,
        'accepted_model_revision': 2, 'exact_head_reopen': True,
        'query_label': answer['answer']['label'], 'actual_scores': actual, 'post_receive_integer_comparisons_match': True,
        'encoder_new_texts': 3, 'model_loaded_once': True, 'full_reader_survives': True,
        'scope': 'Actual fresh two-class mechanics/semantic fixture, not an accuracy benchmark. Proof covers both ct×pt products and final subtraction; plaintext encoder, query/NTT parsing, metadata/global-head gate, decoder and OS remain TCB. No decryption restriction/confidentiality claim.'}
    j.write_json(output / 'RESULT.json', result)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
