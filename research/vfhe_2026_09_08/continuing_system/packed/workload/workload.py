#!/usr/bin/env python3
"""Frozen nine-class, two-bank lifecycle. --prepare encodes once; root launches --run.

Every crypto operation executes in its own OS process against packed.core.Live.
--resume preserves stable request IDs and completed results. It may adopt a
matching externally initialized revision-zero instance without another keygen.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
APP = HERE.parent
REPO = next(p for p in HERE.parents if (p / 'AGENTS.md').is_file())
CORPUS = HERE / 'corpus.json'
PREPARED = HERE / 'prepared'
HELPER = REPO / 'research/vfhe_2026_09_08/proved_journal/live_nonlinear/fixture_builder/helper.py'


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def read(path):
    return json.loads(Path(path).read_text())


def write(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temp = path.with_name(path.name + '.tmp')
    temp.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temp.replace(path)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def utc():
    return datetime.now(timezone.utc).isoformat()


def corpus():
    data = read(CORPUS)
    rows = data['training'] + data['held_out']
    need(len({r['id'] for r in rows}) == len(rows), 'Duplicate corpus ID.')
    need(len({r['text'] for r in rows}) == len(rows), 'Teaching and held-out text overlap.')
    need(len(set(data['classes'])) == len(data['classes']), 'Repeated class label.')
    need(all(r['label'] in data['classes'] for r in rows), 'Unknown corpus class.')
    return data


def empty_model(data):
    return {label: {'bank': str(i // 8), 'lane': i % 8, 'teaches': 0, 'queue': []}
            for i, label in enumerate(data['classes'])}


def answer(model, query, vectors, data):
    classes, banks = {}, {}
    for label, entry in model.items():
        count = len(entry['queue'])
        if not count:
            continue
        parts = [sum(a * b for a, b in zip(vectors[item['text_id']], query))
                 for item in entry['queue']]
        need(all(abs(v) <= 20000 for v in parts), 'Individual reference dot exceeds fixed domain.')
        total = sum(parts)
        need(abs(total) <= count * 20000, 'Class sum exceeds the reader bound.')
        row = {'bank': entry['bank'], 'lane': entry['lane'], 'count': count,
               'sum_dot': total, 'mean_numerator': total, 'mean_denominator': count}
        classes[label] = row
        bank = banks.setdefault(entry['bank'], {'class_sums': [0] * 8, 'counts': [0] * 8})
        bank['class_sums'][entry['lane']] = total
        bank['counts'][entry['lane']] = count
    for bank in banks.values():
        bank['signed_sum'] = sum(bank['class_sums'])
        bank['per_class_signed_bounds'] = [count * 20000 for count in bank['counts']]
        need(abs(bank['signed_sum']) < data['plaintext_modulus'] // 2, 'Bank sum exceeds centered domain.')
    ranking = sorted(classes, key=lambda label: (-Fraction(classes[label]['sum_dot'], classes[label]['count']), label))
    return {'classes': classes, 'banks': banks, 'counts': {c: v['count'] for c, v in classes.items()},
            'ranking': ranking, 'prediction': ranking[0]}


def evaluate(model, data, vectors):
    rows = []
    for item in data['held_out']:
        prediction = answer(model, vectors[item['id']], vectors, data)
        rows.append({'id': item['id'], 'label': item['label'],
                     'label_has_teaching': bool(model[item['label']]['queue']),
                     'prediction': prediction['prediction'], 'ranking': prediction['ranking']})
    count = len(rows)
    correct = sum(row['label'] == row['prediction'] for row in rows)
    active_rows = [row for row in rows if row['label_has_teaching']]
    return {'examples': count, 'correct': correct, 'accuracy': correct / count,
            'active_label_examples': len(active_rows),
            'active_label_correct': sum(row['label'] == row['prediction'] for row in active_rows),
            'active_classes': sum(bool(v['queue']) for v in model.values()),
            'active_banks': len({v['bank'] for v in model.values() if v['queue']}), 'rows': rows}


def build_reference(data, vectors):
    need(set(vectors) == {x['id'] for x in data['training'] + data['held_out']}, 'Vector IDs differ.')
    for vector in vectors.values():
        need(len(vector) == 576 and all(type(v) is int and abs(v) <= 32 for v in vector)
             and sum(v * v for v in vector) <= 20000, 'Vector leaves the fixed E5 domain.')
    model = empty_model(data)
    texts = {r['id']: r for r in data['training'] + data['held_out']}
    operations, checkpoints, expired = {}, {}, []
    revision = 0
    for operation in data['operations']:
        record = {'kind': operation['kind']}
        if operation['kind'] == 'teach':
            item = texts[operation['text_id']]
            entry = model[item['label']]
            old = entry['queue'].pop(0) if len(entry['queue']) == data['capacity'] else None
            entry['queue'].append({'text_id': item['id'], 'lane': entry['lane']})
            entry['teaches'] += 1
            revision += 1
            record.update(label=item['label'], bank=entry['bank'], lane=entry['lane'], expired=old)
            if old:
                expired.append({'operation': operation['id'], 'label': item['label'], **old})
        if operation['kind'] == 'query':
            record['answer'] = answer(model, vectors[operation['text_id']], vectors, data)
        checkpoint = operation.get('checkpoint', operation.get('plaintext_checkpoint'))
        if checkpoint:
            checkpoints[checkpoint] = evaluate(model, data, vectors)
        record.update(revision=revision, model=json.loads(json.dumps(model)))
        operations[operation['id']] = record
    baseline = checkpoints['one_bank']
    counts = Counter(row['label'] for row in data['held_out'])
    majority = sorted(counts, key=lambda c: (-counts[c], c))[0]
    for row in checkpoints.values():
        row.update(frozen_initial_correct=baseline['correct'], frozen_initial_accuracy=baseline['accuracy'],
                   majority_label=majority, majority_correct=counts[majority], majority_accuracy=counts[majority] / sum(counts.values()))
    return {'schema': 'packed-class-lifecycle-reference-v1', 'score': 'exact signed class sum/count',
            'operations': operations, 'checkpoints': checkpoints, 'expired_examples': expired,
            'final_model': model, 'final_revision': revision,
            'scope': data['evaluation_policy']['scope']}


def load_prepared(directory):
    directory = Path(directory).resolve()
    record = read(directory / 'preparation.json')
    need(record['corpus_sha256'] == digest(CORPUS), 'Prepared corpus changed.')
    need(record['vectors_sha256'] == digest(directory / 'vectors.json'), 'Prepared vectors changed.')
    need(record['reference_sha256'] == digest(directory / 'reference.json'), 'Prepared reference changed.')
    return directory, record, read(directory / 'vectors.json'), read(directory / 'reference.json')


def prepare(directory):
    directory = Path(directory).resolve()
    if (directory / 'preparation.json').exists():
        return {**load_prepared(directory)[1], 'preparation_reused': True}
    directory.mkdir(parents=True, exist_ok=True)
    data = corpus()
    corpus_hash = digest(CORPUS)
    write(directory / 'frozen_corpus.json', data)
    module_spec = importlib.util.spec_from_file_location('packed_workload_e5', HELPER)
    module = importlib.util.module_from_spec(module_spec)
    module_spec.loader.exec_module(module)
    encoder = module.TextEncoder(directory / 'encoder_cache')
    started = time.perf_counter()
    rows = data['training'] + data['held_out']
    features = encoder.encode([row['text'] for row in rows])
    need(digest(CORPUS) == corpus_hash, 'Corpus changed during encoding.')
    vectors = {row['id']: vector for row, vector in zip(rows, features)}
    reference = build_reference(data, vectors)
    write(directory / 'vectors.json', vectors)
    write(directory / 'reference.json', reference)
    record = {'schema': 'packed-class-lifecycle-preparation-v1', 'prepared_utc': utc(),
              'corpus_sha256': corpus_hash, 'encoder_helper_sha256': digest(HELPER),
              'vectors_sha256': digest(directory / 'vectors.json'),
              'reference_sha256': digest(directory / 'reference.json'),
              'training_texts': len(data['training']), 'held_out_texts': len(data['held_out']),
              'elapsed_seconds': time.perf_counter() - started, 'encoder_stats': encoder.stats,
              'maximum_abs_coordinate': max(abs(v) for vector in features for v in vector),
              'maximum_squared_norm': max(sum(v * v for v in vector) for vector in features),
              'cryptographic_operations': 0, 'preparation_reused': False,
              'checkpoints': {k: {a: b for a, b in v.items() if a != 'rows'} for k, v in reference['checkpoints'].items()},
              'expired_examples': reference['expired_examples']}
    write(directory / 'preparation.json', record)
    report(directory, reference)
    return record


def check_head(head, expected):
    need(head['revision'] == expected['revision'], 'Durable revision differs from reference.')
    need(set(head['classes']) == set(expected['model']), 'Durable class set differs.')
    for label, row in expected['model'].items():
        actual = head['classes'][label]
        need(str(actual['bank']) == row['bank'] and actual['lane'] == row['lane'], 'Class layout changed.')
        need(actual['teaches'] == row['teaches'], 'Teaching count differs.')
        need(len(actual['queue']) == len(row['queue']), 'Retained example count differs.')
        need([v['lane'] for v in actual['queue']] == [v['lane'] for v in row['queue']], 'FIFO class lane differs.')


def check_answer(result, expected):
    wanted = expected['answer']
    need(result.get('public_accepted') is True and result.get('accepted_all_banks') is True,
         'A bank was read without complete public acceptance.')
    need(result['revision'] == expected['revision'], 'Query revision differs.')
    need(result['counts'] == wanted['counts'], 'Class counts differ.')
    need(result['ranking'] == wanted['ranking'] and result['prediction'] == wanted['prediction'], 'Exact mean ranking differs.')
    need(set(result['classes']) == set(wanted['classes']), 'Returned class set differs.')
    need(set(result['banks']) == set(wanted['banks']), 'Active bank set differs.')
    need(result['private_reads'] == len(wanted['banks']), 'Private read count differs from occupied banks.')
    for label, row in wanted['classes'].items():
        actual = result['classes'][label]
        for key in ('lane', 'count', 'sum_dot', 'mean_numerator', 'mean_denominator'):
            need(actual[key] == row[key], f'{label}: {key} differs.')
        need(str(actual['bank']) == row['bank'] and actual['sum_score'] == row['sum_dot'], 'Class score/layout alias differs.')
    for bank_id, row in wanted['banks'].items():
        actual = result['banks'][bank_id]
        for key in ('class_sums', 'counts', 'signed_sum', 'per_class_signed_bounds'):
            need(actual[key] == row[key], f'Bank {bank_id}: {key} differs.')
        need(actual['sum_values'] == row['class_sums'], 'Reader sum alias differs.')
        need(actual.get('all8192_slots_repeat8') is True and actual.get('zero_empty_lanes') is True,
             'Reader did not validate repetition and empty lanes.')
    return {'every_decrypted_class_sum_equal': True, 'compared_bank_lanes': 8 * len(wanted['banks']),
            'active_banks': len(wanted['banks']), 'active_classes': len(wanted['classes']),
            'private_bank_reads': result['private_reads'],
            'counts_equal': True, 'empty_and_padding_lanes_equal': True,
            'reader_checked_repeat8': True, 'all_banks_accepted_before_read': True,
            'exact_rational_ranking_equal': True}


def worker(spec_path):
    job = read(spec_path)
    sys.path.insert(0, str(APP))
    import core
    started = time.perf_counter()
    operation = job['operation']
    root = Path(job['root'])
    if operation['kind'] == 'init':
        result = core.initialize(root, job['classes'])
    else:
        live = core.Live(root)
        if operation['kind'] == 'teach':
            result = live.teach_vector(job['label'], job['vector'], job['text'], operation['id'])
        elif operation['kind'] == 'query':
            result = live.query_vector(job['vector'], job['text'], operation['id'])
        else:
            result = {'head': live.head(), 'reopened': True}
    engine = core.metadata(root) if hasattr(core, 'metadata') else core.Live(root).metadata()
    envelope = {'result': result, 'engine': engine, 'process': {'pid': os.getpid(), 'ppid': os.getppid(),
                'elapsed_seconds': time.perf_counter() - started, 'finished_utc': utc()}}
    write(job['result_path'], envelope)
    print(json.dumps({'operation': operation['id'], 'complete': True, 'pid': os.getpid()}), flush=True)


def invoke(controller, root, operation, payload):
    folder = controller / 'steps' / operation['id']
    folder.mkdir(parents=True, exist_ok=True)
    number = len(list(folder.glob('attempt-*.json'))) + 1
    prefix = folder / f'attempt-{number:03}'
    output = folder / 'worker_result.json'
    spec = folder / 'input.json'
    write(spec, {'root': str(root), 'operation': operation, 'result_path': str(output), **payload})
    argv = [sys.executable, '-u', '-B', str(Path(__file__).resolve()), '--worker', str(spec)]
    started = time.perf_counter()
    record = {'argv': argv, 'started_utc': utc(), 'attempt': number, 'status': 'running'}
    with prefix.with_suffix('.stdout').open('wb') as stdout, prefix.with_suffix('.stderr').open('wb') as stderr:
        process = subprocess.Popen(argv, stdout=stdout, stderr=stderr, start_new_session=True,
                                   env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'})
        record['pid'] = process.pid
        write(prefix.with_suffix('.json'), record)
        print(json.dumps({'operation': operation['id'], 'status': 'running', 'pid': process.pid,
                          'stderr': str(prefix.with_suffix('.stderr'))}), flush=True)
        try:
            code = process.wait()
        except BaseException:
            record.update(status='controller_interrupted', observed_utc=utc())
            write(prefix.with_suffix('.json'), record)
            raise
    record.update(status='completed' if code == 0 else 'failed', returncode=code,
                  elapsed_seconds=time.perf_counter() - started, finished_utc=utc())
    write(prefix.with_suffix('.json'), record)
    need(code == 0, f'Operation {operation["id"]} failed; see {prefix}.stderr. Resume retains the request ID.')
    return read(output)


def live_pid(pid):
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


def summarize(controller, root, prepared, reference, data, invocation):
    metrics, phase_seconds = Counter(), Counter()
    queries, completed = [], []
    all_metrics = True
    for operation in data['operations']:
        path = controller / 'steps' / operation['id'] / 'completed.json'
        if not path.exists():
            break
        entry = read(path)
        completed.append(operation['id'])
        result = entry['worker']['result']
        if operation['kind'] in ('teach', 'query'):
            values = result.get('metrics')
            if values is None:
                metric_path = root / ('teaching' if operation['kind'] == 'teach' else 'queries') / operation['id'] / 'metrics.json'
                values = read(metric_path) if metric_path.exists() else None
            if values is None:
                all_metrics = False
            else:
                for key in ('proofs_generated', 'accepted_fresh_proofs', 'proofs_verified', 'proof_bytes',
                            'committed_updates', 'answered_queries', 'private_reads', 'discarded_phase_attempts',
                            'classes_answered', 'occupied_banks'):
                    metrics[key] += values.get(key, 0)
                for key, value in values.get('phase_elapsed_seconds', {}).items():
                    if isinstance(value, (float, int)):
                        phase_seconds[key] += value
        if operation['kind'] == 'query':
            queries.append({'id': operation['id'], 'checkpoint': operation['checkpoint'],
                            'revision': result['revision'], 'prediction': result['prediction'],
                            'ranking': result['ranking'], 'checks': entry['checks'],
                            'worker_pid': entry['worker']['process']['pid']})
    attempts = [read(p) for p in (controller / 'steps').glob('*/attempt-*.json')]
    result = {'schema': 'packed-class-lifecycle-result-v1', 'updated_utc': utc(),
              'instance_root': str(root), 'controller_root': str(controller),
              'engine': read(controller / 'steps/initialize/completed.json')['worker']['engine'],
              'corpus_sha256': digest(CORPUS), 'vectors_sha256': digest(prepared / 'vectors.json'),
              'reference_sha256': digest(prepared / 'reference.json'),
              'completed_operations': len(completed), 'required_operations': len(data['operations']),
              'complete': len(completed) == len(data['operations']), 'queries': queries,
              'instance_cumulative_metrics': dict(metrics), 'phase_elapsed_seconds': dict(phase_seconds),
              'metrics_available_for_every_crypto_operation': all_metrics,
              'worker_attempt_wall_seconds': sum(v.get('elapsed_seconds', 0) for v in attempts),
              'worker_attempts_without_terminal_timing': sum('elapsed_seconds' not in v for v in attempts),
              'invocation': invocation, 'expired_reference_examples': reference['expired_examples'],
              'plaintext_utility': {k: {a: b for a, b in v.items() if a != 'rows'} for k, v in reference['checkpoints'].items()},
              'freshness_accounting': 'Actual metrics count each stable request once across invocations. Reused completed requests and resumed phases are not relabeled as new proofs.',
              'scope': data['evaluation_policy']['scope']}
    write(controller / 'RESULT.json', result)
    report(prepared, reference, result)
    return result


def report(prepared, reference, summary=None):
    preparation = read(Path(prepared) / 'preparation.json')
    lines = ['# Packed nine-class lifecycle workload', '',
             '[EXECUTED: plaintext preparation] Eighteen public authored teaching texts and nine held-out texts '
             'were frozen before one E5 encoding pass. Labels were not encoder inputs. There was no held-out tuning.', '',
             '| Checkpoint | Active classes / banks | Correct / 9 | Correct among active labels | Frozen first bank | Majority |',
             '|---|---:|---:|---:|---:|---:|']
    for name, row in reference['checkpoints'].items():
        lines.append(f"| {name} | {row['active_classes']} / {row['active_banks']} | {row['correct']}/9 | "
                     f"{row['active_label_correct']}/{row['active_label_examples']} | {row['frozen_initial_correct']}/9 | {row['majority_correct']}/9 |")
    lines.extend(['', '[DERIVED] The initial model has no network-transport teaching. Later teaching changes '
                  'both class membership and the proof-integrity FIFO. These finite observations establish no general '
                  'accuracy improvement. Reference class sums include exactly the last eight retained feature dots; '
                  'the first two proof-integrity texts expire.', '',
                  f"Corpus SHA256 `{preparation['corpus_sha256']}`; vectors SHA256 `{preparation['vectors_sha256']}`; "
                  f"reference SHA256 `{preparation['reference_sha256']}`.", '',
                  'Encoder statistics: `' + json.dumps(preparation['encoder_stats'], sort_keys=True) + '`.',
                  f"Preparation wall time: {preparation['elapsed_seconds']:.6f} seconds.", ''])
    if summary is None:
        lines.append('[OPEN] Root owns cryptographic launch. No encryption, key generation, proof or private read ran during preparation.')
    else:
        status = '[EXECUTED]' if summary['complete'] else '[EXECUTED: partial lifecycle]'
        lines.append(f"{status} {summary['completed_operations']}/{summary['required_operations']} operations complete. "
                     f"Evidence: `{summary['controller_root']}`. Worker-attempt wall seconds: {summary['worker_attempt_wall_seconds']:.6f}.")
        lines.extend(['', 'Actual unique-request metrics: `' + json.dumps(summary['instance_cumulative_metrics'], sort_keys=True) + '`.', ''])
        for query in summary['queries']:
            check = query['checks']
            lines.append(f"- `{query['id']}`: revision {query['revision']}, {check['active_banks']} active banks; "
                         f"all {check['compared_bank_lanes']} signed class-sum lanes, counts, padding, repeat8 and exact ranking matched; "
                         f"prediction `{query['prediction']}`; worker PID {query['worker_pid']}.")
        lines.extend(['', summary['freshness_accounting'], '',
                      '[DERIVED] The application retains the full BFV reader. Exact class sums and bank-level proof '
                      'gating demonstrate this workload, not absence of operator read authority.'])
    (HERE / 'evaluation.md').write_text('\n'.join(lines) + '\n')


def run(root, directory, resume):
    root = Path(root).resolve()
    controller = root.with_name(root.name + '.workload')
    prepared, preparation, vectors, reference = load_prepared(directory)
    data = corpus()
    texts = {row['id']: row for row in data['training'] + data['held_out']}
    identity = {'schema': 'packed-class-lifecycle-run-v1', 'root': str(root), 'prepared_dir': str(prepared),
                'corpus_sha256': digest(CORPUS), 'vectors_sha256': preparation['vectors_sha256'],
                'reference_sha256': preparation['reference_sha256'], 'class_order': data['classes']}
    adopts = root.exists() and not controller.exists()
    if resume and controller.is_dir():
        stored = read(controller / 'identity.json')
        need(all(stored.get(key) == value for key, value in identity.items()), 'Resume identity changed.')
    else:
        need(not controller.exists(), 'Existing controller requires --resume.')
        need(not resume or adopts, 'No controller or initialized instance exists to resume.')
        controller.mkdir(parents=True)
        write(controller / 'identity.json', {**identity, 'created_utc': utc(), 'adopts_preinitialized_instance': adopts})
    with (controller / 'driver.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        for path in (controller / 'steps').glob('*/attempt-*.json'):
            attempt = read(path)
            need(not (attempt.get('status') in ('running', 'controller_interrupted') and live_pid(attempt['pid'])),
                 f'Existing worker {attempt.get("pid")} remains live; observe it before resuming.')
        started = time.perf_counter()
        invocation = {'started_utc': utc(), 'mode': 'resume' if resume else 'run',
                      'reused_completed_steps': [], 'resumed_incomplete_steps': [], 'newly_completed_steps': []}
        initialization = controller / 'steps/initialize/completed.json'
        if not initialization.exists():
            kind = 'adopt' if read(controller / 'identity.json')['adopts_preinitialized_instance'] else 'init'
            envelope = invoke(controller, root, {'id': 'initialize', 'kind': kind}, {'classes': data['classes']})
            check_head(envelope['result']['head'], {'revision': 0, 'model': empty_model(data)})
            write(initialization, {'worker': envelope})
        for operation in data['operations']:
            folder = controller / 'steps' / operation['id']
            done = folder / 'completed.json'
            if done.exists():
                invocation['reused_completed_steps'].append(operation['id'])
                continue
            if folder.exists():
                invocation['resumed_incomplete_steps'].append(operation['id'])
            payload = {}
            if 'text_id' in operation:
                item = texts[operation['text_id']]
                payload = {'label': item['label'], 'text': item['text'], 'vector': vectors[item['id']]}
            envelope = invoke(controller, root, operation, payload)
            result = envelope['result']
            expected = reference['operations'][operation['id']]
            if operation['kind'] == 'query':
                checks = check_answer(result, expected)
                checks['prediction_correct_for_intended_label'] = result['prediction'] == payload['label']
                if operation.get('must_equal'):
                    previous = read(controller / 'steps' / operation['must_equal'] / 'completed.json')['worker']
                    for key in ('revision', 'model_root', 'ranking', 'prediction', 'counts', 'classes'):
                        need(result[key] == previous['result'][key], f'Restart changed {key}.')
                    need(all(result['banks'][b]['class_sums'] == previous['result']['banks'][b]['class_sums'] for b in result['banks']),
                         'Restart changed decrypted bank sums.')
                    need(envelope['process']['pid'] != previous['process']['pid'], 'Restart query reused the old process.')
                    checks['restarted_process_same_model_class_sums_and_ranking'] = True
            else:
                check_head(result['head'], expected)
                checks = {'durable_revision_layout_and_fifo_counts_equal': True}
                if operation['kind'] == 'teach':
                    need(result.get('committed') is True and result.get('private_reads') == 0, 'Teaching did not commit without a read.')
                    need(result['request']['lane'] == expected['lane'], 'Native teaching lane differs.')
                    checks['expired_reference_example'] = expected['expired']
            write(done, {'operation': operation, 'worker': envelope, 'checks': checks, 'recorded_utc': utc()})
            invocation['newly_completed_steps'].append(operation['id'])
            invocation['elapsed_seconds'] = time.perf_counter() - started
            summary = summarize(controller, root, prepared, reference, data, invocation)
            print(json.dumps({'operation': operation['id'], 'status': 'complete', 'completed_operations': summary['completed_operations']}), flush=True)
        invocation.update(finished_utc=utc(), elapsed_seconds=time.perf_counter() - started)
        return summarize(controller, root, prepared, reference, data, invocation)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument('--prepare', nargs='?', const=str(PREPARED), metavar='DIR')
    actions.add_argument('--run', metavar='ROOT')
    actions.add_argument('--resume', metavar='ROOT')
    actions.add_argument('--worker', help=argparse.SUPPRESS)
    parser.add_argument('--prepared', default=str(PREPARED), metavar='DIR')
    args = parser.parse_args()
    if args.worker:
        worker(args.worker)
        return
    result = prepare(args.prepare) if args.prepare else run(args.resume or args.run, args.prepared, bool(args.resume))
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
