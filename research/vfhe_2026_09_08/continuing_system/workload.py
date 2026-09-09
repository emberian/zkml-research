#!/usr/bin/env python3
"""Frozen public E5 lifecycle workload for core.Live; root launches crypto explicitly.

--prepare [DIR] encodes the fixed corpus and evaluates the plaintext references.
--run ROOT starts one fresh instance; --resume ROOT continues its stable requests.
Either may adopt an already initialized revision-0 core instance with matching
classes/profile; adoption opens core.Live and performs no key generation.
--prepared DIR selects the prepared vectors (default: ./prepared beside this file).
Controller evidence is ROOT.workload; ROOT itself is the core.Live instance.
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
REPO = next(p for p in HERE.parents if (p / 'AGENTS.md').is_file())
CORPUS = HERE / 'workload.json'
DEFAULT_PREPARED = HERE / 'prepared'
HELPER = REPO / 'research/vfhe_2026_09_08/proved_journal/live_nonlinear/fixture_builder/helper.py'


def utc():
    return datetime.now(timezone.utc).isoformat()


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def write(path, value):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + '.tmp')
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    temporary.replace(path)


def need(condition, message):
    if not condition:
        raise RuntimeError(message)


def corpus():
    data = read(CORPUS)
    records = data['training'] + data['held_out']
    need(len({r['id'] for r in records}) == len(records), 'Corpus IDs must be unique.')
    need(len({r['text'] for r in records}) == len(records), 'Training and held-out texts must be distinct.')
    need(all(r['label'] in data['classes'] for r in records), 'Unknown corpus label.')
    return data


def text_map(data):
    return {r['id']: r for r in data['training'] + data['held_out']}


def empty_model(data):
    return {label: {'teaches': 0, 'queue': []} for label in data['classes']}


def teach_reference(model, record, capacity):
    entry = model[record['label']]
    lane = entry['teaches'] % capacity
    expired = entry['queue'].pop(0) if len(entry['queue']) == capacity else None
    entry['queue'].append({'text_id': record['id'], 'lane': lane})
    entry['teaches'] += 1
    return expired


def reference_answer(model, query, vectors, modulus):
    answers = {}
    for label, entry in model.items():
        if not entry['queue']:
            continue
        lanes = [0] * 8
        linear = 0
        for example in entry['queue']:
            dot = sum(a * b for a, b in zip(vectors[example['text_id']], query))
            lanes[example['lane']] = dot * dot
            linear += dot
        need(max(lanes) < modulus and sum(lanes) < modulus, 'Reference leaves the declared no-wrap kernel domain.')
        answers[label] = {'kernel_values': lanes, 'sum_kernel': sum(lanes),
                          'count': len(entry['queue']), 'sum_dot': linear}
    ranking = sorted(answers, key=lambda label: (-Fraction(answers[label]['sum_kernel'], answers[label]['count']), label))
    linear_ranking = sorted(answers, key=lambda label: (-Fraction(answers[label]['sum_dot'], answers[label]['count']), label))
    return {'classes': answers, 'ranking': ranking, 'prediction': ranking[0],
            'linear_ranking': linear_ranking, 'linear_prediction': linear_ranking[0],
            'counts': {label: a['count'] for label, a in answers.items()}}


def evaluate(model, data, vectors):
    rows = []
    for item in data['held_out']:
        answer = reference_answer(model, vectors[item['id']], vectors, data['plaintext_modulus'])
        rows.append({'id': item['id'], 'label': item['label'], 'prediction': answer['prediction'],
                     'linear_prediction': answer['linear_prediction'], 'ranking': answer['ranking']})
    correct = sum(r['prediction'] == r['label'] for r in rows)
    linear_correct = sum(r['linear_prediction'] == r['label'] for r in rows)
    return {'examples': len(rows), 'correct': correct, 'accuracy': correct / len(rows),
            'linear_correct': linear_correct, 'linear_accuracy': linear_correct / len(rows),
            'rows': rows}


def build_reference(data, vectors):
    model = empty_model(data)
    texts = text_map(data)
    operations = {}
    checkpoints = {}
    revision = 0
    expired = []
    for operation in data['operations']:
        record = {'kind': operation['kind']}
        if operation['kind'] == 'teach':
            item = texts[operation['text_id']]
            old = teach_reference(model, item, data['capacity'])
            revision += 1
            record.update(label=item['label'], lane=(model[item['label']]['teaches'] - 1) % data['capacity'], expired=old)
            if old:
                expired.append({'operation': operation['id'], 'label': item['label'], **old})
        elif operation['kind'] == 'query':
            record['answer'] = reference_answer(model, vectors[operation['text_id']], vectors, data['plaintext_modulus'])
            checkpoint = operation['checkpoint']
            checkpoints[checkpoint] = evaluate(model, data, vectors)
        record['revision'] = revision
        record['model'] = json.loads(json.dumps(model))
        operations[operation['id']] = record
    baseline = checkpoints['initial']
    counts = Counter(r['label'] for r in data['held_out'])
    majority = sorted(counts, key=lambda c: (-counts[c], c))[0]
    for value in checkpoints.values():
        value['frozen_initial_correct'] = baseline['correct']
        value['frozen_initial_accuracy'] = baseline['accuracy']
        value['balanced_majority_label'] = majority
        value['balanced_majority_correct'] = counts[majority]
        value['balanced_majority_accuracy'] = counts[majority] / len(data['held_out'])
    return {'schema': 'continuing-system-reference-v1', 'operations': operations,
            'checkpoints': checkpoints, 'expired_examples': expired,
            'final_model': model, 'final_revision': revision,
            'accuracy_scope': 'Fixed author-written held-out set; no tuning, encryption or private-resident claim.'}


def load_prepared(directory):
    directory = Path(directory).resolve()
    record = read(directory / 'preparation.json')
    need(record['workload_sha256'] == digest(CORPUS), 'Prepared corpus differs from frozen workload.')
    need(record['vectors_sha256'] == digest(directory / 'vectors.json'), 'Prepared vectors changed.')
    need(record['reference_sha256'] == digest(directory / 'reference.json'), 'Prepared reference changed.')
    return directory, record, read(directory / 'vectors.json'), read(directory / 'reference.json')


def prepare(directory):
    directory = Path(directory).resolve()
    if (directory / 'preparation.json').is_file():
        _, record, _, _ = load_prepared(directory)
        return {**record, 'preparation_reused': True}
    directory.mkdir(parents=True, exist_ok=True)
    data = corpus()
    workload_hash = digest(CORPUS)
    write(directory / 'frozen_workload.json', data)
    spec = importlib.util.spec_from_file_location('continuing_workload_e5', HELPER)
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    encoder = helper.TextEncoder(directory / 'encoder_cache')
    texts = data['training'] + data['held_out']
    started = time.perf_counter()
    encoded = encoder.encode([r['text'] for r in texts])
    vectors = {r['id']: v for r, v in zip(texts, encoded)}
    need(digest(CORPUS) == workload_hash, 'Corpus changed while encoding.')
    reference = build_reference(data, vectors)
    write(directory / 'vectors.json', vectors)
    write(directory / 'reference.json', reference)
    record = {'schema': 'continuing-system-preparation-v1', 'prepared_utc': utc(),
              'workload_sha256': workload_hash, 'encoder_helper_sha256': digest(HELPER),
              'vectors_sha256': digest(directory / 'vectors.json'),
              'reference_sha256': digest(directory / 'reference.json'),
              'encoder_stats': encoder.stats, 'elapsed_seconds': time.perf_counter() - started,
              'training_texts': len(data['training']), 'held_out_texts': len(data['held_out']),
              'vector_domain': {'dimension': 576, 'maximum_abs_coordinate': max(abs(x) for v in encoded for x in v),
                                'maximum_squared_norm': max(sum(x * x for x in v) for v in encoded)},
              'checkpoints': {name: {k: v for k, v in value.items() if k != 'rows'}
                              for name, value in reference['checkpoints'].items()},
              'expired_examples': reference['expired_examples'], 'cryptographic_operations': 0,
              'preparation_reused': False}
    write(directory / 'preparation.json', record)
    evaluation_note(directory)
    return record


def evaluation_note(prepared, summary=None):
    prepared = Path(prepared)
    preparation = read(prepared / 'preparation.json')
    lines = [
        '# Continuing issue router: lifecycle evaluation', '',
        '[EXECUTED: plaintext preparation] The fixed public corpus contains '
        f"{preparation['training_texts']} teaching texts and {preparation['held_out_texts']} "
        'held-out issue texts. All texts were fixed before encoding. The existing local E5 '
        'helper encoded them without class labels; no held-out tuning followed.', '',
        '| Checkpoint | Kernel mean | Current linear mean | Frozen initial model | Majority |',
        '|---|---:|---:|---:|---:|',
    ]
    for name in ('initial', 'after_teaching', 'after_expiry'):
        row = preparation['checkpoints'][name]
        total = row['examples']
        lines.append(f"| {name} | {row['correct']}/{total} | {row['linear_correct']}/{total} | "
                     f"{row['frozen_initial_correct']}/{total} | {row['balanced_majority_correct']}/{total} |")
    lines.extend(['', '[DERIVED] Additional teaching and FIFO expiry do not improve accuracy on this '
                  'fixed set. The nonlinear and linear comparators agree in aggregate. This remains '
                  'a narrow author-written issue-routing workload, not a benchmark accuracy claim.', '',
                  '[EXECUTED] Encoder statistics: `' + json.dumps(preparation['encoder_stats'], sort_keys=True) + '`.',
                  f"Preparation elapsed: {preparation['elapsed_seconds']:.6f} seconds. "
                  'The plaintext reference retains per-example predictions and every expected kernel lane.', '',
                  f"Prepared artifacts: `{prepared}`. Corpus SHA256 `{preparation['workload_sha256']}`; "
                  f"vectors SHA256 `{preparation['vectors_sha256']}`; reference SHA256 `{preparation['reference_sha256']}`.", ''])
    if summary is None:
        lines.append('[OPEN] No cryptographic lifecycle operation has been launched by this preparation. '
                     'The root owner launches `workload.py --run ROOT --prepared DIR` when core is ready.')
    else:
        status = '[EXECUTED]' if summary['complete'] else '[EXECUTED: partial lifecycle]'
        lines.append(f"{status} {summary['completed_operations']}/{summary['required_operations']} operations "
                     f"completed against `{summary['instance_root']}`. Full result and attempt logs: "
                     f"`{summary['controller_root']}`. Recorded worker-attempt wall time: "
                     f"{summary['worker_attempt_wall_seconds']:.6f} seconds.")
        lines.append('')
        for query in summary['queries']:
            lines.append(f"- `{query['id']}`: revision {query['revision']}, prediction "
                         f"`{query['prediction']}`, {query['checks']['compared_kernel_values']} exact kernel "
                         f"values matched, rational ranking matched; worker PID {query['process_pid']}.")
        lines.extend(['', 'Cumulative metrics for unique stable requests: `' +
                      json.dumps(summary['instance_cumulative_metrics'], sort_keys=True) + '`.',
                      'Metrics available for every completed crypto operation: `' +
                      str(summary['metrics_available_for_every_crypto_operation']) + '`.',
                      f"Current invocation reused {len(summary['invocation']['reused_completed_steps'])} "
                      f"completed operations and resumed {len(summary['invocation']['resumed_incomplete_steps'])} "
                      'incomplete operation records. These are not claimed as fresh proofs.', '',
                      '[DERIVED] The checked interface retains a full BFV reader. Public texts and '
                      'features supply the reference; exact agreement establishes execution of this '
                      'workload, not operator-private state or cryptographically restricted decryption.'])
    (HERE / 'evaluation.md').write_text('\n'.join(lines) + '\n')


def check_head(head, expected):
    need(head['revision'] == expected['revision'], 'Durable revision differs from reference.')
    need(set(head['classes']) == set(expected['model']), 'Durable class set differs from reference.')
    for label, wanted in expected['model'].items():
        actual = head['classes'][label]
        need(actual['teaches'] == wanted['teaches'], f'{label}: durable teaching count differs.')
        need([e['lane'] for e in actual['queue']] == [e['lane'] for e in wanted['queue']],
             f'{label}: FIFO lane order differs.')


def check_answer(answer, expected):
    wanted = expected['answer']
    need(answer.get('answered') is True, 'Query did not return an accepted answer.')
    need(answer['revision'] == expected['revision'], 'Answer revision differs from reference.')
    need(answer['counts'] == wanted['counts'], 'Answer counts differ from reference.')
    need(answer['ranking'] == wanted['ranking'] and answer['prediction'] == wanted['prediction'],
         'Exact rational ranking differs from reference.')
    need(set(answer['classes']) == set(wanted['classes']), 'A decrypted class is missing or extra.')
    for label, reference in wanted['classes'].items():
        actual = answer['classes'][label]
        need(actual['kernel_values'] == reference['kernel_values'], f'{label}: decrypted kernel lanes differ.')
        need(actual['sum_kernel'] == reference['sum_kernel'], f'{label}: decrypted sum differs.')
        need(actual.get('all8192_slots_repeat8') is True, f'{label}: reader did not verify repeated SIMD slots.')
    return {'every_kernel_lane_equal': True, 'compared_kernel_values': 8 * len(wanted['classes']),
            'reader_checked_repeat8_per_class': True, 'exact_rational_ranking_equal': True,
            'prediction_correct_for_intended_label': None}


def worker(spec_path):
    job = read(spec_path)
    sys.path.insert(0, str(HERE))
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
    envelope = {'result': result, 'process': {'pid': os.getpid(), 'ppid': os.getppid(),
                'finished_utc': utc(), 'elapsed_seconds': time.perf_counter() - started}}
    write(job['result_path'], envelope)
    print(json.dumps({'operation': operation['id'], 'complete': True, 'pid': os.getpid()}), flush=True)


def invoke(controller, root, operation, payload):
    folder = controller / 'steps' / operation['id']
    folder.mkdir(parents=True, exist_ok=True)
    attempt = len(list(folder.glob('attempt-*.json'))) + 1
    prefix = folder / f'attempt-{attempt:03}'
    result_path = folder / 'worker_result.json'
    job = {'root': str(root), 'operation': operation, 'result_path': str(result_path), **payload}
    spec_path = folder / 'input.json'
    write(spec_path, job)
    argv = [sys.executable, '-u', '-B', str(Path(__file__).resolve()), '--worker', str(spec_path)]
    started = time.perf_counter()
    record = {'argv': argv, 'started_utc': utc(), 'attempt': attempt, 'status': 'running'}
    with prefix.with_suffix('.stdout').open('wb') as stdout, prefix.with_suffix('.stderr').open('wb') as stderr:
        process = subprocess.Popen(argv, stdout=stdout, stderr=stderr,
                                   env={**os.environ, 'PYTHONDONTWRITEBYTECODE': '1'}, start_new_session=True)
        record['pid'] = process.pid
        write(prefix.with_suffix('.json'), record)
        print(json.dumps({'operation': operation['id'], 'status': 'running', 'pid': process.pid,
                          'stderr': str(prefix.with_suffix('.stderr'))}), flush=True)
        try:
            returncode = process.wait()
        except BaseException:
            # The child may still be proving. Leave its actual handle and all artifacts intact.
            record.update(status='controller_interrupted', observed_utc=utc())
            write(prefix.with_suffix('.json'), record)
            raise
    record.update(status='completed' if returncode == 0 else 'failed', returncode=returncode,
                  elapsed_seconds=time.perf_counter() - started, finished_utc=utc())
    write(prefix.with_suffix('.json'), record)
    need(returncode == 0, f"Operation {operation['id']} failed; see {prefix}.stderr. Resume retains its request ID.")
    return read(result_path)


def live_pid(pid):
    try:
        os.kill(pid, 0)
        return True
    except ProcessLookupError:
        return False
    except PermissionError:
        return True


def refuse_running_attempts(controller):
    for path in (controller / 'steps').glob('*/attempt-*.json'):
        record = read(path)
        if record.get('status') in ('running', 'controller_interrupted') and live_pid(record['pid']):
            raise RuntimeError(f"Existing worker PID {record['pid']} is live; observe that handle before resuming ({path}).")


def summarize(controller, root, prepared, reference, data, invocation):
    completed = {}
    metrics = Counter()
    phase_seconds = Counter()
    all_metrics = True
    queries = []
    for operation in data['operations']:
        path = controller / 'steps' / operation['id'] / 'completed.json'
        if not path.is_file():
            break
        entry = read(path)
        completed[operation['id']] = entry
        result = entry['worker']['result']
        if operation['kind'] in ('teach', 'query'):
            values = result.get('metrics')
            if values is None:
                kind = 'teaching' if operation['kind'] == 'teach' else 'queries'
                metric_path = root / kind / operation['id'] / 'metrics.json'
                values = read(metric_path) if metric_path.is_file() else None
            if values is None:
                all_metrics = False
            else:
                for key in ('proofs_generated', 'proofs_verified', 'proof_bytes', 'committed_updates', 'answered_queries', 'private_reads'):
                    metrics[key] += values.get(key, 0)
                for key, value in values.get('phase_elapsed_seconds', {}).items():
                    if isinstance(value, (int, float)):
                        phase_seconds[key] += value
        if operation['kind'] == 'query':
            queries.append({'id': operation['id'], 'checkpoint': operation['checkpoint'],
                            'revision': result['revision'], 'prediction': result['prediction'],
                            'ranking': result['ranking'], 'checks': entry['checks'],
                            'process_pid': entry['worker']['process']['pid']})
    attempts = [read(p) for p in (controller / 'steps').glob('*/attempt-*.json')]
    summary = {'schema': 'continuing-system-workload-result-v1', 'updated_utc': utc(),
               'instance_root': str(root), 'controller_root': str(controller),
               'workload_sha256': digest(CORPUS), 'preparation_sha256': digest(prepared / 'preparation.json'),
               'completed_operations': len(completed), 'required_operations': len(data['operations']),
               'complete': len(completed) == len(data['operations']),
               'queries': queries, 'metrics_available_for_every_crypto_operation': all_metrics,
               'instance_cumulative_metrics': dict(metrics), 'phase_elapsed_seconds': dict(phase_seconds),
               'worker_attempt_wall_seconds': sum(a.get('elapsed_seconds', 0) for a in attempts),
               'worker_attempts_without_terminal_timing': sum('elapsed_seconds' not in a for a in attempts),
               'invocation': invocation,
               'freshness_accounting': 'Metrics describe each unique stable request once across all invocations. Reused or resumed requests are not counted as fresh work in this invocation.',
               'plaintext_utility': {k: {a: b for a, b in v.items() if a != 'rows'} for k, v in reference['checkpoints'].items()},
               'expired_reference_examples': reference['expired_examples'],
               'scope': data['evaluation_policy']['scope']}
    write(controller / 'RESULT.json', summary)
    evaluation_note(prepared, summary)
    return summary


def run(root, prepared_dir, resume):
    root = Path(root).resolve()
    controller = root.with_name(root.name + '.workload')
    prepared, prep, vectors, reference = load_prepared(prepared_dir)
    data = corpus()
    texts = text_map(data)
    identity = {'schema': 'continuing-system-workload-run-v1', 'root': str(root),
                'workload_sha256': digest(CORPUS), 'prepared_dir': str(prepared),
                'vectors_sha256': prep['vectors_sha256'], 'reference_sha256': prep['reference_sha256']}
    bootstrap_existing = root.exists() and not controller.exists()
    if resume and controller.is_dir():
        stored = read(controller / 'identity.json')
        need(all(stored.get(k) == v for k, v in identity.items()), 'Resume identity or prepared corpus changed.')
    else:
        need(not controller.exists(), 'An existing workload controller requires --resume.')
        need(not resume or bootstrap_existing, 'No workload instance or controller exists to resume.')
        controller.mkdir(parents=True)
        write(controller / 'identity.json', {**identity, 'created_utc': utc(),
                                            'adopts_preinitialized_instance': bootstrap_existing})
    with (controller / 'driver.lock').open('a') as lock:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        refuse_running_attempts(controller)
        started = time.perf_counter()
        invocation = {'started_utc': utc(), 'mode': 'resume' if resume else 'run',
                      'reused_completed_steps': [], 'resumed_incomplete_steps': [], 'newly_completed_steps': []}
        init_path = controller / 'steps/initialize/completed.json'
        if not init_path.is_file():
            # core.Live validates the pinned profile on an existing instance.
            # Adopting HTTP initialization never calls initialize/keygen again.
            # A driver-owned partial initialization uses core's idempotent
            # initializer; an externally initialized HTTP instance is read-only
            # adoption, so no key generation is requested in that path.
            kind = 'adopt' if read(controller / 'identity.json').get('adopts_preinitialized_instance') else 'init'
            envelope = invoke(controller, root, {'id': 'initialize', 'kind': kind}, {'classes': data['classes']})
            check_head(envelope['result']['head'], {'revision': 0, 'model': empty_model(data)})
            write(init_path, {'worker': envelope})
        for operation in data['operations']:
            folder = controller / 'steps' / operation['id']
            done = folder / 'completed.json'
            expected = reference['operations'][operation['id']]
            if done.is_file():
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
            if operation['kind'] == 'query':
                checks = check_answer(result, expected)
                checks['prediction_correct_for_intended_label'] = result['prediction'] == payload['label']
                if operation.get('must_equal'):
                    earlier = read(controller / 'steps' / operation['must_equal'] / 'completed.json')['worker']['result']
                    for key in ('prediction', 'ranking', 'counts', 'revision', 'model_root'):
                        need(result[key] == earlier[key], f'Restart changed {key}.')
                    need(all(result['classes'][c]['kernel_values'] == earlier['classes'][c]['kernel_values'] for c in result['classes']),
                         'Restart changed a decrypted lane.')
                    previous_pid = read(controller / 'steps' / operation['must_equal'] / 'completed.json')['worker']['process']['pid']
                    need(previous_pid != envelope['process']['pid'], 'Restart query did not execute in a new process.')
                    checks['restarted_process_same_model_and_every_lane'] = True
            else:
                check_head(result['head'], expected)
                checks = {'durable_revision_and_fifo_lanes_equal': True}
                if operation['kind'] == 'teach':
                    need(result.get('committed') is True and result.get('private_reads') == 0, 'Teaching was not committed without a private read.')
                    need(result['request']['lane'] == expected['lane'], 'Issued teaching lane differs.')
                    checks['expired_reference_example'] = expected['expired']
            entry = {'operation': operation, 'worker': envelope, 'checks': checks, 'recorded_utc': utc()}
            write(done, entry)
            invocation['newly_completed_steps'].append(operation['id'])
            invocation['elapsed_seconds'] = time.perf_counter() - started
            summary = summarize(controller, root, prepared, reference, data, invocation)
            print(json.dumps({'operation': operation['id'], 'status': 'complete', 'completed_operations': summary['completed_operations']}), flush=True)
        invocation.update(finished_utc=utc(), elapsed_seconds=time.perf_counter() - started)
        return summarize(controller, root, prepared, reference, data, invocation)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    actions = parser.add_mutually_exclusive_group(required=True)
    actions.add_argument('--prepare', nargs='?', const=str(DEFAULT_PREPARED), metavar='DIR')
    actions.add_argument('--run', metavar='ROOT')
    actions.add_argument('--resume', metavar='ROOT')
    actions.add_argument('--worker', help=argparse.SUPPRESS)
    parser.add_argument('--prepared', default=str(DEFAULT_PREPARED), metavar='DIR')
    args = parser.parse_args()
    if args.worker:
        worker(args.worker)
        return
    if args.prepare:
        result = prepare(args.prepare)
    else:
        result = run(args.resume or args.run, args.prepared, bool(args.resume))
    print(json.dumps(result, indent=2), flush=True)


if __name__ == '__main__':
    main()
