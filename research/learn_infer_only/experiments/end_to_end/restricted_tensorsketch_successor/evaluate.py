"""The single frozen paired benchmark. No encoder imports or crypto calls."""
import csv
import datetime
import hashlib
import json
import time
from pathlib import Path

import numpy as np

from basis import GeneralBasis, pivots
from tensorsketch import HERE, POLICY, HASHES, SIGNS, transform_many, raw_sketch

ROOT = HERE.parents[4]
OLD = HERE.parent / 'useful_learner_2026_09_08'
FIXED = HERE.parent / 'restricted_query_learner_2026_09_08'
OUT = HERE / 'results'


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2, allow_nan=False) + '\n')


def check_freeze():
    frozen = json.loads((HERE / 'POLICY_FREEZE.json').read_text())
    for path, expected in frozen['pins'].items():
        assert sha(ROOT / path) == expected, path
    return sha(HERE / 'POLICY_FREEZE.json')


def full_evaluation(train, test, records, labels):
    queues = {label: [] for label in labels}
    results = {}
    snapshots = {}
    truth = [row['category'] for row in records['test']]
    expiries = 0
    for step, (row, vector) in enumerate(zip(records['train'], train), 1):
        queue = queues[row['category']]
        if len(queue) == 8:
            queue.pop(0)
            expiries += 1
        queue.append(vector)
        if step in [304, 616, 1232]:
            active = [label for label in labels if queues[label]]
            assert all(len(queues[label]) == 8 for label in active)
            sums = np.array([np.sum(queues[label], axis=0) for label in active], dtype=np.int64)
            scores = test @ sums.T
            predictions = [active[i] for i in np.argmax(scores, axis=1)]
            correct = np.array([a == b for a, b in zip(predictions, truth)])
            old = np.array([label in labels[:38] for label in truth])
            results[str(step)] = {
                'revision': step, 'active_classes': len(active),
                'correct': int(correct.sum()), 'total': len(truth),
                'accuracy': float(correct.mean()),
                'original38_correct': int(correct[old].sum()),
                'added39_correct': int(correct[~old].sum()),
                'predictions': predictions,
                'max_abs_class_sum_score': int(np.max(abs(scores))),
            }
            snapshots[step] = sums
    assert expiries == 616
    assert np.array_equal(snapshots[304], snapshots[616][:38])
    return results


def paired_summary(first, second, truth):
    a, b = first['predictions'], second['predictions']
    return {
        'linear_correct': first['correct'], 'tensorsketch_correct': second['correct'],
        'total': len(truth),
        'accuracy_difference_percentage_points': 100 * (second['correct'] - first['correct']) / len(truth),
        'changed_predictions': sum(x != y for x, y in zip(a, b)),
        'linear_only_correct': sum(x == t and y != t for x, y, t in zip(a, b, truth)),
        'tensorsketch_only_correct': sum(y == t and x != t for x, y, t in zip(a, b, truth)),
    }


def fixed_evaluation(queries, observations, fixture):
    classes = fixture['classes']
    queues = {label: [] for label in classes}
    snapshots = []
    for i, (event, x) in enumerate(zip(fixture['events'], observations), 1):
        queue = queues[event['class']]
        if len(queue) == 2:
            expired = queue.pop(0)
            assert event['expired_event'] == expired[0]
        else:
            assert event['expired_event'] is None
        queue.append((i, x))
        if i % 2 == 0:
            assert len(queues[classes[0]]) == len(queues[classes[1]])
            sums = np.array([np.sum([x for _, x in queues[label]], axis=0) for label in classes])
            scores = queries @ sums.T
            predictions = [classes[j] for j in np.argmax(scores, axis=1)]
            snapshots.append({'revision': i, 'counts': {c: len(queues[c]) for c in classes},
                              'scores': [{c: int(v) for c, v in zip(classes, row)} for row in scores],
                              'predictions': predictions})
    return snapshots


def main():
    started = time.perf_counter()
    assert ROOT.name == 'zkml-research'
    freeze = check_freeze()
    OUT.mkdir()  # Refuse overwriting the single attempt.
    save(OUT / 'STARTED.json', {'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'policy_freeze_sha256': freeze, 'evaluation_source_sha256': sha(Path(__file__)),
         'numpy': np.__version__, 'successor_utility_attempt': 1})
    records = json.loads((OLD / 'full77/selection.json').read_text())
    labels = records['classes']
    arrays = np.load(OLD / 'full77/features.npz', allow_pickle=False)
    train, test = arrays['train'].astype(np.int64), arrays['test'].astype(np.int64)
    assert train.shape == (1232, 577) and test.shape == (3080, 577) and len(labels) == 77
    mapped_train, train_stats = transform_many(train)
    mapped_test, test_stats = transform_many(test)
    np.savez_compressed(OUT / 'mapped_features.npz', train=mapped_train.astype(np.int16),
                        test=mapped_test.astype(np.int16))
    linear = full_evaluation(train, test, records, labels)
    sketch = full_evaluation(mapped_train, mapped_test, records, labels)
    predecessor = json.loads((OLD / 'full77/result.json').read_text())['checkpoints']
    for revision in linear:
        assert linear[revision]['predictions'] == predecessor[revision]['predictions']
    truth = [r['category'] for r in records['test']]
    paired = {r: paired_summary(linear[r], sketch[r], truth) for r in linear}
    save(OUT / 'full77.json', {'linear': linear, 'tensorsketch': sketch, 'paired': paired})
    with (OUT / 'predictions.csv').open('w') as f:
        writer = csv.writer(f)
        writer.writerow(['revision', 'test_index', 'truth', 'linear', 'tensorsketch'])
        for r in linear:
            writer.writerows((r, i, t, a, b) for i, (t, a, b) in enumerate(zip(
                truth, linear[r]['predictions'], sketch[r]['predictions'])))

    registry_old = json.loads((FIXED / 'registry.json').read_text())
    fixture = json.loads((FIXED / 'fixture.json').read_text())
    queries = np.array([r['vector'] for r in registry_old['queries']], dtype=np.int64)
    observations = np.array([r['vector'] for r in fixture['events']], dtype=np.int64)
    mapped_queries, query_stats = transform_many(queries)
    mapped_observations, observation_stats = transform_many(observations)
    baseline_slice = fixed_evaluation(queries, observations, fixture)
    sketch_slice = fixed_evaluation(mapped_queries, mapped_observations, fixture)
    slice_truth = [r['label'] for r in registry_old['queries']]
    for a, b, old in zip(baseline_slice, sketch_slice, fixture['snapshots']):
        assert a['scores'] == old['scores'] and a['predictions'] == old['predictions']
        for s in [a, b]:
            s.update(correct=sum(x == y for x, y in zip(s['predictions'], slice_truth)), total=16)
    save(OUT / 'known16.json', {'linear': baseline_slice, 'tensorsketch': sketch_slice,
                              'source_fixture_sha256': sha(FIXED / 'fixture.json')})
    query_rows = mapped_queries.tolist()
    pivot_columns = pivots(query_rows, POLICY['p'])
    registry = {
        'schema': 'restricted-tensorsketch-query-registry-v1', 'p': POLICY['p'],
        'dimension': 577, 'registered_recipients': 16, 'classes': fixture['classes'],
        'feature_map': {'policy_sha256': sha(HERE / 'policy.json'),
                        'tensorsketch_sha256': sha(HERE / 'tensorsketch.py'),
                        'input': 'Original577 cached semantic vector', 'output_norm_bound': 512},
        'queries': [dict(coordinate=i, text=old['text'], label=old['label'],
                         test_index=old['test_index'], vector=row)
                    for i, (old, row) in enumerate(zip(registry_old['queries'], query_rows))],
        'pivot_columns': pivot_columns,
        'identity_columns': [i for i in range(577) if i not in pivot_columns],
        'basis_rule': 'First16 rows are mapped fixed queries; canonical identity completion',
        'source_registry_sha256': sha(FIXED / 'registry.json'),
    }
    save(HERE / 'registry.json', registry)
    basis_ok = len(pivot_columns) == 16
    if basis_ok:
        basis = GeneralBasis(registry)
        for x in mapped_observations.tolist():
            encoded = basis.transform(x)
            assert basis.inverse(encoded) == [v % POLICY['p'] for v in x]
            assert encoded[:16] == [sum(v*w for v, w in zip(q, x)) for q in query_rows]
    save(HERE / 'fixture.json', {
        'classes': fixture['classes'], 'capacity': 2,
        'events': [dict(event=e['event'], **{'class': e['class']}, text=e['text'],
                        train_index=e['train_index'], expired_event=e['expired_event'],
                        vector=x.tolist(), original_vector_sha256=hashlib.sha256(
                            np.asarray(e['vector'], dtype='<i8').tobytes()).hexdigest())
                   for e, x in zip(fixture['events'], mapped_observations)],
        'snapshots': sketch_slice, 'scope': 'Known reused plaintext fixture; no new cryptography'})
    save(HERE / 'hash_tables.json', {'policy_sha256': sha(HERE / 'policy.json'),
        'h1': HASHES[0].tolist(), 'h2': HASHES[1].tolist(),
        's1': SIGNS[0].tolist(), 's2': SIGNS[1].tolist()})

    # Predetermined64 pairs quantify approximation, never select a map or policy.
    errors = []
    for i in range(64):
        x, y = train[i], test[i]
        raw_x, raw_y = raw_sketch(x), raw_sketch(y)
        raw_product = sum(int(a)*int(b) for a, b in zip(raw_x, raw_y))
        target_numerator = (int(x[:-1] @ y[:-1]) + 256**2)**2
        target = target_numerator / 512**4
        estimate = raw_product / 512**4
        quantized = int(mapped_train[i] @ mapped_test[i]) / 256**2
        errors.append({'train_index': i, 'test_index': i, 'target_kernel': target,
                       'raw_sketch_estimate': estimate, 'quantized_estimate': quantized,
                       'raw_error': estimate-target, 'quantized_error': quantized-target})
    save(OUT / 'approximation64.json', errors)
    final = paired['1232']
    gate = (final['tensorsketch_correct'] - final['linear_correct'] >= -154 and
            sketch_slice[-1]['correct'] >= 14 and basis_ok)
    result = {
        'status': 'PASS', 'completed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'elapsed_seconds': time.perf_counter()-started,
        'policy_freeze_sha256': check_freeze(), 'full77_paired': paired,
        'known16_paired': [{'revision': a['revision'], 'linear_correct': a['correct'],
                            'tensorsketch_correct': b['correct'], 'total': 16}
                           for a, b in zip(baseline_slice, sketch_slice)],
        'transform_statistics': {'full77_train': train_stats, 'full77_test': test_stats,
                                 'known16_queries': query_stats, 'six_observations': observation_stats},
        'registered_query_rank': len(pivot_columns), 'six_basis_roundtrips': basis_ok,
        'exact_signed_weight32_bound': 32 * 512**2, 'p_half_floor': POLICY['p']//2,
        'approximation64_raw_mean_absolute_error': float(np.mean([abs(e['raw_error']) for e in errors])),
        'approximation64_quantized_mean_absolute_error': float(np.mean([abs(e['quantized_error']) for e in errors])),
        'predeclared_crypto_recommendation_gate_passes': bool(gate),
        'counts': {'maps': 1, 'seeds': 1, 'paired_utility_runs': 1, 'new_model_forwards': 0,
                   'new_downloads': 0, 'crypto_runs': 0, 'private_artifacts_read': 0},
    }
    save(OUT / 'RESULT.json', result)
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
