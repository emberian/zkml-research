"""ONE fixed plaintext feasibility evaluation; no model or cryptography run."""
import hashlib
import json
from pathlib import Path
from basis import D, R, P, GeneralBasis, pivots
import kernel as K

HERE = Path(__file__).resolve().parent
BASE = HERE.parent / 'restricted_query_learner_2026_09_08'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
def save(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')

def main():
    if (HERE / 'PREPARATION.json').exists():
        raise ValueError('Sole fixed plaintext evaluation already exists; no retuning')
    old_registry = json.loads((BASE / 'registry.json').read_text())
    old_fixture = json.loads((BASE / 'fixture.json').read_text())
    queries = []
    for original in old_registry['queries']:
        q = K.compact(original['vector'])
        queries.append({**{k: v for k, v in original.items() if k != 'vector'},
                        'compact_vector': q, 'vector': K.query_coefficients(q)})
    rows = [q['vector'] for q in queries]
    pc = pivots(rows, P)
    registry = {'schema': 'restricted-quadratic-kernel-query-registry-v1',
                'p': P, 'dimension': D, 'registered_recipients': R,
                'selection': old_registry['selection'], 'classes': old_registry['classes'],
                'queries': queries, 'pivot_columns': pc,
                'identity_columns': [i for i in range(D) if i not in pc],
                'basis_rule': 'First16 rows are symmetric-quadratic query coefficients; ascending nonpivot identity completion',
                'feature_map': {'domain_ascii': K.DOMAIN.decode(), 'input_dimension': 576,
                                'compact_dimension': 32, 'radius': 4, 'lift_dimension': 528,
                                'padding': 49, 'normalization': 'max absolute coordinate; nearest integer ties away from zero',
                                'kernel_sha256': sha(HERE / 'kernel.py')},
                'source_sha256': {str(BASE / name): sha(BASE / name)
                                  for name in ['registry.json', 'fixture.json', 'SOURCE_PINS.json']}}
    b = GeneralBasis(registry)
    events = []
    queues = {c: [] for c in old_fixture['classes']}
    snapshots = []
    identity_checks = 0
    for original in old_fixture['events']:
        x = K.compact(original['vector'])
        v = K.lift(x)
        a = b.transform(v)
        assert b.inverse(a) == [z % P for z in v]
        event = {**{k: z for k, z in original.items() if k != 'vector'},
                 'compact_vector': x, 'vector': v}
        for coordinate, query in enumerate(queries):
            exact = K.kernel(x, query['compact_vector'])
            assert sum(vv * yy for vv, yy in zip(v, query['vector'])) == exact
            assert a[coordinate] == exact
            identity_checks += 1
        queue = queues[event['class']]
        expired = queue.pop(0)['event'] if len(queue) == 2 else None
        assert expired == event['expired_event']
        queue.append(event)
        events.append(event)
        if event['event'] % 2 == 0:
            scores = [{c: sum(K.kernel(e['compact_vector'], q['compact_vector']) for e in queues[c])
                       for c in old_fixture['classes']} for q in queries]
            predictions = [sorted(s, key=lambda c: (-s[c], c))[0] for s in scores]
            snapshots.append({'revision': event['event'], 'counts': {c: len(queues[c]) for c in queues},
                              'live_events': {c: [e['event'] for e in queues[c]] for c in queues},
                              'scores': scores, 'predictions': predictions,
                              'correct': sum(p == q['label'] for p, q in zip(predictions, queries))})
    save('registry.json', registry)
    save('fixture.json', {'classes': old_fixture['classes'], 'capacity': 2,
                         'events': events, 'snapshots': snapshots,
                         'scope': 'Exactly reused known-public six-input/16-query slice; one fixed map evaluation'})
    result = {'status': 'PASS', 'map_selected_before_scores': True, 'plaintext_map_evaluations': 1,
              'query_row_rank': len(pc), 'identity_completion_rows': len(b.rest),
              'six_input_basis_roundtrips': len(events), 'exact_pairwise_kernel_identities': identity_checks,
              'universal_abs_compact_bound': 4, 'universal_abs_lift_bound': 16,
              'universal_abs_query_coefficient_bound': 32,
              'universal_single_kernel_bound': (32 * 4 * 4) ** 2,
              'universal_positive_capacity2_sum_bound': 2 * (32 * 4 * 4) ** 2,
              'universal_signed_weight32_sum_bound': 32 * (32 * 4 * 4) ** 2,
              'p_half_floor': P // 2,
              'whole_weight32_kernel_bound_strictly_below_p_half': 32 * (32 * 4 * 4) ** 2 < P // 2,
              'registered_max_query_L1': max(sum(map(abs, row)) for row in rows),
              'registered_capacity2_generic_int8_bound': 2 * max(b.bounds),
              'observed_max_single_kernel': max(K.kernel(e['compact_vector'], q['compact_vector']) for e in events for q in queries),
              'observed_max_capacity2_score': max(v for s in snapshots for pair in s['scores'] for v in pair.values()),
              'snapshots': [{'revision': s['revision'], 'correct': s['correct'], 'total': 16} for s in snapshots],
              'new_model_forwards': 0, 'new_crypto_runs': 0,
              'sources_unchanged': all(sha(Path(k)) == v for k, v in registry['source_sha256'].items())}
    assert result['whole_weight32_kernel_bound_strictly_below_p_half']
    save('PREPARATION.json', result)
    print(json.dumps(result), flush=True)

if __name__ == '__main__':
    main()
