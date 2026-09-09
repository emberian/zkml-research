#!/usr/bin/env python3
"""Pure field replay of canonical001/query0; never invokes a crypto executable."""
from pathlib import Path
from functools import lru_cache
import hashlib
import json
import time

HERE = Path(__file__).resolve().parent
CAPTURE = Path('/Users/ember/dev/zkml-research/research/vfhe_2026_09_08/query_runtime/acceptance_bridge/canonical001/events.jsonl')
P = 2013265921
RINV = pow(2**32, -1, P)
ZERO, ONE = (0, 0, 0, 0), (1, 0, 0, 0)

def base(raw):
    assert isinstance(raw, int) and 0 <= raw < P
    return raw * RINV % P

def ext(raw):
    assert len(raw['value']) == 4
    return tuple(base(v) for v in raw['value'])

def add(a, b):
    return tuple((x+y) % P for x, y in zip(a, b))

def sub(a, b):
    return tuple((x-y) % P for x, y in zip(a, b))

def mul(a, b):
    tmp = [0]*7
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            tmp[i+j] += x*y
    for i in range(6, 3, -1):
        tmp[i-4] += 11*tmp[i]
    return tuple(x % P for x in tmp[:4])

def power(a, n):
    r = ONE
    while n:
        if n & 1:
            r = mul(r, a)
        a = mul(a, a)
        n >>= 1
    return r

@lru_cache(None)
def inverse(a):
    assert a != ZERO
    r = power(a, P**4-2)
    assert mul(a, r) == ONE
    return r

def main():
    start = time.perf_counter()
    events = [json.loads(line) for line in CAPTURE.open()]
    alpha = ext(next(e['data']['alpha'] for e in events if e['kind'] == 'fri_alpha'))
    claims = next(e['data']['batches'] for e in events if e['kind'] == 'pcs_claims')
    begin = next(i for i, e in enumerate(events) if e['kind'] == 'fri_query' and e['data']['query'] == 0)
    end = next(i for i in range(begin+1, len(events)) if events[i]['kind'] == 'fri_reduced_openings')
    query = events[begin]['data']
    selected = events[begin:end+1]
    widths, point_counts = [[8, 8], [2513, 5], [8]*16, [59], [8, 8]], [1, 2, 1, 1, 2]
    opened = {e['data']['batch']: e['data']['opened_values'] for e in selected if e['kind'] == 'input_batch_verified'}
    matrices = [e['data'] for e in selected if e['kind'] == 'input_matrix']
    after = [e['data'] for e in selected if e['kind'] == 'input_matrix_reduced']
    assert len(matrices) == len(after) == 23
    expected_order = [(b, m) for b, ws in enumerate(widths) for m in range(len(ws))]
    assert [(m['batch'], m['matrix']) for m in matrices] == expected_order
    raw = query['index']
    rev = int(f'{raw:017b}'[::-1], 2)
    omega = pow(31, (P-1)//2**17, P)
    subgroup_x = pow(omega, rev, P)
    coset_x = 31*subgroup_x % P
    total, alpha_power, wrong_coset, reset_total = ZERO, ONE, ZERO, ZERO
    term_count = 0
    offsets = []
    reset_power, previous_batch = ONE, -1
    for mat, actual_after in zip(matrices, after):
        b, m = mat['batch'], mat['matrix']
        assert mat['log_height'] == 17 and mat['reversed_index'] == rev
        assert mat['width'] == widths[b][m] and base(mat['x']) == coset_x
        assert ext(mat['alpha_power_start']) == alpha_power
        assert ext(mat['reduced_opening_start']) == total
        assert mat['points_and_values'] == claims[b]['matrices'][m]['points_and_values']
        assert len(mat['points_and_values']) == point_counts[b]
        if b != previous_batch:
            reset_power = ONE
            previous_batch = b
        offsets.append({'batch': b, 'matrix': m, 'first_alpha_exponent': term_count})
        row = [base(v) for v in opened[b][m]]
        assert len(row) == widths[b][m]
        for raw_z, raw_claims in mat['points_and_values']:
            z = ext(raw_z)
            inv = inverse(sub(z, (coset_x, 0, 0, 0)))
            wrong_inv = inverse(sub(z, (subgroup_x, 0, 0, 0)))
            assert len(raw_claims) == len(row)
            for value, raw_claim in zip(row, raw_claims):
                numerator = sub(ext(raw_claim), (value, 0, 0, 0))
                quotient = mul(numerator, inv)
                total = add(total, mul(alpha_power, quotient))
                wrong_coset = add(wrong_coset, mul(alpha_power, mul(numerator, wrong_inv)))
                reset_total = add(reset_total, mul(reset_power, quotient))
                alpha_power = mul(alpha_power, alpha)
                reset_power = mul(reset_power, alpha)
                term_count += 1
        assert ext(actual_after['alpha_power_end']) == alpha_power
        assert ext(actual_after['reduced_opening_end']) == total
    actual = events[end]['data']
    assert actual['query'] == 0 and len(actual['values']) == 1 and actual['values'][0][0] == 17
    assert term_count == 5271 and alpha_power == power(alpha, 5271)
    assert total == ext(actual['values'][0][1])
    assert wrong_coset != total and reset_total != total
    result = dict(scope='One existing canonical query, pure public field/index arithmetic; no new crypto run.',
                  capture=str(CAPTURE), capture_sha256=hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
                  query=0, raw_index=raw, natural_exponent=rev, term_count=term_count,
                  matrix_checkpoints=23, matrix_offsets=offsets,
                  reduced_opening_canonical=list(total), all_native_checkpoints_match=True,
                  omitted_coset_factor_refused=True, reset_alpha_each_batch_refused=True,
                  seconds=time.perf_counter()-start)
    (HERE/'checks/saved-query.json').write_text(json.dumps(result, indent=2)+'\n')
    print(json.dumps({k: v for k, v in result.items() if k != 'matrix_offsets'}, indent=2))

if __name__ == '__main__':
    main()
