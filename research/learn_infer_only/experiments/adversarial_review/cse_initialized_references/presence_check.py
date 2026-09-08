"""Public wire storage checks. Never evaluate a gate operation or run any crypto."""
from pathlib import Path
import hashlib
import json

HERE = Path(__file__).resolve().parent
ARTIFACTS = HERE.parents[2] / 'formal/private_address_ema/emitted_schedule/artifacts'
PINS = {'learn': '94e8369ffc8fcdf57b8351b278d5af90dc49a26d83600d40f0bd6a0da359dde8',
        'infer': 'b742ed7710d2680119eceeff0c553d675e1ce187a503981fc500a6a4a683b80c'}
MISSING = object()

def storage_check(descriptor, payload):
    n, bound = descriptor['nInputs'], descriptor['nWires']
    assert 0 <= n <= bound
    # A tagged Some supports arbitrary values, including Python None.
    store = [MISSING for _ in range(bound)]
    for i in range(n):
        store[i] = ('some', ('input', i))
    lower, reads = n, 0
    def read(wire):
        nonlocal reads
        reads += 1
        if set(wire) == {'c'}:
            return ('some', ('constant', wire['c']))
        assert set(wire) == {'w'}
        index = wire['w']
        assert type(index) is int and 0 <= index < bound
        assert store[index] is not MISSING, ('uninitialized wire', index)
        return store[index]
    for ordinal, gate in enumerate(descriptor['gates']):
        out = gate['out']
        assert type(out) is int and lower <= out < bound
        read(gate['a']); read(gate['b'])
        store[out] = ('some', payload(ordinal))
        lower = out + 1
        # Intentionally do not access gate['op'] or derive a value from operands.
    for wire in descriptor['outputs']:
        read(wire)
    return {'input_slots': n, 'allocated_slots': bound, 'gate_writes': len(descriptor['gates']),
            'outputs': len(descriptor['outputs']), 'successful_reads': reads,
            'unwritten_allocated_slots': sum(value is MISSING for value in store)}

result = {}
payloads = {'none': lambda _: None, 'text': lambda i: 'payload-' + str(i),
            'negative_integer': lambda i: -(i+1), 'tuple': lambda i: (i, False, None)}
for operation, expected in PINS.items():
    path = ARTIFACTS / (operation + '.json')
    assert hashlib.sha256(path.read_bytes()).hexdigest() == expected
    descriptor = json.loads(path.read_text())
    assert descriptor['operation'] == operation and descriptor['schema'] == 'private-address-ema-bool-schedule-v1'
    observed = [storage_check(descriptor, payload) for payload in payloads.values()]
    assert all(item == observed[0] for item in observed)
    result[operation] = {'sha256': expected, **observed[0], 'payload_controls': list(payloads)}

hole = {'nInputs': 0, 'nWires': 2,
        'gates': [{'out': 1, 'a': {'w': 0}, 'b': {'c': False}}], 'outputs': [{'w': 1}]}
assert 0 <= hole['gates'][0]['a']['w'] < hole['gates'][0]['out'] < hole['nWires']
try:
    storage_check(hole, lambda _: None)
except AssertionError as error:
    assert error.args == (('uninitialized wire', 0),)
else:
    raise AssertionError('hole control must fail')
report = {'ok': True, 'actual_frozen_descriptors': result, 'hole_control': 'allocated auxiliary wire0 has no input or prior producer; lookup fails',
          'gate_operations_evaluated': 0, 'Lean_builds': 0, 'crypto_execution': 0,
          'scope': 'Finite JSON presence-only controls and arbitrary payload examples. Universal Option presence is the Lean statement; JSON/serde/Rust correspondence remains TCB.'}
(HERE / 'presence_results.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
print(json.dumps(report, indent=2, sort_keys=True))
