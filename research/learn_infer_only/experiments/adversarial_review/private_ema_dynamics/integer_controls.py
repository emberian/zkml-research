"""Independent integer controls; no Lean, Rust, TFHE, model, or private data calls."""
from collections import Counter


def step(s, u):
    return (7 * s + u) // 8


def advance(s, labels):
    for u in labels:
        s = step(s, u)
    return s


def history(state, events):
    state = list(state)
    for address, label in events:
        state[address] = step(state[address], label)
    return state


def run():
    residuals = Counter()
    full_byte_pairs = 0
    monotonic_adjacent_pairs = 0
    for s in range(-128, 128):
        for u in range(-128, 128):
            v = step(s, u)
            assert -128 <= v <= 127
            r = 8 * v - (7 * s + u)
            assert -7 <= r <= 0
            residuals[r] += 1
            full_byte_pairs += 1
            if s < 127:
                assert v <= step(s + 1, u)
                monotonic_adjacent_pairs += 1

    horizon = {}
    for u in (-120, 120):
        rows = []
        for s in range(-120, 121):
            first = next(n for n in range(7)
                         if (advance(s, [u] * n) < 0) == (u < 0))
            values = [advance(s, [u] * n) for n in range(7)]
            assert (values[6] < 0) == (u < 0)
            assert (step(values[6], u) < 0) == (u < 0)
            rows.append((s, first, values[5], values[6]))
        horizon[str(u)] = {
            'initial_states': len(rows),
            'max_first_correct_step': max(row[1] for row in rows),
            'five_step_failures': [row[0] for row in rows if (row[2] < 0) != (u < 0)],
            'six_step_min': min(row[3] for row in rows),
            'six_step_max': max(row[3] for row in rows),
            'endpoint_trace': [advance(-u, [u] * n) for n in range(7)],
        }
    fixed = {
        str(u): {
            'within120': [s for s in range(-120, 121) if step(s, u) == s],
            'full_byte': [s for s in range(-128, 128) if step(s, u) == s],
            'from_zero_after_25': advance(0, [u] * 25),
        } for u in (-120, 120)
    }
    assert fixed['120']['within120'] == list(range(113, 121))
    assert fixed['-120']['within120'] == [-120]
    assert fixed['-120']['full_byte'] == list(range(-127, -119))
    assert fixed['120']['from_zero_after_25'] == 113
    assert fixed['-120']['from_zero_after_25'] == -120

    # Distinct boundary controls: falsify two tempting weakenings of the theorem.
    count_only_events = [(2, 120)] + [(1, 120)] * 5
    count_only = history([-120] * 4, count_only_events)
    assert len(count_only_events) == 6 and count_only[2] == -90
    inconsistent_events = [(2, 120)] * 5 + [(2, -120)]
    inconsistent = history([-120] * 4, inconsistent_events)
    assert len(inconsistent_events) == 6 and inconsistent[2] == -19

    # General local framing control on the entire selected-byte/label domain.
    # Infinite histories are covered by the inspected induction, not this count.
    frame_checks = 0
    for initial in range(-128, 128):
        for label in range(-128, 128):
            for target in range(4):
                out = history([initial] * 4, [(target, label)])
                assert all(out[j] == initial for j in range(4) if j != target)
                frame_checks += 1

    return {
        'all_passed': True,
        'instrument': 'Python exact signed integers and // 8; independent of BitVec and gate circuit',
        'scope': 'Finite arithmetic and quantifier-boundary controls; no claim to exhaust arbitrary histories',
        'full_byte_pairs': full_byte_pairs,
        'monotonic_adjacent_pairs': monotonic_adjacent_pairs,
        'scaled_residual_histogram': dict(sorted(residuals.items())),
        'horizon': horizon,
        'fixed_points': fixed,
        'one_step_frame_checks': frame_checks,
        'invalid_weakenings': {
            'six_total_events_not_six_target_events': {
                'initial': [-120] * 4, 'events': count_only_events,
                'final': count_only, 'target': 2, 'desired_label': 120},
            'six_target_events_without_consistency': {
                'initial': [-120] * 4, 'events': inconsistent_events,
                'final': inconsistent, 'target': 2, 'desired_label': 120},
        },
    }
