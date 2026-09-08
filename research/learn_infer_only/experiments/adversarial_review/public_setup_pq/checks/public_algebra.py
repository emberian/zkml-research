#!/usr/bin/env python3
"""Exact public algebra only: no keygen, encryption, decryption or private files.

The phase check rounds explicitly supplied public integers. It is not a
cryptographic implementation or a security experiment.
"""

import hashlib
import itertools
import json
from pathlib import Path


def mv(matrix, vector, p):
    return tuple(sum(a * b for a, b in zip(row, vector)) % p for row in matrix)


def center(x, p):
    return (x + p // 2) % p - p // 2


def closest_grid_residue(phase, p, delta):
    q = p * delta
    distances = [abs(center(phase - delta * x, q)) for x in range(p)]
    best = min(distances)
    winners = [x for x, distance in enumerate(distances) if distance == best]
    assert len(winners) == 1
    return winners[0]


def main():
    basis = ((1, 0, 1), (0, 1, 1), (0, 0, 1))
    inverse = ((1, 0, -1), (0, 1, -1), (0, 0, 1))
    rows = basis[:2]
    direction = (-1, -1, 1)
    basis_checks = 0
    witness_checks = 0
    for p in (2, 3, 5, 7):
        assert mv(rows, direction, p) == (0, 0)
        assert mv(basis, direction, p) == (0, 0, 1)
        for x in itertools.product(range(p), repeat=3):
            transformed = mv(basis, x, p)
            assert mv(inverse, transformed, p) == x
            basis_checks += 1
            paired = tuple((a + h) % p for a, h in zip(x, direction))
            assert x != paired
            assert mv(rows, x, p) == mv(rows, paired, p)
            assert x[2] != paired[2]
            witness_checks += 1

    p, delta = 5, 25
    phase_checks = 0
    max_abs_error = 0
    for a, b in itertools.product(range(p), repeat=2):
        for ea, eb, wa, wb in itertools.product(range(-2, 3), repeat=4):
            phase = wa * (delta * a + ea) + wb * (delta * b + eb)
            error = wa * ea + wb * eb
            assert 2 * abs(error) < delta
            assert closest_grid_residue(phase, p, delta) == (wa * a + wb * b) % p
            max_abs_error = max(max_abs_error, abs(error))
            phase_checks += 1

    # A public witness for the necessity of the strict rounding-radius bound.
    # No secret vector, public key, ciphertext, or cryptographic code is made.
    outside_radius = {
        "p": p,
        "delta": delta,
        "intended_residue": 0,
        "supplied_phase_error": 13,
        "nearest_grid_residue": closest_grid_residue(13, p, delta),
    }
    assert outside_radius["nearest_grid_residue"] == 1

    integer_wrap = {
        "p": 5,
        "integer_state": [2, 2, 2],
        "integer_readouts": [4, 4],
        "field_readouts": list(mv(rows, (2, 2, 2), 5)),
        "centered_readouts": [center(4, 5), center(4, 5)],
    }
    assert integer_wrap["centered_readouts"] == [-1, -1]

    # Symbolic coefficients on formal rows (U_1,U_2,U_3): a swap of rows
    # 1 and 3 leaves residual U_3-U_1 when subtracting the old row-1 term.
    transformed_row_1 = (0, 0, 1)
    old_key_row_1 = (1, 0, 0)
    residual = tuple(a - b for a, b in zip(transformed_row_1, old_key_row_1))
    assert residual == (-1, 0, 1)
    assert residual != (0, 0, 0)

    report = {
        "scope": "Exact public algebra; no cryptographic execution or private inputs",
        "basis_roundtrips": basis_checks,
        "equal_output_distinct_state_pairs": witness_checks,
        "phase_combination_checks": phase_checks,
        "phase_grid": {"p": p, "delta": delta, "q": p * delta},
        "max_absolute_error_in_passing_checks": max_abs_error,
        "outside_radius_witness": outside_radius,
        "integer_wrap_witness": integer_wrap,
        "unsupported_matrix_update_symbolic_residual_coefficients": residual,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "result": "PASS",
    }
    print(json.dumps(report, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
