#!/usr/bin/env python3
"""ALS16 section4.2 equation/noise witness with DELIBERATELY INSECURE parameters.

Small uniform secret entries and bounded deterministic errors do NOT instantiate
the source's Gaussian tau distribution or security parameters. This verifies only
algebra, residue semantics, continuing-state dataflow and explicit attacks.
"""
from __future__ import annotations
from dataclasses import dataclass
import hashlib
import itertools
import json
from pathlib import Path
import random
import sys


def dot(a, b):
    return sum(x * y for x, y in zip(a, b, strict=True))


def mv(a, v):
    return [dot(row, v) for row in a]


def mm(a, b):
    return [[dot(row, col) for col in zip(*b)] for row in a]


@dataclass
class Parameters:
    p: int
    q: int
    d: int
    n: int
    m: int
    A: list[list[int]]
    U: list[list[int]]

    @property
    def scale(self):
        assert self.q % self.p == 0
        return self.q // self.p


def setup(rng):
    p, q, d, n, m = 5, 5**6, 3, 2, 6
    A = [[rng.randrange(q) for _ in range(n)] for _ in range(m)]
    Z = [[rng.randrange(-2, 3) for _ in range(m)] for _ in range(d)]
    U = [[x % q for x in row] for row in mm(Z, A)]
    return Parameters(p, q, d, n, m, A, U), Z


def keygen(Z, vector):
    return [dot(vector, col) for col in zip(*Z)]


def encrypt(pp, plain, s, e0, e1):
    c0 = [(v + e) % pp.q for v, e in zip(mv(pp.A, s), e0, strict=True)]
    c1 = [(v + e + pp.scale * y) % pp.q
          for v, e, y in zip(mv(pp.U, s), e1, plain, strict=True)]
    return c0, c1


def encrypt_fresh(pp, plain, rng, errors=None):
    s = [rng.randrange(pp.q) for _ in range(pp.n)]
    if errors is None:
        e0 = [rng.randrange(-1, 2) for _ in range(pp.m)]
        e1 = [rng.randrange(-1, 2) for _ in range(pp.d)]
    else:
        e0, e1 = errors
    return encrypt(pp, plain, s, e0, e1), (s, e0, e1)


def public_add(pp, ct, observation):
    c0, c1 = ct
    return list(c0), [(v + pp.scale * u) % pp.q for v, u in zip(c1, observation, strict=True)]


def encrypted_add(pp, ct, observation_ct):
    return tuple([(a + b) % pp.q for a, b in zip(c, d, strict=True)]
                 for c, d in zip(ct, observation_ct, strict=True))


def phase(pp, ct, y, zy):
    return (dot(y, ct[1]) - dot(zy, ct[0])) % pp.q


def signed(value, modulus):
    value %= modulus
    return value if value <= modulus // 2 else value - modulus


def decode_modular(pp, value):
    # q=p^k: exactly p equally spaced slots around the residue circle.
    return ((value % pp.q + pp.scale // 2) // pp.scale) % pp.p


def noise(pp, ct, plain, y, zy):
    return signed(phase(pp, ct, y, zy) - pp.scale * (dot(plain, y) % pp.p), pp.q)


def floor_port_falsifier():
    q, p = 101, 5
    scale = q // p
    value = 0
    for count in range(1, 100):
        value = (value + scale) % q
        expected = count % p
        scores = [abs(signed(value - scale * candidate, q)) for candidate in range(p)]
        decoded = min(range(p), key=lambda candidate: (scores[candidate], candidate))
        if decoded != expected:
            return {"q": q, "p": p, "scale_floor": scale,
                    "public_plus_one_updates": count, "wraps": count // p,
                    "phase": value, "expected_plain_mod_p": expected, "decoded": decoded,
                    "wrap_residual_per_cycle": p * scale - q,
                    "classification": "naive floor-scaled modular port; not the ALS modular construction"}
    raise AssertionError("expected floor-port wrap failure")


def dependent_key_attack(rng):
    p = 5
    Z = [[rng.randrange(-3, 4) for _ in range(4)] for _ in range(2)]
    y1, y2 = [1, 2], [3, 1]
    z1, z2 = keygen(Z, y1), keygen(Z, y2)
    assert all(b == (3 * a) % p for a, b in zip(y1, y2, strict=True))
    # z1=row1+2row2; z2=3row1+row2; determinant=-5, invert over Q.
    recovered_row2 = [(3 * a - b) // 5 for a, b in zip(z1, z2, strict=True)]
    recovered_row1 = [a - 2 * b for a, b in zip(z1, recovered_row2, strict=True)]
    assert [recovered_row1, recovered_row2] == Z
    correct_lift2 = [3 * a for a in y1]
    correct_z2 = [3 * a for a in z1]
    assert correct_z2 == keygen(Z, correct_lift2)
    initial, alternative = [0, 0], [3, 1]
    assert dot(y1, initial) % p == dot(y1, alternative) % p
    assert dot(y2, initial) % p == dot(y2, alternative) % p
    return {"p": p, "requested_vectors": [y1, y2], "dependent_scalar_mod_p": 3,
            "naive_integer_determinant": -5, "master_recovered": True,
            "correct_lift_for_second": correct_lift2,
            "correct_second_key_is_three_times_first": True,
            "admissible_challenge_pair": [initial, alternative],
            "classification": "source-described attack on naive canonical independent issuance; correct stateful issuer prevents it"}


def main():
    rng = random.Random(2026090601)
    pp, Z = setup(rng)
    y = [1, 1, 0]
    zy = keygen(Z, y)
    initial, alternative = [1, 4, 3], [2, 3, 1]
    assert dot(y, initial) % pp.p == dot(y, alternative) % pp.p
    ct, coins = encrypt_fresh(pp, initial, rng)
    initial_noise = noise(pp, ct, initial, y, zy)
    assert abs(initial_noise) * 2 < pp.scale
    current, state = ct, initial
    outputs, states, errors = [decode_modular(pp, phase(pp, ct, y, zy))], [initial], [initial_noise]
    for u in ([3, 1, 2], [4, 2, 4]):
        current = public_add(pp, current, u)
        state = [(v + w) % pp.p for v, w in zip(state, u, strict=True)]
        assert current == encrypt(pp, state, *coins)
        states.append(state)
        outputs.append(decode_modular(pp, phase(pp, current, y, zy)))
        errors.append(noise(pp, current, state, y, zy))
    assert states == [[1, 4, 3], [4, 0, 0], [3, 2, 4]] and outputs == [0, 4, 0]
    assert errors == [initial_noise] * 3
    # Arbitrary finite-length public update loop, including many plaintext wraps.
    public_iterations = 10000
    for _ in range(public_iterations):
        u = [rng.randrange(pp.p) for _ in range(pp.d)]
        current = public_add(pp, current, u)
        state = [(v + w) % pp.p for v, w in zip(state, u, strict=True)]
        assert current == encrypt(pp, state, *coins)
        assert noise(pp, current, state, y, zy) == initial_noise
        assert decode_modular(pp, phase(pp, current, y, zy)) == dot(y, state) % pp.p
    # Exhaust all modular states and one-step commands under same fixed test coins.
    exhaustive_edges = 0
    for start in itertools.product(range(pp.p), repeat=pp.d):
        base = encrypt(pp, start, *coins)
        for update in itertools.product(range(pp.p), repeat=pp.d):
            post = tuple((a + b) % pp.p for a, b in zip(start, update, strict=True))
            assert public_add(pp, base, update) == encrypt(pp, post, *coins)
            exhaustive_edges += 1
    # Private encoded observations close algebraically but add error.
    private_state, private_ct = list(initial), ct
    s_total, e0_total, e1_total = [list(c) for c in coins]
    private_outputs, private_errors = [], []
    for u in ([3, 1, 2], [4, 2, 4]):
        uct, ucoins = encrypt_fresh(pp, u, rng)
        private_ct = encrypted_add(pp, private_ct, uct)
        private_state = [(a + b) % pp.p for a, b in zip(private_state, u, strict=True)]
        s_total = [(a + b) % pp.q for a, b in zip(s_total, ucoins[0], strict=True)]
        e0_total = [a + b for a, b in zip(e0_total, ucoins[1], strict=True)]
        e1_total = [a + b for a, b in zip(e1_total, ucoins[2], strict=True)]
        assert private_ct == encrypt(pp, private_state, s_total, e0_total, e1_total)
        private_outputs.append(decode_modular(pp, phase(pp, private_ct, y, zy)))
        private_errors.append(noise(pp, private_ct, private_state, y, zy))
    assert private_outputs == [4, 0]
    # Worst legal noise under this TOY bounded-support contract, no tail claims.
    e0_worst = [-((z > 0) - (z < 0)) for z in zy]
    e1_worst = [((v > 0) - (v < 0)) for v in y]
    E = sum(abs(v) for v in y) + sum(abs(z) for z in zy)
    assert dot(y, e1_worst) - dot(zy, e0_worst) == E
    zero = [0] * pp.d
    accum, _ = encrypt_fresh(pp, zero, rng, errors=([0] * pp.m, [0] * pp.d))
    first_failure = None
    for h in range(1, 10000):
        delta, _ = encrypt_fresh(pp, zero, rng, errors=(e0_worst, e1_worst))
        accum = encrypted_add(pp, accum, delta)
        actual_phase = phase(pp, accum, y, zy)
        assert actual_phase == (h * E) % pp.q
        output = decode_modular(pp, actual_phase)
        if output != 0:
            first_failure = {"added_zero_ciphertexts": h, "noise_per_ciphertext": E,
                             "total_error": h * E, "scale": pp.scale, "wrong_output": output,
                             "classification": "bounded-noise worst-case correctness falsifier; not an attack probability"}
            break
    assert first_failure is not None
    safe_additions_from_zero_noise = (pp.scale - 1) // (2 * E)
    assert first_failure['added_zero_ciphertexts'] == safe_additions_from_zero_noise + 1
    # Each standalone private input projects without any release/provenance gate.
    input_ct, _ = encrypt_fresh(pp, [3, 1, 2], rng)
    assert decode_modular(pp, phase(pp, input_ct, y, zy)) == 4
    substituted = ([0] * pp.m, [pp.scale * 3, 0, 0])
    assert decode_modular(pp, phase(pp, substituted, y, zy)) == 3
    master_recovered = [decode_modular(pp, phase(pp, current,
                        [int(i == j) for j in range(pp.d)], Z[i])) for i in range(pp.d)]
    assert master_recovered == state
    report = {
        "classification": "EXECUTED equation/noise witness with deliberately insecure parameters; not a secure LWE instantiation",
        "source": "ALS16 ePrint2015/608 section4.2 pp16-18, theorem3 and theorem4 pp20-22",
        "seed": 2026090601,
        "parameters": {"p": pp.p, "q": pp.q, "scale": pp.scale, "dimension": pp.d,
                       "lwe_dimension": pp.n, "lwe_samples": pp.m,
                       "secret_distribution": "uniform small entries -2..2 (NOT source tau)",
                       "error_distribution": "uniform bounded -1..1 / deterministic bounded witnesses (NOT source Gaussian)",
                       "security_bits": None},
        "fixed_projection": y, "test_projection_key_l1_norm": sum(abs(z) for z in zy),
        "initial": initial, "alternative": alternative,
        "two_public_updates": {"states": states, "outputs": outputs, "noise_values": errors},
        "public_update_iterations": public_iterations, "exhaustive_public_edges": exhaustive_edges,
        "two_private_encoded_updates": {"outputs": private_outputs, "noise_values": private_errors},
        "noise_contract": {"per_ciphertext_bound": E,
                           "equation": "epsilon_y=<y,e1>-<z_y,e0>",
                           "correctness_sufficient": "2*abs(epsilon_total)<q/p",
                           "safe_additions_starting_from_zero_noise": safe_additions_from_zero_noise,
                           "first_worst_case_failure": first_failure,
                           "zero_ciphertext_addition_is_not_noise_reset": True},
        "falsifiers": {"naive_floor_scaled_modular_port": floor_port_falsifier(),
                       "naive_mod_dependent_key_issuance": dependent_key_attack(rng),
                       "private_ingress_projection_leaks_before_gate": 4,
                       "unkeyed_substitution_releases_three": True,
                       "retained_master_reads_final_state": master_recovered,
                       "public_updates_create_no_new_unknown_state_input": True},
        "exact_counts": {"public_key_residues": (pp.m + pp.d) * pp.n,
                         "ciphertext_residues": pp.m + pp.d,
                         "fixed_function_key_integer_entries": pp.m,
                         "public_add_scalar_multiplies": pp.d,
                         "public_add_residue_additions": pp.d,
                         "private_ciphertext_add_residue_additions": pp.m + pp.d,
                         "fresh_encode_scalar_multiplies": (pp.m + pp.d) * pp.n + pp.d,
                         "projection_scalar_multiplies": pp.m + pp.d},
        "residuals": ["no source tau sampler/secure parameter instantiation", "no audited quantum lifting",
                      "common-kernel privacy only", "all input projections readable", "no release binding",
                      "no continuity", "noise horizon applies to fresh ciphertext additions, not public constant adds"],
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), "python": sys.version}
    out = Path(__file__).parent / 'results' / 'lwe_results.json'
    out.write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({k: report[k] for k in ('two_public_updates', 'public_update_iterations',
                     'exhaustive_public_edges', 'noise_contract', 'falsifiers')}, indent=2))


if __name__ == '__main__':
    main()
