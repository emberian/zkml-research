#!/usr/bin/env python3
"""Reference algebra for ABDP15 Construction 3.1 in RFC3526 group14.

This is not constant-time or production cryptography; no security strength or PQ
claim is made. The paper's selective DDH theorem is distinct from these tests.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import secrets
import sys

# RFC3526 section3: 2048-bit MODP group14, g=2. Q names subgroup order here.
P = int("""
FFFFFFFF FFFFFFFF C90FDAA2 2168C234 C4C6628B 80DC1CD1
29024E08 8A67CC74 020BBEA6 3B139B22 514A0879 8E3404DD
EF9519B3 CD3A431B 302B0A6D F25F1437 4FE1356D 6D51C245
E485B576 625E7EC6 F44C42E9 A637ED6B 0BFF5CB6 F406B7ED
EE386BFB 5A899FA5 AE9F2411 7C4B1FE6 49286651 ECE45B3D
C2007CB8 A163BF05 98DA4836 1C55D39A 69163FA8 FD24CF5F
83655D23 DCA3AD96 1C62F356 208552BB 9ED52907 7096966D
670C354E 4ABC9804 F1746C08 CA18217C 32905E46 2E36CE3B
E39E772C 180E8603 9B2783A2 EC07A28F B5C55DF0 6F4C52C9
DE2BCBF6 95581718 3995497C EA956AE5 15D22618 98FA0510
15728E5A 8AACAA68 FFFFFFFF FFFFFFFF
""".replace(" ", "").replace("\n", ""), 16)
Q = (P - 1) // 2
G = 2
D = 3
Y = (1, 1, 0)
DECODE_LOW, DECODE_HIGH = -64, 64


def dot(x, y):
    return sum(a * b for a, b in zip(x, y, strict=True))


def add(x, y):
    return tuple(a + b for a, b in zip(x, y, strict=True))


def setup():
    msk = tuple(secrets.randbelow(Q) for _ in range(D))
    mpk = tuple(pow(G, s, P) for s in msk)
    return mpk, msk


def encrypt(mpk, x, coins=None):
    if len(x) != D or len(mpk) != D:
        raise ValueError("dimension")
    r = secrets.randbelow(Q) if coins is None else coins % Q
    return (pow(G, r, P),) + tuple((pow(h, r, P) * pow(G, v % Q, P)) % P
                                  for h, v in zip(mpk, x, strict=True))


def combine(c1, c2):
    if len(c1) != D + 1 or len(c2) != D + 1:
        raise ValueError("dimension")
    return tuple((a * b) % P for a, b in zip(c1, c2, strict=True))


def keyder(msk, y):
    return dot(msk, y) % Q


def project_group(ct, sky, y=Y, validate=True):
    if len(ct) != D + 1 or len(y) != D:
        raise ValueError("dimension")
    if validate and any(not 1 <= c < P or pow(c, Q, P) != 1 for c in ct):
        raise ValueError("not a canonical subgroup element")
    value = pow(pow(ct[0], sky, P), -1, P)
    for c, v in zip(ct[1:], y, strict=True):
        value = (value * pow(c, v % Q, P)) % P
    return value


def decode_table():
    return {pow(G, i % Q, P): i for i in range(DECODE_LOW, DECODE_HIGH + 1)}


def decode(value, table):
    if value not in table:
        raise ValueError("outside declared integer output interval")
    return table[value]


def main():
    assert P.bit_length() == 2048 and pow(G, Q, P) == 1 and G != 1
    table = decode_table()
    mpk, msk = setup()
    sky = keyder(msk, Y)
    initial = (1, 4, 6)
    alternative = (2, 3, 11)
    updates = [(3, 1, 2), (-1, 2, -4)]
    # Exact equality of algebraic encryption with summed coins; synthetic audit only.
    c0 = encrypt(mpk, initial, coins=7)
    u0 = encrypt(mpk, updates[0], coins=11)
    u1 = encrypt(mpk, updates[1], coins=13)
    c1 = combine(c0, u0)
    c2 = combine(c1, u1)
    expected_states = [initial, add(initial, updates[0]), add(add(initial, updates[0]), updates[1])]
    assert c1 == encrypt(mpk, expected_states[1], coins=18)
    assert c2 == encrypt(mpk, expected_states[2], coins=31)
    outputs = [decode(project_group(ct, sky), table) for ct in (c0, c1, c2)]
    assert outputs == [5, 9, 10]
    # A real randomly generated initial ciphertext and updates close too.
    fresh0 = encrypt(mpk, initial)
    fresh1 = combine(fresh0, encrypt(mpk, updates[0]))
    fresh2 = combine(fresh1, encrypt(mpk, updates[1]))
    assert [decode(project_group(ct, sky), table) for ct in (fresh0, fresh1, fresh2)] == outputs
    # All public additions preserve common-kernel differences, with actual raw vector retained.
    invariant_checks = 0
    for dx in range(-5, 6):
        for dy in range(-5, 6):
            for dz in range(-2, 3):
                offset = (dx, dy, dz)
                assert dot(add(initial, offset), Y) == dot(add(alternative, offset), Y)
                invariant_checks += 1
    # Reachable known function keys include the entire scalar span of issued keys.
    span_checks = 0
    for scalar in (-3, -1, 0, 1, 2, 3):
        yprime = tuple(scalar * v for v in Y)
        derived = (scalar * sky) % Q
        assert derived == keyder(msk, yprime)
        assert decode(project_group(c2, derived, yprime), table) == scalar * outputs[-1]
        span_checks += 1
    # Retained initialization master reads all coordinates: direct falsifier.
    recovered = []
    for i in range(D):
        basis = tuple(int(j == i) for j in range(D))
        recovered.append(decode(project_group(c2, keyder(msk, basis), basis), table))
    assert tuple(recovered) == expected_states[-1]
    # Public ingress has no master secret, but its projection leaks BEFORE any gate.
    ingress_projections = [decode(project_group(u, sky), table) for u in (u0, u1)]
    assert ingress_projections == [4, 1]
    # Encryption coins expose the entire associated input, not other ciphertexts.
    input_recovered_from_coins = tuple(decode((c * pow(pow(h, 11, P), -1, P)) % P, table)
                                       for c, h in zip(u0[1:], mpk, strict=True))
    assert input_recovered_from_coins == updates[0]
    # No output authenticity: anyone public-encrypts a chosen vector and gets its answer.
    substituted = encrypt(mpk, (42, 0, 0))
    assert decode(project_group(substituted, sky), table) == 42
    # The decoder interval is NOT a cryptographic leakage gate: group value remains.
    outside_group = project_group(encrypt(mpk, (77, 0, 0)), sky)
    assert outside_group == pow(G, 77, P)
    try:
        decode(outside_group, table)
    except ValueError:
        outside_decode_refused = True
    else:
        outside_decode_refused = False
    assert outside_decode_refused
    # Our input membership check rejects non-group elements, a separate wrapper obligation.
    malformed_rejections = 0
    for bad in (0, P, P - 1):
        malformed = (bad,) + c0[1:]
        try:
            project_group(malformed, sky)
        except ValueError:
            malformed_rejections += 1
    assert malformed_rejections == 3
    # A supported nonlinear transition would expose the retained hidden distinction.
    square_first = lambda x: (x[0] ** 2, x[1], x[2])
    assert dot(square_first(initial), Y) == 5
    assert dot(square_first(alternative), Y) == 7
    # Ciphertext re-randomization cannot create unknown learned-state randomness.
    refreshed = combine(fresh2, encrypt(mpk, (0, 0, 0)))
    assert decode(project_group(refreshed, sky), table) == outputs[-1]
    assert refreshed != fresh2
    # Raw ciphertexts remain available after restore; no continuity mechanism.
    assert decode(project_group(c0, sky), table) == 5
    report = {
        "classification": "executed reference DDH-IPFE algebra; sourced selective security, no deployed-system claim",
        "source": "ePrint2015/017 Construction3.1 and Theorem3.2 printedpp7-8",
        "group": {"source": "RFC3526 section3 group14", "modulus_bits": P.bit_length(),
                  "subgroup_order_bits": Q.bit_length(), "generator": G,
                  "modulus_sha256": hashlib.sha256(P.to_bytes(256, "big")).hexdigest(),
                  "security_bits": None, "post_quantum": False},
        "dimension": D, "issued_projection": Y, "issued_span_rank": 1,
        "common_kernel_dimension": D - 1, "initial": initial, "alternative": alternative,
        "public_updates": updates, "represented_states": expected_states,
        "authorized_outputs": outputs, "fixed_output_decode_interval": [DECODE_LOW, DECODE_HIGH],
        "invariant_additions_checked": invariant_checks, "derived_span_keys_checked": span_checks,
        "positive": {"two_ct_updates_equal_direct_encryption_with_summed_coins": True,
                     "fresh_randomized_ct_loop_matches": True,
                     "ciphertext_zero_refresh_preserves_state": True},
        "falsifiers": {"retained_master_recovers_all_final_coordinates": recovered,
                       "ingress_projection_visible_before_release": ingress_projections,
                       "retained_input_coins_recover_whole_input": input_recovered_from_coins,
                       "public_ciphertext_substitution_returns_42": True,
                       "outside_decoder_interval_projection_77_still_testable": True,
                       "nonlinear_square_exposes_hidden_pair": [5, 7],
                       "restored_snapshot_still_reads_old_projection": 5},
        "malformed_group_elements_rejected": malformed_rejections,
        "exact_counts": {"state_ciphertext_group_elements": D + 1,
                         "state_ciphertext_fixed_width_bytes": (D + 1) * 256,
                         "master_public_group_elements": D,
                         "exposed_function_key_scalars": 1,
                         "online_encoding_modexp": 2 * D + 1,
                         "online_encoding_group_multiplications": D,
                         "learn_add_group_multiplications": D + 1,
                         "projection_membership_checks_modexp": D + 1,
                         "projection_general_modexp_excluding_membership": D + 1,
                         "projection_mod_inverse": 1,
                         "decode_table_entries": DECODE_HIGH - DECODE_LOW + 1,
                         "decode_table_precompute_modexp_as_executed": DECODE_HIGH - DECODE_LOW + 1},
        "privacy_scope": "selective initial pair; fixed keys; public adaptive additions and forkable projection reads; honest initializer erases master, plaintext and coins",
        "residuals": ["Python pow is not constant-time", "no proof implementation matches source reduction",
                      "no quantum security", "no neural utility", "no hidden nonlinearity",
                      "no private projected input secrecy", "no output binding or continuity",
                      "no security-strength calibration", "source theorem not a simulation theorem"],
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "python": sys.version}
    target = Path(__file__).parent / "results" / "ipfe_results.json"
    target.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("represented_states", "authorized_outputs", "falsifiers", "exact_counts")}, indent=2))


if __name__ == "__main__":
    main()
