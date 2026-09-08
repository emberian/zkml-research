#!/usr/bin/env python3
"""Frozen EMA mathematical/source review. No Rust, ciphertext, key, or crypto execution."""
from pathlib import Path
import hashlib
import itertools
import json
import re

HERE = Path(__file__).resolve().parent
BASE = HERE.parents[2]
AUTHOR = BASE / 'formal/private_address_ema'
RUST = BASE / 'experiments/end_to_end/private_ema/src/lib.rs'
EXPECTED = {
    AUTHOR / 'Theory/PrivateAddressEma.lean': '0b148bff8a53447bc9f30950948771a4b0f53edeb1110cc78f44e85a960d562d',
    AUTHOR / 'minidregg-private-address-ema.patch': '9fabd5d64ab3280dde1bbb1affab9ced9d5835f248f984dd4bb9d0488622ebae',
    RUST: 'fad1864642ff6c0036cdfed66b93bc7e21bb2720572d0ddd30b6effa2c65c880',
}

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

for path, expected in EXPECTED.items():
    assert digest(path) == expected, path

lean = (AUTHOR / 'Theory/PrivateAddressEma.lean').read_text()
theorems = re.findall(r'^theorem\s+(\w+)\b', lean, re.M)
pins = re.findall(r'^#guard_msgs[^\n]*#print axioms Minidregg\.Theory\.PrivateAddressEma\.(\w+)', lean, re.M)
assert len(theorems) == len(set(theorems)) == 28
assert theorems == pins
assert not re.search(r'^\s*(?:axiom|opaque)\s|\bsorry\b|\bnative_decide\b', lean, re.M)

def signed(word, width):
    return word - (1 << width) if word >= (1 << (width - 1)) else word

min_num, max_num = 0, 0
pair_count = 0
for s in range(-128, 128):
    for u in range(-128, 128):
        s11, u11 = s & 2047, u & 2047
        eight_s = (s & 255) << 3
        assert eight_s == ((s11 << 3) & 2047)
        not_s = (~s11) & 2047
        seven_s = (eight_s + not_s + 1) & 2047
        assert signed(seven_s, 11) == 7 * s
        numerator = (seven_s + u11) & 2047
        assert signed(numerator, 11) == 7 * s + u
        answer = signed(numerator >> 3, 8)
        assert answer == (7 * s + u) // 8
        assert -128 <= answer <= 127
        min_num = min(min_num, 7 * s + u)
        max_num = max(max_num, 7 * s + u)
        pair_count += 1
assert (min_num, max_num) == (-1024, 1016)

for n in range(2048):
    assert signed(n >> 3, 8) == signed(n, 11) // 8

addresses = []
for a in range(4):
    a0, a1 = bool(a & 1), bool(a & 2)
    chosen = []
    for j in range(4):
        b0 = a0 if j & 1 else not a0
        b1 = a1 if j & 2 else not a1
        chosen.append(b0 and b1)
    assert chosen == [j == a for j in range(4)]
    addresses.append({'address': a, 'wire0': a0, 'wire1': a1, 'selected': chosen})

infer_cases = 0
for signs in itertools.product([False, True], repeat=4):
    for q in range(4):
        low = signs[1] if q & 1 else signs[0]
        high = signs[3] if q & 1 else signs[2]
        answer = high if q & 2 else low
        assert answer == signs[q]
        infer_cases += 1

full_adder_cases = 0
for x, y, c in itertools.product([False, True], repeat=3):
    p = x ^ y
    out = p ^ c
    xy, pc = x and y, p and c
    carry = xy ^ pc
    assert not (xy and pc)
    assert int(out) + 2 * int(carry) == int(x) + int(y) + int(c)
    full_adder_cases += 1

invariant_cases = 0
for s in range(-120, 121):
    for u in [-120, 120]:
        assert -120 <= (7 * s + u) // 8 <= 120
        invariant_cases += 1

witnesses = {
    'nonvacuous_premise': {'old': 0, 'label': 120, 'address': 3, 'updated': 15},
    'satisfying_subject': {'state': [0, 0, 0, 0], 'label': -120, 'address': 3,
                           'next': [0, 0, 0, -15], 'query': 3, 'negative': True},
    'floor_vs_truncation': {'old': 1, 'label': -8, 'numerator': -1, 'floor': -1, 'trunc': 0},
    'ten_bit_width': {'old': -128, 'label': -128, 'numerator': -1024,
                     'narrowed_numerator': 0, 'correct_output': -128},
    'unselected': {'old': 0, 'label': 120, 'learn_address': 3, 'register': 0,
                   'selected_output': 0, 'unconditional_output': 15},
    'carry_drop': {'width': 1, 'a': 1, 'b': 1, 'initial_carry': 0,
                   'output': 0, 'final_carry': 1, 'integer_sum': 2},
    'invariant_premise_needed': {'old': -120, 'disallowed_label': -128,
                               'output': (7 * -120 - 128) // 8},
}
assert witnesses['invariant_premise_needed']['output'] == -121

paths_read = list(EXPECTED) + [
    BASE / 'experiments/end_to_end/private_ema/src/bin/issuer.rs',
    BASE / 'experiments/end_to_end/private_ema/src/bin/host.rs',
    BASE / 'experiments/end_to_end/private_ema/Cargo.toml',
    Path('/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/tfhe-1.6.3/src/boolean/server_key/mod.rs'),
]
results = {
    'scope': 'Independent cleartext finite mathematics and static source review only; does not execute Rust/TFHE or realize its trace in Lean.',
    'source_pins': {str(p): digest(p) for p in paths_read},
    'theorem_count': len(theorems), 'pin_count': len(pins), 'theorem_pin_order_equal': theorems == pins,
    'theorems': theorems,
    'all_signed_byte_pairs_checked': pair_count,
    'signed_numerator_min_max': [min_num, max_num],
    'all_eleven_bit_extractions_checked': 2048,
    'address_selection_cases_checked': 16,
    'address_truth_table': addresses,
    'all_sign_pattern_query_cases_checked': infer_cases,
    'full_adder_truth_table_cases_checked': full_adder_cases,
    'strict_subrange_endpoint_label_cases_checked': invariant_cases,
    'witnesses': witnesses,
    'forbidden_proof_constructs_found': [],
    'frozen_hashes_unchanged': all(digest(p) == h for p, h in EXPECTED.items()),
    'cryptographic_operations_executed': 0,
    'query_counts': {'web': 0, 'scry_sql': 0, 'scry_schema': 0, 'kagi': 0},
    'all_checks_passed': True,
}
(HERE / 'results.json').write_text(json.dumps(results, indent=2) + '\n')
print(json.dumps(results, indent=2))
