#!/usr/bin/env python3
"""Exact finite support counts and sizing inequalities; NO cryptography."""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import json
import platform


def ceil_log2(n):
    return (n-1).bit_length()


def seeded_support_control():
    h, declared_coins, next_parameter, current_s, n = 3, 64, 128, 4, 2
    # A deterministic expansion preserves the support size of its short seed.
    def output(message, seed):
        expanded = tuple((seed >> (j % h)) & 1 for j in range(next_parameter))
        return message, expanded
    left = [output(0, seed) for seed in range(2**h)]
    right = [output(1, seed) for seed in range(2**h)]
    event = Fraction(left.count(output(0, 0)), len(left))
    assert event == Fraction(1, 2**h)
    assert output(0, 0) not in right
    exponent = 2*n*current_s+h
    assert event > Fraction(1, 2**exponent)
    return {'classification': 'EXECUTED injective tuple support control; no encryption',
            'effective_seed_bits': h, 'declared_coin_tape_bits': declared_coins,
            'expanded_next_coin_bits': next_parameter,
            'left_fixed_output_mass': str(event), 'right_mass': '0',
            'epsilon_exponent': exponent, 'padding_or_stretching_does_not_fix': True}


def collision_control():
    # The left zero-coin output is deliberately the rare output, so this also
    # checks that sampling avoids assuming efficient access to a heaviest atom.
    left = [1] + [0]*7
    right = [2]*4 + [3]*4
    distribution = Counter(left)
    collision = sum((Fraction(v, len(left))**2 for v in distribution.values()), Fraction(0))
    cross = sum(Fraction(x == y, len(left)*len(right)) for x in left for y in right)
    assert collision == Fraction(25, 32) and cross == 0
    assert collision >= Fraction(1, 2**2)
    return {'classification': 'EXECUTED finite sample-collision identity',
            'projection_bits': 2, 'left_collision': str(collision),
            'right_against_left_sample': str(cross),
            'general_projection_bound': '2^(-projection_bits)',
            'rare_fixed_left_output_probability': '1/8'}


def sizing_family(k, stronger_rate=False):
    # Illustrative coherent dimensions, not a realized PKE or security claim.
    # Current message width excludes next FE key/ciphertext encodings.
    message_bits, payload_coins, proof_coins = 16*k**3, k, k**3
    metadata_bits = 4*k**3+4*k+2*k**2+32
    assert metadata_bits < message_bits
    security = [k]
    ciphertext_bits = []
    rows = []
    for layer in range(3):
        current = security[layer]
        s = 2*current+message_bits
        ciphertext_bits.append(s)
        if layer == 2:
            break
        E = 4*s+current
        if stronger_rate:
            next_security = (2*E)**2
        else:
            next_security = 8*s+2*current+2*payload_coins+1
        next_s = 2*next_security+message_bits
        coin_bits = payload_coins+2*next_security+proof_coins
        # Pick polynomial illustrative authentication/proof dimensions too.
        next_auth_bits = (6*next_s+next_security+1)**2
        output_bits = 2*next_s+next_auth_bits+metadata_bits+1
        # A deliberately generous explicit circuit-description budget: the
        # comparison only needs it polynomial, not a succinct representation.
        description_bits = (output_bits+coin_bits+next_security+1)**3
        assert payload_coins+next_security > E
        assert next_s > E and coin_bits > E
        assert output_bits > s and description_bits > s
        row = {'layer': layer, 'lambda_current': current, 'input_bits': message_bits,
               's_current_PKE_bits': s, 'epsilon_exponent_E': E,
               'lambda_next': next_security, 's_next_PKE_bits': next_s,
               'payload_coin_plus_first_PKE_exponent': payload_coins+next_security,
               'function_coin_bits_ellR': coin_bits,
               'function_output_bits_ellY': output_bits,
               'illustrative_description_budget_ellF': description_bits,
               'metadata_carried_into_next_input_bits': metadata_bits,
               'all_three_lower_bound_exponents_exceed_E': True}
        if stronger_rate:
            # Hypothetical explicit WHOLE-joint-package upper bound:
            # delta(t) <= t^3 * 2^(-sqrt(t)). No source proof supplies it here.
            exact_root = 2*E
            safe_exponent = exact_root-3*ceil_log2(next_security)
            assert safe_exponent >= E
            row['hypothetical_upper_bound_safe_exponent'] = safe_exponent
        rows.append(row)
        security.append(next_security)
    return {'classification': 'EXECUTED dimension inequalities only, no security realization',
            'base_parameter': k, 'horizon': 2,
            's_model': 's(lambda,M)=2*lambda+M',
            'hypothetical_explicit_rate_used': stronger_rate,
            'security_parameters': security, 'PKE_ciphertext_bits': ciphertext_bits,
            'rows': rows}


def negligible_rate_control():
    results = []
    for log_base in (20, 30):
        current = 2**log_base
        for polynomial_degree in (1, 2, 4):
            # t=lambda^d; a(t)=2^[-(log2 t)^2] is negligible in t.
            weak_exponent = (polynomial_degree*log_base)**2
            E = 25*current  # Independent rate example: s=6*lambda and n=2
            assert weak_exponent < E
            results.append({'lambda_current_log2': log_base,
                            'next_parameter_polynomial_degree': polynomial_degree,
                            'weak_negligible_rate_exponent': weak_exponent,
                            'required_epsilon_exponent': E})
    return {'classification': 'EXECUTED exponent comparisons; asymptotic proof in note',
            'rate': 'a(t)=2^[-(log2 t)^2]', 'examples': results}


def main():
    script = Path(__file__).resolve()
    result = {'classification': 'EXECUTED symbolic parameter/support audit only',
              'command': f'python3 {script}', 'python': platform.python_version(),
              'source_sha256': sha256(script.read_bytes()).hexdigest(),
              'short_seed_falsifier': seeded_support_control(),
              'collision_bound': collision_control(),
              'sizing_escape': sizing_family(16),
              'hypothetical_quantitative_sizing': sizing_family(16, True),
              'negligible_does_not_mean_exponentially_small': negligible_rate_control()}
    data = json.dumps(result, indent=2)+'\n'
    script.with_name('parameter_results.json').write_text(data)
    print(data, end='')


if __name__ == '__main__':
    main()
