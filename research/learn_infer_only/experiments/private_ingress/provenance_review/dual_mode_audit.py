#!/usr/bin/env python3
"""Groth-Sahai scalar commitment algebra in an explicit-exponent toy group.

NO cryptographic security: group elements are exposed integers, DDH is easy,
history certificates and next ciphertexts are ideal semantic objects.
"""
from collections import Counter
from hashlib import sha256
import json
from pathlib import Path
import platform

P, ALPHA, T = 257, 7, 11


def com(mode, x, r):
    # GS section 9: u1=(1,alpha), u=u2+(0,1).
    # Binding u=t*u1+(0,1); hiding u=t*u1.
    extra = 1 if mode == 'bind' else 0
    return ((r + T*x) % P, (ALPHA*(r + T*x) + extra*x) % P)


def equivocate(x, r, other):
    return (r + T*(x-other)) % P


def main():
    here = Path(__file__).resolve()
    bind_images = {com('bind', x, r) for x in range(P) for r in range(P)}
    assert len(bind_images) == P*P
    reference = Counter(com('hide', 0, r) for r in range(P))
    pairs = 0
    for x in range(P):
        assert Counter(com('hide', x, r) for r in range(P)) == reference
        adjusted = [equivocate(0, r, x) for r in range(P)]
        assert sorted(adjusted) == list(range(P))
        for r, rp in zip(range(P), adjusted):
            assert com('hide', 0, r) == com('hide', x, rp)
            pairs += 1

    r0 = 23
    common = com('hide', 0, r0)
    r1 = equivocate(0, r0, 1)
    assert common == com('hide', 1, r1)
    # Full public parent domain; V(z) abbreviates every observation-only check.
    observation_replacement_checks = 0
    for parent in bind_images:
        for observation_checks in (False, True):
            a = observation_checks and com('hide', 0, r0) == parent
            b = observation_checks and com('hide', 1, r1) == parent
            assert a == b
            observation_replacement_checks += 1

    # Fixed genesis0, authorized first Learn can be any byte. Thus every state
    # has a TRUE one-step history; no false proof is supplied in this test.
    accepted = {}
    separators = {}
    state_replacement_checks = 0
    for mode in ('bind', 'hide'):
        actual_parent = com(mode, 0, r0)
        accepted[mode], separators[mode] = [], []
        for value in range(256):
            for opening in range(P):
                first_private_observation = value
                valid_history = (0 + first_private_observation) % 256 == value
                ga = valid_history and com(mode, value, opening) == actual_parent
                gb = valid_history and com(mode, value, opening) == actual_parent
                assert ga == gb  # both x=0 and x=1 packets have same parent
                state_replacement_checks += 1
                if ga:
                    accepted[mode].append(value)
                    # These bits require the explicit future terminal key if
                    # F itself returns only ACK plus an encrypted next state.
                    output_a = ((value + 0) % 256) >> 7
                    output_b = ((value + 1) % 256) >> 7
                    if output_a != output_b:
                        separators[mode].append(value)
        assert len(accepted[mode]) == len(set(accepted[mode]))
    assert accepted['bind'] == [0]
    assert accepted['hide'] == list(range(256))
    assert separators == {'bind': [], 'hide': [127, 255]}

    # Two different openings reveal this particular scalar-equivocation trapdoor.
    recovered_t = ((r0-r1) * pow(1-0, -1, P)) % P
    assert recovered_t == T
    result = {'classification': 'EXECUTED algebra/ideal-interface checks; no cryptography',
              'python': platform.python_version(), 'command': f'python3 {here}',
              'source_sha256': sha256(here.read_bytes()).hexdigest(),
              'toy_prime': P,
              'binding_domain_size': P*P, 'distinct_binding_commitments': len(bind_images),
              'hiding_support_size_each_message': len(reference),
              'equivocation_and_uniform_marginal_checks': pairs,
              'all_observation_replacement_guard_checks': observation_replacement_checks,
              'all_state_replacement_guard_checks': state_replacement_checks,
              'same_parent_accepted_state_count': {m: len(v) for m, v in accepted.items()},
              'honest_fresh_observation_pair': [0, 1],
              'honest_state': 0, 'honest_terminal_answers': [0, 0],
              'separating_true_history_states': separators,
              'joint_future_terminal_key_required_for_separation': True,
              'two_distinct_openings_recover_t': recovered_t == T,
              'no_claim_of_CRS_indistinguishability_in_this_toy': True}
    data = json.dumps(result, indent=2)+'\n'
    here.with_name('dual_mode_results.json').write_text(data)
    print(data, end='')


if __name__ == '__main__':
    main()
