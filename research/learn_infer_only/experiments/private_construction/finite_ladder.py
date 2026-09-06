#!/usr/bin/env python3
"""Symbolic independent-key FE ladder: schedules, ideal traces, proof shape.

No cryptography is implemented. Tokens are opaque handles in a trusted test
registry, not an encryption construction. Source-backed conditional security is
argued separately in FINITE_LADDER.md.
"""
from collections import defaultdict
import hashlib
import itertools
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
MIRROR = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')
COMMANDS = ('add_one', 'double', 'infer')


def step(state, command):
    if command == 'add_one':
        return (state + 1) % 256, 'ACK'
    if command == 'double':
        return 2 * state % 256, 'ACK'
    if command == 'infer':
        return state, state >> 7
    raise ValueError(command)


def run_clear(state, commands):
    answers, states = [], [state]
    for command in commands:
        state, answer = step(state, command)
        states.append(state)
        answers.append(answer)
    return tuple(answers) + (state >> 7,), states


def profile(state, horizon):
    return tuple(run_clear(state, path)[0]
                 for path in itertools.product(COMMANDS, repeat=horizon))


class SymbolicLadder:
    """A typed ideal functionality; never serialized as a cryptographic claim."""
    def __init__(self, horizon):
        self.horizon = horizon
        self.events, self.public_keys, self.function_keys = [], {}, {}
        self.live_masters, self.registry = set(), {}
        self._setup_events, self._function_events = {}, {}
        self._compile(0)

    def event(self, action, **data):
        self.events.append({'index': len(self.events), 'action': action, **data})
        return len(self.events) - 1

    def _compile(self, layer):
        if layer < self.horizon:
            self._compile(layer + 1)
            assert layer + 1 in self.public_keys
            names = COMMANDS
            embedded = layer + 1
        else:
            names, embedded = ('terminal_read',), None
        # This ordering, rather than the cryptographic Setup algorithm itself,
        # is what matches the source's IND_pre experiment.
        for name in names:
            self._function_events[layer, name] = self.event(
                'define_function', layer=layer, name=name,
                embedded_public_key_layer=embedded)
        self._setup_events[layer] = self.event('setup', layer=layer)
        self.public_keys[layer] = f'public-key-{layer}'
        self.live_masters.add(layer)
        for name in names:
            self.issue(layer, name)
        self.live_masters.remove(layer)
        self.event('erase_raw_setup_and_keygen_secrets', layer=layer)

    def issue(self, layer, name):
        if layer not in self.live_masters:
            raise PermissionError('symbolic master has been erased')
        key = (layer, name)
        self.function_keys[key] = f'issued-key-{layer}-{name}'
        self.event('issue_key', layer=layer, name=name)

    def encrypt(self, layer, state):
        if layer not in self.public_keys:
            raise ValueError('no such public key')
        token = f'opaque-handle-{len(self.registry)}'
        self.registry[token] = (layer, state)
        return token

    def evaluate(self, layer, name, token):
        if (layer, name) not in self.function_keys:
            raise PermissionError('no issued key')
        actual_layer, state = self.registry[token]
        if layer != actual_layer:
            raise ValueError('symbolic layer type mismatch')
        if name == 'terminal_read':
            return None, state >> 7
        next_state, answer = step(state, name)
        # Deterministic ciphertext/key caching is modeled by memoization.
        cache_name = (layer, name, token)
        if not hasattr(self, 'cache'):
            self.cache = {}
        if cache_name not in self.cache:
            self.cache[cache_name] = self.encrypt(layer + 1, next_state)
        return self.cache[cache_name], answer

    def exposed_inventory(self):
        return {'public_keys': dict(self.public_keys),
                'all_function_keys': [list(key) for key in self.function_keys],
                'raw_masters': sorted(self.live_masters),
                'registry_exposed': False}


def acyclic(edges):
    adjacency = defaultdict(list)
    for source, target in edges:
        adjacency[source].append(target)
        adjacency[target]
    visiting, done = set(), set()
    def visit(node):
        if node in visiting:
            return False
        if node in done:
            return True
        visiting.add(node)
        if not all(visit(child) for child in adjacency[node]):
            return False
        visiting.remove(node)
        done.add(node)
        return True
    return all(visit(node) for node in list(adjacency))


def schedule_control(horizon=2):
    ladder = SymbolicLadder(horizon)
    for (layer, name), defined in ladder._function_events.items():
        assert defined < ladder._setup_events[layer]
        if layer < horizon:
            assert ladder._setup_events[layer + 1] < defined
    assert not ladder.live_masters
    erased_refusals = 0
    for layer in range(horizon + 1):
        try:
            ladder.issue(layer, 'identity_export')
        except PermissionError:
            erased_refusals += 1
    assert erased_refusals == horizon + 1
    # A back-edge would require root pk before terminal function definition,
    # which must precede terminal setup; the forward dependencies close a cycle.
    edges = []
    for layer in range(horizon + 1):
        edges.extend([(f'F{layer}', f'Setup{layer}'),
                      (f'Setup{layer}', f'pk{layer}')])
        if layer < horizon:
            edges.append((f'pk{layer + 1}', f'F{layer}'))
    assert acyclic(edges)
    assert not acyclic(edges + [('pk0', f'F{horizon}')])
    return ladder, {'events': ladder.events, 'exposed_inventory': ladder.exposed_inventory(),
                    'post_erasure_keygen_refusals': erased_refusals,
                    'forward_timing_graph_acyclic': True,
                    'terminal_to_root_reencryption_timing_graph_acyclic': False}


def finite_witness():
    ladder, schedule = schedule_control()
    classes = defaultdict(list)
    for state in range(256):
        classes[profile(state, 2)].append(state)
    assert profile(0, 2) == profile(1, 2)
    checks = 0
    for initial in range(256):
        root = ladder.encrypt(0, initial)
        for commands in itertools.product(COMMANDS, repeat=2):
            token, outputs = root, []
            for layer, command in enumerate(commands):
                next_token, answer = ladder.evaluate(layer, command, token)
                # Same input/key gives the same returned opaque token.
                assert ladder.evaluate(layer, command, token) == (next_token, answer)
                token = next_token
                outputs.append(answer)
            _, terminal_answer = ladder.evaluate(2, 'terminal_read', token)
            outputs.append(terminal_answer)
            assert tuple(outputs) == run_clear(initial, commands)[0]
            checks += 1
    a, states_a = run_clear(63, ('add_one', 'double'))
    b, states_b = run_clear(63, ('double', 'add_one'))
    assert states_a == [63, 64, 128] and states_b == [63, 126, 127]
    assert a[-1] == 1 and b[-1] == 0
    # Public replacement is authorized by public issuance, not history binding.
    replacement = ladder.encrypt(2, 255)
    assert ladder.evaluate(2, 'terminal_read', replacement) == (None, 1)
    mismatch = False
    try:
        ladder.evaluate(0, 'infer', replacement)
    except ValueError:
        mismatch = True
    assert mismatch
    return {'classification': 'typed ideal execution only; no cryptographic rejection evidence',
            'schedule': schedule, 'initial_states_checked': 256,
            'complete_two_command_paths_checked': checks,
            'behavioral_classes': len(classes),
            'class_containing_zero': classes[profile(0, 2)],
            'private_challenge_pair': [0, 1],
            'noncommuting_example': {'initial': 63, 'add_then_double_states': states_a,
                                     'double_then_add_states': states_b,
                                     'first_terminal_answer': a[-1], 'second_terminal_answer': b[-1]},
            'public_replacement_terminal_answer': 1,
            'wrong_layer_symbolic_refusal': mismatch,
            'retained_master_negative': 'A raw PKE secret in any layer reads that layer; source-level, not implemented',
            'no_indefinite_continuation': True}


def proof_schedule(branches=3):
    # Local source-theorem applications and ciphertext-hybrid obligations, not
    # an extracted numerical advantage bound for the iO reduction.
    rows = []
    for horizon in range(1, 9):
        rows.append({'horizon': horizon, 'public_key_objects': horizon + 1,
                     'issued_function_key_objects': horizon * branches + 1,
                     'root_to_leaf_command_paths': branches ** horizon,
                     'local_theorem_and_hybrid_tree_nodes': sum(branches ** j for j in range(horizon + 1)),
                     'security_established_here': 'qualitative fixed H=2 only' if horizon == 2 else 'accounting only'})
    assert rows[1]['issued_function_key_objects'] == 7
    assert rows[1]['local_theorem_and_hybrid_tree_nodes'] == 13
    return rows


def main():
    pdf = MIRROR / '2013/729.pdf'
    report = {'classification': 'symbolic schedule and ideal traces; source-conditional proof in FINITE_LADDER.md',
              'finite_witness': finite_witness(), 'proof_schedule': proof_schedule(),
              'source': {'path': str(pdf), 'sha256': hashlib.sha256(pdf.read_bytes()).hexdigest(),
                         'url': 'https://eprint.iacr.org/2013/729',
                         'access': 'Def2.4 and Remark2.5 pp7-8; Def2.6/Remark2.8/Lemma2.9 p9; section4 algorithms pp12-14 and Theorem4.1 p14; proof not fully audited'},
              'search_accounting': {'new_scry_sql_queries': 0, 'new_schema_calls': 0,
                                    'new_web_queries': 0, 'cumulative_scry_sql_queries': 8,
                                    'cumulative_schema_calls': 1, 'cumulative_web_queries': 28,
                                    'kagi_queries': 0, 'eprint_pdf_downloads': 0},
              'script_sha256': hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              'python': sys.version}
    (HERE / 'results/finite_ladder_results.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report, indent=2))


if __name__ == '__main__':
    main()
