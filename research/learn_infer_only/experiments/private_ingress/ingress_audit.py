#!/usr/bin/env python3
"""Finite capability/compatibility witnesses. This does NOT implement encryption."""
from __future__ import annotations

import hashlib
import itertools
import json
import platform
import sys
from dataclasses import dataclass
from pathlib import Path

HERE = Path(__file__).resolve().parent


@dataclass(frozen=True)
class Handle:
    slot: str
    serial: int


class IdealLadder:
    """An ideal registry, not a secure implementation or malformed-CT proof.

    Model public state/observation issuance, one private Learn, one state-preserving
    Infer, and a terminal bit reader. Raw register inspection is out of model.
    """

    def __init__(self, public_state_issuance: bool):
        self.public_state_issuance = public_state_issuance
        self._registry: dict[Handle, int] = {}
        self._cache: dict[tuple, tuple[Handle, object]] = {}
        self.exposed_keys = ("F0_Learn", "F1_Infer", "K2_high_bit")

    def _enc(self, slot: str, value: int) -> Handle:
        h = Handle(slot, len(self._registry))
        self._registry[h] = value % 256
        return h

    def initialize(self, value: int) -> Handle:
        return self._enc("state0", value)

    def sensor_issue(self, value: int) -> Handle:
        # Called after setup. A real sensor knows its own value and coins.
        return self._enc("obs0", value)

    def issue_state(self, value: int) -> Handle:
        if not self.public_state_issuance:
            raise PermissionError("state0 issuance capability absent")
        return self._enc("state0", value)

    def learn(self, s: Handle, x: Handle) -> tuple[Handle, str]:
        if (s.slot, x.slot) != ("state0", "obs0"):
            raise ValueError("wrong symbolic slot")
        key = ("F0_Learn", s, x)
        if key not in self._cache:
            self._cache[key] = (self._enc("state1", self._registry[s] + self._registry[x]), "ACK")
        return self._cache[key]

    def infer(self, s: Handle) -> tuple[Handle, int]:
        if s.slot != "state1":
            raise ValueError("wrong symbolic layer")
        key = ("F1_Infer", s)
        if key not in self._cache:
            self._cache[key] = (self._enc("state2", self._registry[s]), self._registry[s] >> 7)
        return self._cache[key]

    def terminal(self, s: Handle) -> int:
        if s.slot != "state2":
            raise ValueError("wrong symbolic layer")
        return self._registry[s] >> 7

    def probe(self, x: Handle, offset: int) -> int:
        s1, ack = self.learn(self.issue_state(offset), x)
        s2, answer = self.infer(s1)
        assert ack == "ACK" and answer == self.terminal(s2)
        return answer


def recover_byte(ladder: IdealLadder, x: Handle) -> tuple[int, list[dict]]:
    lo, hi = 0, 255
    trace = []
    while lo < hi:
        midpoint = (lo + hi + 1) // 2
        offset = (128 - midpoint) % 256
        answer = ladder.probe(x, offset)
        trace.append({"interval_before": [lo, hi], "offset": offset, "answer": answer})
        if answer:
            lo = midpoint
        else:
            hi = midpoint - 1
    return lo, trace


def controls() -> dict:
    # Two different observations agree on the entire intended fixed-root trace.
    traces = []
    for secret in (0, 1):
        ladder = IdealLadder(public_state_issuance=True)
        root = ladder.initialize(0)
        observation = ladder.sensor_issue(secret)
        next_state, ack = ladder.learn(root, observation)
        terminal_state, bit = ladder.infer(next_state)
        traces.append([ack, bit, ladder.terminal(terminal_state)])
        assert ladder.learn(root, observation) == (next_state, ack)
    assert traces[0] == traces[1] == ["ACK", 0, 0]

    all_recoveries = []
    example = None
    for secret in range(256):
        ladder = IdealLadder(public_state_issuance=True)
        ladder.initialize(0)
        observation = ladder.sensor_issue(secret)
        recovered, trace = recover_byte(ladder, observation)
        assert recovered == secret and len(trace) == 8
        all_recoveries.append(recovered)
        if secret == 173:
            example = trace

    # Removing precisely the writer capability blocks this attack path.
    denied = False
    ladder = IdealLadder(public_state_issuance=False)
    root = ladder.initialize(0)
    observation = ladder.sensor_issue(1)
    honest_state, _ = ladder.learn(root, observation)
    assert ladder.infer(honest_state)[1] == 0
    try:
        ladder.probe(observation, 127)
    except PermissionError:
        denied = True
    assert denied

    # Diagonal-only admissibility fails even with no exposed encryption keys.
    # All lists have two entries. The function is deterministic one-bit XOR.
    worlds = [([0, 1], [0, 1]), ([0, 0], [0, 0])]
    matrices = [[[s ^ x for x in xs] for s in ss] for ss, xs in worlds]
    assert [matrices[0][i][i] for i in range(2)] == [matrices[1][i][i] for i in range(2)]
    assert matrices[0][0][1] != matrices[1][0][1]

    # A semantic positive: private hidden coordinates persist through H=2.
    # State/observation=(visible bit, hidden Z4). All public-slot replacements,
    # all cross-query indices and both layers preserve visible equivalence.
    def step(s, x):
        return (s[0] ^ x[0], (3 * s[1] + x[1]) % 4)

    domain = list(itertools.product(range(2), range(4)))
    state_pairs = [((0, 0), (0, 1)), ((1, 2), (1, 3))]
    observation_pairs = [((0, 0), (0, 1)), ((1, 2), (1, 3))]
    checked = 0
    next_pairs = []
    # U in {}, {state}, {observation}, {state,observation}.
    for replaced_state, replaced_obs in itertools.product((False, True), repeat=2):
        ss = [(v, v) for v in domain] if replaced_state else state_pairs
        xx = [(v, v) for v in domain] if replaced_obs else observation_pairs
        for sp, xp in itertools.product(ss, xx):
            a, b = step(sp[0], xp[0]), step(sp[1], xp[1])
            assert a[0] == b[0]
            next_pairs.append((a, b))
            checked += 1
    continuation_checks = 0
    for a, b in next_pairs:
        for z in domain:
            assert step(a, z)[0] == step(b, z)[0]
            continuation_checks += 1
    related_pairs = [(a, b) for a, b in itertools.product(domain, repeat=2) if a[0] == b[0]]
    full_relation_checks = 0
    for (s0, s1), (x0, x1) in itertools.product(related_pairs, repeat=2):
        assert step(s0, x0)[0] == step(s1, x1)[0]
        full_relation_checks += 1
    learned_states = []
    for fresh_observation in ((0, 0), (0, 1)):
        s = step((0, 0), fresh_observation)
        learned_states.append([s, step(s, (0, 0))])
    assert learned_states[0][-1] != learned_states[1][-1]
    assert step((0, 0), (0, 0))[0] != step((0, 0), (1, 0))[0]
    assert step(step((0, 0), (0, 1)), (0, 2)) != step(step((0, 0), (0, 2)), (0, 1))

    # Necessary zero-coin comparison condition for n=2 in Theorem 6.1.
    # This checks exponents, NOT encryption security or compatibility sufficiency.
    inequalities = []
    for current_lambda in range(1, 65):
        for s in range(1, 65):
            epsilon_exponent = 4 * s + current_lambda
            assert current_lambda < epsilon_exponent
            inequalities.append([current_lambda, s, epsilon_exponent])
    return {
        "not_encryption": True,
        "fixed_root_honest_traces": traces,
        "chosen_state_recoveries": len(all_recoveries),
        "probes_per_recovery": 8,
        "transition_key_evaluations_per_recovery": 16,
        "terminal_evaluations_per_recovery": 8,
        "example_secret": 173,
        "example_recovery_trace": example,
        "attack_blocked_when_state_issuance_removed": denied,
        "diagonal_only_falsifier_matrices": matrices,
        "all_public_slot_semantic_positive_checks": checked,
        "semantic_positive_continuation_checks": continuation_checks,
        "full_visible_relation_closure_checks": full_relation_checks,
        "persisting_private_observation_states": learned_states,
        "same_parameter_epsilon_failures": len(inequalities),
        "necessary_output_coin_length_condition": "lambda_next >= 4*s_current + lambda_current; not sufficient",
    }


def main() -> None:
    data = controls()
    data["provenance"] = {
        "command": "python3 research/learn_infer_only/experiments/private_ingress/ingress_audit.py",
        "python": sys.version,
        "platform": platform.platform(),
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }
    target = HERE / "results.json"
    target.write_text(json.dumps(data, indent=2) + "\n")
    print(json.dumps({k: v for k, v in data.items() if k not in {"example_recovery_trace", "provenance"}}, indent=2))
    print("PASS: finite semantic/capability witnesses only; no encryption or cryptographic security proof")


if __name__ == "__main__":
    main()
