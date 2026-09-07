#!/usr/bin/env python3
"""Finite semantic/reduction-premise checks. NO encryption, commitment, or ZK.

Registry indices are ideal certificates. The coin experiment uses injective
tuples solely to count a fixed-output event; it is deliberately not private.
"""
from __future__ import annotations

from dataclasses import dataclass, replace
from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
import platform


@dataclass(frozen=True)
class State:
    value: int
    opening: int
    history: tuple[int, ...]


@dataclass(frozen=True)
class Observation:
    value: int
    parent: int
    proof: int
    authorized: bool = True


class IdealRelation:
    """Perfect-binding registry and true bounded-history certificates only."""

    def __init__(self):
        self.entries: dict[int, State] = {}

    def issue(self, value: int, history: tuple[int, ...]) -> State:
        assert sum(history) % 256 == value
        opening = len(self.entries) + 1
        state = State(value, opening, history)
        self.entries[opening] = state
        return state

    def commitment(self, state: State) -> int | None:
        # Opening check binds value and opening, but deliberately not H.
        entry = self.entries.get(state.opening)
        return state.opening if entry and entry.value == state.value else None

    def relation(self, state: State) -> bool:
        return sum(state.history) % 256 == state.value

    def observation(self, state: State, value: int = 0) -> Observation:
        assert self.relation(state)
        return Observation(value, state.opening, state.opening)

    def guard(self, state: State, obs: Observation, check_history=False) -> bool:
        return (obs.authorized and obs.parent in self.entries
                and obs.proof == obs.parent
                and self.commitment(state) == obs.parent
                and (not check_history or self.relation(state)))


def compatibility_projection():
    model = IdealRelation()
    # One common genesis 0; authorized first observations 0/1 and 2/3.
    left = [model.issue(v, (v,)) for v in (0, 2)]
    right = [model.issue(v, (v,)) for v in (1, 3)]
    ol = [model.observation(s) for s in left]
    oright = [model.observation(s) for s in right]
    assert all(s.value != t.value for s, t in zip(left, right))
    assert all(model.relation(s) for s in left + right)
    diagonals = []
    for s, t, x, y in zip(left, right, ol, oright):
        assert model.guard(s, x) and model.guard(t, y)
        answer = lambda state, obs: ((state.value + obs.value) % 256) >> 7
        assert answer(s, x) == answer(t, y) == 0
        diagonals.append([answer(s, x), answer(t, y)])

    # q1=2: all mixed stored-query choices, not just matching indices.
    no_replacement = []
    for j, k in product(range(2), repeat=2):
        bits = [model.guard(left[j], ol[k]), model.guard(right[j], oright[k])]
        assert bits[0] == bits[1]
        no_replacement.append({"state_query": j, "observation_query": k,
                               "success_bits": bits})

    # Def4.3 uses the SAME x'_O in both worlds. x'_O is a true left packet.
    xprime = ol[0]
    observation_replacement = [model.guard(left[0], xprime),
                               model.guard(right[0], xprime)]
    assert observation_replacement == [True, False]
    state_replacement = [model.guard(left[0], ol[0]),
                         model.guard(left[0], oright[0])]
    assert state_replacement == [True, False]
    both_replaced = [model.guard(left[0], ol[0])] * 2
    assert both_replaced == [True, True]

    # Positive guard-only control: fresh x differs, committed state is fixed.
    fixed = left[0]
    xa, xb = model.observation(fixed, 0), model.observation(fixed, 1)
    tested = 0
    for s in left + right:
        assert model.guard(s, xa) == model.guard(s, xb)
        tested += 1
    assert model.guard(fixed, xa) and model.guard(fixed, xb)
    return {"classification": "EXECUTED ideal guard projection, not full rMIFE compatibility",
            "same_genesis_valid_distinct_pairs": 2,
            "honest_terminal_answers": diagonals,
            "all_stored_query_mixtures": no_replacement,
            "U_observation_success_bits": observation_replacement,
            "U_state_success_bits": state_replacement,
            "U_both_success_bits": both_replaced,
            "compatibility_probability_gap": 1,
            "fixed_parent_distinct_observation_guard_control_count": tested}


def history_control():
    model = IdealRelation()
    good = model.issue(1, (1,))
    obs = model.observation(good)
    bad = replace(good, history=(2,))
    assert model.guard(bad, obs)
    assert not model.relation(bad)
    assert not model.guard(bad, obs, check_history=True)
    assert model.guard(good, obs, check_history=True)
    return {"classification": "EXECUTED local guard-completeness control",
            "original_guard_accepts_bad_supplied_history": True,
            "internal_history_relation_check_rejects": True,
            "repaired_guard_honest_control_accepts": True}


def coin_control():
    rho, enc = 2, 3
    # Injective serialization represents a perfectly correct but NOT secure
    # hypothetical encryption map. This only falsifies a counting inference.
    outcomes = [((0, r), e) for r, e in product(range(2 ** rho), range(2 ** enc))]
    target = ((0, 0), 0)
    mass = Fraction(outcomes.count(target), len(outcomes))
    assert mass == Fraction(1, 2 ** (rho + enc))
    assert mass < Fraction(1, 2 ** enc)
    right = [((1, r), e) for r, e in product(range(2 ** rho), range(2 ** enc))]
    assert target not in right
    return {"classification": "EXECUTED finite probability identity, not encryption security",
            "payload_coin_bits": rho, "first_PKE_coin_bits": enc,
            "left_fixed_ciphertext_event": str(mass), "right_event": "0",
            "incorrect_inherited_bound": str(Fraction(1, 2 ** enc)),
            "correct_general_guaranteed_bound": "2^(-rho-lambda_next)",
            "equal_parameter_width_premise": "rho <= input_bits_current <= s_current",
            "epsilon_exponent": "4*s_current + lambda_current"}


def initial_input_control():
    commands = ("add", "double", "infer")

    def step(s, command):
        if command == "add":
            return (s + 1) % 256, "ACK"
        if command == "double":
            return (2 * s) % 256, "ACK"
        return s, s >> 7

    def tree(s, depth):
        if depth == 0:
            return s >> 7
        return tuple((a, tree(t, depth - 1))
                     for t, a in (step(s, c) for c in commands))

    # Entire fork tree equality implies every adaptive public-command view.
    assert tree(0, 2) == tree(1, 2)
    assert tree(63, 2) != tree(64, 2)
    classes = {}
    for state in range(256):
        classes.setdefault(tree(state, 2), []).append(state)
    assert len(classes) == 14
    assert classes[tree(0, 2)] == list(range(32))
    traces = []
    for path in product(commands, repeat=2):
        records = []
        for root in (0, 1):
            state, answers = root, []
            for command in path:
                state, answer = step(state, command)
                answers.append(answer)
            records.append(answers + [state >> 7])
        assert records[0] == records[1]
        traces.append({"commands": path, "common_trace": records[0]})
    return {"classification": "EXECUTED finite interface witness, source-conditional crypto separate",
            "initial_private_values": [0, 1], "public_command_horizon": 2,
            "all_fork_tree_equal": True, "trace_count": len(traces), "traces": traces,
            "behavioral_class_count": len(classes),
            "class_containing_zero": classes[tree(0, 2)],
            "falsifier_pair": [63, 64], "falsifier_trees_distinct": True}


def main():
    path = Path(__file__).resolve()
    result = {"classification": "EXECUTED symbolic checks only; no cryptography implemented",
              "command": f"python3 {path}", "python": platform.python_version(),
              "source_sha256": sha256(path.read_bytes()).hexdigest(),
              "parent_compatibility": compatibility_projection(),
              "history_guard": history_control(), "coin_counting": coin_control(),
              "initial_private_input": initial_input_control()}
    serialized = json.dumps(result, indent=2) + "\n"
    path.with_name("results.json").write_text(serialized)
    print(serialized, end="")


if __name__ == "__main__":
    main()
