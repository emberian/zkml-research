#!/usr/bin/env python3
"""Ordinary Boolean-circuit dependency projection; not an encryption scheme."""
from itertools import product
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent


def project(circuit):
    used = sorted({index for gate in circuit["gates"] for kind, index in gate[1:]
                   if kind == "key"} | {index for kind, index in circuit["outputs"]
                                       if kind == "key"})
    remap = {old: new for new, old in enumerate(used)}

    def wire(w):
        kind, index = w
        return (kind, remap[index] if kind == "key" else index)

    return used, {
        "gates": [(gate[0], *(wire(w) for w in gate[1:])) for gate in circuit["gates"]],
        "outputs": [wire(w) for w in circuit["outputs"]],
    }


def evaluate(circuit, key, message, random):
    values = {"key": key, "message": message, "random": random, "gate": []}
    for operation, *inputs in circuit["gates"]:
        args = [values[kind][index] for kind, index in inputs]
        if operation == "xor":
            result = args[0] ^ args[1]
        elif operation == "and":
            result = args[0] & args[1]
        else:
            raise ValueError(operation)
        values["gate"].append(result)
    return [values[kind][index] for kind, index in circuit["outputs"]]


# Both nontrivial gates and a direct key-to-output wire are deliberate.
circuit = {
    "gates": [("xor", ("key", 2), ("message", 0)),
              ("and", ("key", 5), ("random", 0)),
              ("xor", ("gate", 0), ("gate", 1)),
              ("xor", ("key", 9), ("message", 1))],
    "outputs": [("gate", 2), ("gate", 3), ("key", 11)],
}
positions, compact = project(circuit)
assert positions == [2, 5, 9, 11]
checks = 0
nonzero = 0
for key in product((0, 1), repeat=12):
    for message in product((0, 1), repeat=2):
        for random in product((0, 1), repeat=1):
            before = evaluate(circuit, key, message, random)
            after = evaluate(compact, [key[i] for i in positions], message, random)
            assert before == after
            nonzero += any(before)
            checks += 1

# Gate-only dependency analysis misses the direct output bit.
k0 = [0] * 12
k1 = k0.copy()
k1[11] = 1
gate_only = positions[:-1]
assert [k0[i] for i in gate_only] == [k1[i] for i in gate_only]
assert evaluate(circuit, k0, [0, 0], [0]) != evaluate(circuit, k1, [0, 0], [0])

# Zero-gate passthrough refutes a key bound based on gate count alone.
passthrough = []
for width in (8, 32, 128):
    direct = {"gates": [], "outputs": [("key", i) for i in range(width)]}
    retained, _ = project(direct)
    assert len(retained) == width
    passthrough.append({"gates": 0, "output_bits": width, "retained_key_bits": len(retained)})

# After absorbing logarithms, beta=1/4, A=3,a=2,B=5,d=1.
# T=(10U)^12 is a single common bound; no level-dependent exponent recurrence.
closure = []
for u in (1, 2, 4, 8, 16, 32, 64, 128):
    t = (10 * u) ** 12
    t_quarter = (10 * u) ** 3
    assert t >= 2 * 5 * u and t_quarter >= 2 * 3 * u**2
    work = 3 * u**2 * t_quarter**3 + 5 * u
    assert work <= t
    n = u + t.bit_length()
    key_bound = 8 * n
    closure.append({"U": u, "T": t, "node_work_upper_bound": work,
                    "message_bound_example": n, "effective_key_bound_example": key_bound,
                    "key_exceeds_message": key_bound > n})

result = {
    "scope": "Finite ordinary Boolean-circuit and integer-inequality witnesses only. No encryption implementation or cryptographic security validation.",
    "original_key_bits": 12, "payload_bits": 2,
    "gate_count": len(circuit["gates"]), "output_bits": len(circuit["outputs"]),
    "retained_positions": positions, "fan_in_bound": 2 * len(circuit["gates"]) + len(circuit["outputs"]),
    "exhaustive_equalities": checks, "nonzero_output_cases": nonzero,
    "gate_only_falsifier": {"same_retained_key": [k0[i] for i in gate_only],
        "output0": evaluate(circuit, k0, [0, 0], [0]),
        "output1": evaluate(circuit, k1, [0, 0], [0])},
    "zero_gate_passthrough": passthrough,
    "after_log_absorption_closure_examples": closure,
}
(HERE / "circuit_dependency.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"exhaustive_equalities": checks, "nonzero_output_cases": nonzero,
                  "retained_key_bits": len(positions), "closure_examples": len(closure)}))
