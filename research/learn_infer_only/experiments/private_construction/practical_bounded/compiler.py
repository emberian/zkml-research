#!/usr/bin/env python3
"""Private-initializer boundary for a finite quotient, not secure erasure."""
from __future__ import annotations

import argparse
import base64
import itertools
import json
from pathlib import Path
import shutil
import sys

from runtime import FORMAT

COMMANDS = ("learn_0_negative", "learn_0_positive", "learn_1_negative",
            "learn_1_positive", "infer_0", "infer_1")
STATES = tuple(itertools.product(range(-8, 9), repeat=2))
ACK = 255


def step(state: tuple[int, int], command: int) -> tuple[tuple[int, int], int]:
    """Two independent bounded scores; update by label only after a mistake."""
    if 0 <= command < 4:
        context, label = command // 2, 2 * (command % 2) - 1
        score = state[context]
        if (1 if score >= 0 else -1) != label:
            updated = list(state)
            updated[context] += label
            return tuple(updated), ACK
        return state, ACK
    if command in (4, 5):
        return state, int(state[command - 4] >= 0)
    raise ValueError("invalid public command")


def profile(initial: tuple[int, int], horizon: int) -> bytes:
    if initial not in STATES or not 0 <= horizon <= 6:
        raise ValueError("supported domain: two scores -8..8, horizon 0..6")
    branching = len(COMMANDS)
    internal = (branching**horizon - 1) // (branching - 1)
    states = [initial]
    outputs = bytearray()
    for parent in range(internal):
        for command in range(branching):
            nxt, output = step(states[parent], command)
            states.append(nxt)
            outputs.append(output)
    return bytes(outputs)


def wire(value: dict) -> bytes:
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def make_catalog(horizon: int) -> tuple[dict, dict[tuple[int, int], int]]:
    profiles = {state: profile(state, horizon) for state in STATES}
    distinct = sorted(set(profiles.values()))
    ids = {p: i for i, p in enumerate(distinct)}
    width = max(1, ((len(distinct) - 1).bit_length() + 7) // 8)
    public = {"format": FORMAT, "horizon": horizon, "commands": list(COMMANDS),
              "resident_width": width,
              "profiles": [base64.b64encode(p).decode("ascii") for p in distinct]}
    return public, {state: ids[p] for state, p in profiles.items()}


def initialize(public_catalog: Path, output: Path, initial: tuple[int, int]) -> dict:
    public_bytes = public_catalog.read_bytes()
    public = json.loads(public_bytes)
    if public["format"] != FORMAT or public["commands"] != list(COMMANDS):
        raise ValueError("wrong public program")
    encoded = base64.b64encode(profile(initial, public["horizon"])).decode("ascii")
    class_id = public["profiles"].index(encoded)
    output.mkdir(parents=True, exist_ok=False)
    (output / "program.json").write_bytes(public_bytes)
    (output / "resident.bin").write_bytes(class_id.to_bytes(public["resident_width"], "big"))
    shutil.copyfile(Path(__file__).with_name("runtime.py"), output / "runtime.py")
    # The local initial/profile values die with this process. This is NOT a
    # secure deletion guarantee; the initialization boundary must be trusted.
    return {"files": ["program.json", "resident.bin", "runtime.py"],
            "horizon": public["horizon"], "resident_bytes": public["resident_width"]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)
    cp = sub.add_parser("catalog", help="entirely public preprocessing")
    cp.add_argument("--horizon", type=int, required=True)
    cp.add_argument("--output", type=Path, required=True)
    ip = sub.add_parser("initialize", help="read synthetic/private score pair from stdin")
    ip.add_argument("--catalog", type=Path, required=True)
    ip.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.mode == "catalog":
        catalog, _ = make_catalog(args.horizon)
        args.output.write_bytes(wire(catalog))
        print(json.dumps({"classes": len(catalog["profiles"]), "horizon": args.horizon}))
    else:
        initial = tuple(json.load(sys.stdin)["state"])
        print(json.dumps(initialize(args.catalog, args.output, initial), sort_keys=True))


if __name__ == "__main__":
    main()
