#!/usr/bin/env python3
"""Evaluate a public finite fork table. No encryption or hidden-state runtime."""
from __future__ import annotations

import argparse
import base64
import json
from pathlib import Path

FORMAT = "bounded-mistake-learner-quotient-v1"


class Runner:
    def __init__(self, package: Path):
        self.program = json.loads((package / "program.json").read_bytes())
        if self.program["format"] != FORMAT:
            raise ValueError("wrong program format")
        self.horizon = self.program["horizon"]
        self.commands = tuple(self.program["commands"])
        self.branching = len(self.commands)
        self.internal = (self.branching**self.horizon - 1) // (self.branching - 1)
        resident = (package / "resident.bin").read_bytes()
        if len(resident) != self.program["resident_width"]:
            raise ValueError("wrong fixed resident width")
        self.class_id = int.from_bytes(resident, "big")
        if not 0 <= self.class_id < len(self.program["profiles"]):
            raise ValueError("invalid behavioral class")
        self.profile = base64.b64decode(self.program["profiles"][self.class_id], validate=True)
        if len(self.profile) != self.branching * self.internal:
            raise ValueError("wrong complete topology")

    def advance(self, node: int, command: int) -> tuple[int, int]:
        if type(command) is not int or not 0 <= command < self.branching:
            raise ValueError("command outside the finite public alphabet")
        if type(node) is not int or not 0 <= node < self.internal:
            raise ValueError("horizon exhausted or invalid node")
        child = self.branching * node + command + 1
        return child, self.profile[child - 1]

    def run(self, commands: list[int], node: int = 0) -> dict:
        outputs = []
        for command in commands:
            node, output = self.advance(node, command)
            outputs.append("ack" if output == 255 else output)
        return {"outputs": outputs, "node": node}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--package", type=Path, required=True)
    parser.add_argument("--commands", default="", help="comma-separated public command names or indices")
    parser.add_argument("--node", type=int, default=0, help="public snapshot node; root is zero")
    args = parser.parse_args()
    runner = Runner(args.package)
    commands = [int(c) if c.isdecimal() else runner.commands.index(c)
                for c in args.commands.split(",") if c]
    print(json.dumps(runner.run(commands, args.node), sort_keys=True))


if __name__ == "__main__":
    main()
