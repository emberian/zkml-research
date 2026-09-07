#!/usr/bin/env python3
"""Positive fixed-span DDH-IPFE window reference. Not production cryptography."""
from __future__ import annotations

import argparse
from collections import deque
import json
from pathlib import Path
import struct
import sys
import time

# Reuse the approved reference algorithms. Its guarded main() is NEVER called.
BASE = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(BASE))
import additive_ipfe as ip

Y = ((1, 1, 0), (0, 1, 1))
WIDTH = 256
CT_BYTES = 4 * WIDTH
WINDOW = 4
INPUT_BOUND = 2
OUTPUT_BOUND = 2 * INPUT_BOUND * WINDOW
MAGIC = b"FSPANW01"


def pack(values) -> bytes:
    return b"".join(int(value).to_bytes(WIDTH, "big") for value in values)


def unpack(data: bytes, count: int, group: bool = True) -> tuple[int, ...]:
    if len(data) != count * WIDTH:
        raise ValueError("incorrect canonical frame size")
    values = tuple(int.from_bytes(data[i:i + WIDTH], "big") for i in range(0, len(data), WIDTH))
    if group:
        if any(not 1 <= value < ip.P or pow(value, ip.Q, ip.P) != 1 for value in values):
            raise ValueError("not a canonical subgroup element")
    elif any(not 0 <= value < ip.Q for value in values):
        raise ValueError("invalid scalar")
    return values


def setup_files(output: Path) -> None:
    output.mkdir(parents=True, exist_ok=False)
    public, master = ip.setup()
    keys = tuple(ip.keyder(master, y) for y in Y)
    (output / "public.bin").write_bytes(pack(public))
    (output / "projection_keys.bin").write_bytes(pack(keys))
    # Private initializer exits with master only in its transient process state.
    # This is an explicit erasure ASSUMPTION, not verified secure deletion.


def issue(public_path: Path, output: Path, rows: list[list[int]], benchmark_log: Path | None = None) -> dict:
    public = unpack(public_path.read_bytes(), 3)
    samples = []
    encrypted = []
    for row in rows:
        if len(row) != 3 or any(type(v) is not int or not -INPUT_BOUND <= v <= INPUT_BOUND for v in row):
            raise ValueError("input outside declared finite domain")
        start = time.perf_counter_ns()
        encrypted.append(pack(ip.encrypt(public, tuple(row))))
        samples.append(time.perf_counter_ns() - start)
    output.write_bytes(b"".join(encrypted))
    if benchmark_log is not None:
        # Synthetic audit-only diagnostics; not part of the ciphertext interface.
        benchmark_log.write_text(json.dumps({"encryption_ns_samples": samples}) + "\n")
    return {"records": len(rows), "bytes": output.stat().st_size}


def decode_table() -> dict[int, int]:
    current = pow(ip.G, -OUTPUT_BOUND, ip.P)
    result = {}
    for integer in range(-OUTPUT_BOUND, OUTPUT_BOUND + 1):
        result[current] = integer
        current = current * ip.G % ip.P
    assert len(result) == 2 * OUTPUT_BOUND + 1
    return result


class Learner:
    def __init__(self):
        self.queue = deque()
        self.aggregate = (1,) * 4  # Public empty-window identity.
        self.steps = 0

    def update(self, ciphertext: tuple[int, ...]) -> bool:
        self.aggregate = ip.combine(self.aggregate, ciphertext)
        self.queue.append(ciphertext)
        expired = len(self.queue) > WINDOW
        if expired:
            old = self.queue.popleft()
            self.aggregate = ip.combine(self.aggregate, tuple(pow(v, -1, ip.P) for v in old))
        self.steps += 1
        return expired

    def scores(self, keys: tuple[int, int], table: dict[int, int]) -> tuple[int, int]:
        # All ingressed ciphertexts were validated; products/inverses preserve
        # membership. No new secret-key derivation or decryption oracle is used.
        groups = [ip.project_group(self.aggregate, key, y, validate=False) for key, y in zip(keys, Y)]
        try:
            return tuple(table[value] for value in groups)
        except KeyError as error:
            raise ValueError("projection outside declared integer decode range") from error

    def rebuild(self) -> tuple[int, ...]:
        value = (1,) * 4
        for ciphertext in self.queue:
            value = ip.combine(value, ciphertext)
        return value

    def serialize(self) -> bytes:
        return MAGIC + struct.pack(">QI", self.steps, len(self.queue)) + pack(self.aggregate) + b"".join(map(pack, self.queue))

    @classmethod
    def load(cls, data: bytes):
        if len(data) < 20 + CT_BYTES or data[:8] != MAGIC:
            raise ValueError("wrong checkpoint format")
        steps, count = struct.unpack(">QI", data[8:20])
        if count != min(steps, WINDOW) or len(data) != 20 + CT_BYTES * (count + 1):
            raise ValueError("incorrect public window dimensions")
        result = cls()
        result.steps = steps
        result.aggregate = unpack(data[20:20 + CT_BYTES], 4)
        for offset in range(20 + CT_BYTES, len(data), CT_BYTES):
            result.queue.append(unpack(data[offset:offset + CT_BYTES], 4))
        if result.rebuild() != result.aggregate:
            raise ValueError("checkpoint aggregate disagrees with current ciphertext queue")
        return result


def evaluate(key_path: Path, input_path: Path, output_path: Path, checkpoint: Path | None) -> dict:
    keys = unpack(key_path.read_bytes(), 2, group=False)
    learner = Learner() if checkpoint is None else Learner.load(checkpoint.read_bytes())
    table = decode_table()
    stream = input_path.read_bytes()
    if len(stream) % CT_BYTES:
        raise ValueError("truncated ciphertext stream")
    trace = []
    for offset in range(0, len(stream), CT_BYTES):
        validation_start = time.perf_counter_ns()
        ciphertext = unpack(stream[offset:offset + CT_BYTES], 4)
        validation_ns = time.perf_counter_ns() - validation_start
        update_start = time.perf_counter_ns()
        expired = learner.update(ciphertext)
        update_ns = time.perf_counter_ns() - update_start
        assert learner.aggregate == learner.rebuild()
        read_start = time.perf_counter_ns()
        scores = learner.scores(keys, table)
        read_ns = time.perf_counter_ns() - read_start
        trace.append({"step": learner.steps, "window_items": len(learner.queue),
                      "scores": scores, "class": int(scores[1] > scores[0]),
                      "expired_exact_old_ciphertext": expired,
                      "aggregate_bytes_equal_current_queue_product": True,
                      "validation_ns": validation_ns, "update_ns": update_ns, "two_read_ns": read_ns})
    output_path.write_bytes(learner.serialize())
    return {"trace": trace, "checkpoint_bytes": output_path.stat().st_size,
            "projection_vectors": Y, "integer_decode_interval": [-OUTPUT_BOUND, OUTPUT_BOUND]}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)
    init = sub.add_parser("setup")
    init.add_argument("--output", type=Path, required=True)
    issuer = sub.add_parser("issue")
    issuer.add_argument("--public", type=Path, required=True)
    issuer.add_argument("--output", type=Path, required=True)
    issuer.add_argument("--benchmark-log", type=Path, help="private synthetic audit diagnostics, never a host input")
    runtime = sub.add_parser("run")
    runtime.add_argument("--keys", type=Path, required=True)
    runtime.add_argument("--input", type=Path, required=True)
    runtime.add_argument("--output", type=Path, required=True)
    runtime.add_argument("--checkpoint", type=Path)
    args = parser.parse_args()
    if args.mode == "setup":
        setup_files(args.output)
    elif args.mode == "issue":
        print(json.dumps(issue(args.public, args.output, json.load(sys.stdin)["rows"], args.benchmark_log)))
    else:
        print(json.dumps(evaluate(args.keys, args.input, args.output, args.checkpoint)))


if __name__ == "__main__":
    main()
