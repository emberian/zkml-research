#!/usr/bin/env python3
"""Finite behavioral compilation, not a neural learner or secure-erasure runtime.

Real AES-GCM operations from installed cryptography. Setup erasure is an assumption;
the artifact excludes raw states. Deterministic keys occur only in equality tests.
"""
from __future__ import annotations

import argparse
import base64
import copy
import hashlib
import importlib.metadata
import json
import os
from pathlib import Path
import platform
import struct
import subprocess
import sys
from cryptography.exceptions import InvalidTag
from cryptography.hazmat.primitives.ciphers.aead import AESGCM

COMMANDS = ("learn_plus_one", "learn_double", "infer")
B = len(COMMANDS)
ACK = 255
DOMAIN = b"private-unfold-v1"


def step(state: int, command: int) -> tuple[int, int]:
    if command == 0:
        return (state + 1) % 256, ACK
    if command == 1:
        return (2 * state) % 256, ACK
    if command == 2:
        return state, state >> 7
    raise ValueError("command not in authorized alphabet")


def counts(horizon: int) -> tuple[int, int]:
    internal = (B**horizon - 1) // (B - 1)
    return internal, B * internal


def aad(horizon: int, parent: int, command: int) -> bytes:
    return DOMAIN + struct.pack(">IQQ", horizon, parent, command)


def nonce(command: int) -> bytes:
    return command.to_bytes(12, "big")


def b64(value: bytes) -> str:
    return base64.b64encode(value).decode("ascii")


def unb64(value: str) -> bytes:
    return base64.b64decode(value, validate=True)


def wire(artifact: dict) -> bytes:
    return json.dumps(artifact, sort_keys=True, separators=(",", ":")).encode()


def compile_tree(initial: int, horizon: int, test_coins: bytes | None = None) -> dict:
    """Only return deployment artifacts. Python does NOT guarantee memory erasure."""
    if not 0 <= initial < 256 or not 0 <= horizon <= 8:
        raise ValueError("prototype supports a byte and horizons 0..8")
    internal, edges = counts(horizon)
    if test_coins is None:
        keys = [os.urandom(32) for _ in range(edges + 1)]
    else:
        # Reproducible COUPLING TEST coins, never claimed secret from test readers.
        keys = [hashlib.shake_256(DOMAIN + test_coins + i.to_bytes(8, "big")).digest(32)
                for i in range(edges + 1)]
    assert len(set(keys)) == len(keys), "resample setup on key collision"
    states = [initial]
    records: list[str] = []
    for parent in range(internal):
        for command in range(B):
            nxt, output = step(states[parent], command)
            states.append(nxt)
            child = B * parent + command + 1
            assert child == len(states) - 1
            payload = keys[child] + bytes([output])
            records.append(b64(AESGCM(keys[parent]).encrypt(
                nonce(command), payload, aad(horizon, parent, command))))
    return {"format": DOMAIN.decode(), "horizon": horizon,
            "commands": list(COMMANDS), "root": {"node": 0, "key": b64(keys[0])},
            "records": records}


def advance(artifact: dict, token: dict, command: int) -> tuple[dict, int]:
    if artifact["format"] != DOMAIN.decode() or artifact["commands"] != list(COMMANDS):
        raise ValueError("wrong program / format")
    if not isinstance(command, int) or not 0 <= command < B:
        raise ValueError("command not in authorized alphabet")
    internal, edges = counts(artifact["horizon"])
    if len(artifact["records"]) != edges:
        raise ValueError("wrong fixed topology")
    node = token["node"]
    if not 0 <= node < internal:
        raise ValueError("horizon exhausted or invalid node")
    payload = AESGCM(unb64(token["key"])).decrypt(
        nonce(command), unb64(artifact["records"][B * node + command]),
        aad(artifact["horizon"], node, command))
    if len(payload) != 33:
        raise ValueError("wrong fixed payload length")
    return {"node": B * node + command + 1, "key": b64(payload[:32])}, payload[32]


def run_path(artifact: dict, commands: list[int]) -> list[int]:
    current = artifact["root"]
    outputs = []
    for command in commands:
        current, output = advance(artifact, current, command)
        outputs.append(output)
    return outputs


def ideal_tree(initial: int, horizon: int) -> tuple[int, ...]:
    internal, _ = counts(horizon)
    states = [initial]
    outputs = []
    for parent in range(internal):
        for command in range(B):
            nxt, out = step(states[parent], command)
            states.append(nxt)
            outputs.append(out)
    return tuple(outputs)


def decrypt_whole_tree(artifact: dict) -> tuple[int, ...]:
    internal, _ = counts(artifact["horizon"])
    tokens = [artifact["root"]]
    outputs = []
    for parent in range(internal):
        for command in range(B):
            token, out = advance(artifact, tokens[parent], command)
            tokens.append(token)
            outputs.append(out)
    return tuple(outputs)


def refused(fn, exception=(ValueError, InvalidTag)) -> bool:
    try:
        fn()
    except exception:
        return True
    return False


def semantic_merge_leak(initial: int) -> bool:
    # Bad optimization: token indexed by (depth, RAW state), versus history.
    left, _ = step(initial, 0)
    right, _ = step(initial, 1)
    return left == right


def audit(outdir: Path) -> dict:
    outdir.mkdir(parents=True, exist_ok=True)
    horizon = 5
    fixed_coins = b"coupling-audit-public-seed-2026-09-06"
    classes: dict[tuple[int, ...], list[int]] = {}
    for initial in range(256):
        classes.setdefault(ideal_tree(initial, horizon), []).append(initial)
    equivalent = next(group for group in classes.values() if 0 in group)
    assert 1 in equivalent
    # Exhaustively verify every legal edge for every possible initial byte.
    total_edges = 0
    for initial in range(256):
        artifact = compile_tree(initial, horizon, fixed_coins)
        decoded = decrypt_whole_tree(artifact)
        assert decoded == ideal_tree(initial, horizon)
        total_edges += len(decoded)
    # Exact coupled artifact equality for all pairs within each equivalence class.
    coupled_checks = 0
    for signature, group in classes.items():
        first_wire = wire(compile_tree(group[0], horizon, fixed_coins))
        for initial in group[1:]:
            assert wire(compile_tree(initial, horizon, fixed_coins)) == first_wire
            coupled_checks += 1
    a0 = compile_tree(0, horizon, fixed_coins)
    a1 = compile_tree(1, horizon, fixed_coins)
    assert wire(a0) == wire(a1)
    # State distinctions that DO matter are preserved, including update order.
    learning = compile_tree(63, horizon, fixed_coins)
    plus_then_double = run_path(learning, [0, 1, 2])
    double_then_plus = run_path(learning, [1, 0, 2])
    assert plus_then_double == [ACK, ACK, 1]
    assert double_then_plus == [ACK, ACK, 0]
    assert ideal_tree(63, horizon) != ideal_tree(64, horizon)
    assert wire(compile_tree(63, horizon, fixed_coins)) != wire(
        compile_tree(64, horizon, fixed_coins))
    assert (0 >> 7) == (1 >> 7)
    assert semantic_merge_leak(0) is False and semantic_merge_leak(1) is True
    # Their forgotten distinction would become visible outside the allowed horizon.
    longpath = [1] * 7 + [2]
    assert run_path(compile_tree(0, 8, fixed_coins), longpath)[-1] == 0
    assert run_path(compile_tree(1, 8, fixed_coins), longpath)[-1] == 1
    # Authentication checks are scoped: root-key holder CAN forge a new record.
    corrupt = copy.deepcopy(a0)
    raw = bytearray(unb64(corrupt["records"][0]))
    raw[0] ^= 1
    corrupt["records"][0] = b64(raw)
    invalid_tag_refused = refused(lambda: advance(corrupt, corrupt["root"], 0))
    assert invalid_tag_refused
    forged = copy.deepcopy(a0)
    genuine_child, _ = advance(a0, a0["root"], 0)
    forged["records"][0] = b64(AESGCM(unb64(a0["root"]["key"])).encrypt(
        nonce(0), unb64(genuine_child["key"]) + b"\x2a", aad(horizon, 0, 0)))
    assert advance(forged, forged["root"], 0)[1] == 42
    assert hashlib.sha256(wire(forged)).digest() != hashlib.sha256(wire(a0)).digest()
    # Private-ingress failure: parent holder enumerates tokens and matches selection.
    command_by_token = {wire(advance(a0, a0["root"], c)[0]): c for c in range(B)}
    ingress_recovered = []
    metadata_only_recovered = []
    for hidden_command in range(B):
        selected, _ = advance(a0, a0["root"], hidden_command)
        guessed = command_by_token[wire(selected)]
        assert guessed == hidden_command
        ingress_recovered.append(guessed)
        metadata_guess = (selected["node"] - 1) % B
        assert metadata_guess == hidden_command
        metadata_only_recovered.append(metadata_guess)
    # Prefix restore permits contradictory future outward responses for same root.
    assert run_path(learning, [0, 1, 2])[-1] != run_path(learning, [1, 0, 2])[-1]
    assert refused(lambda: run_path(a0, [2] * (horizon + 1)))
    wrongkey = {"node": 0, "key": b64(bytes(32))}
    assert refused(lambda: advance(a0, wrongkey, 0))
    assert refused(lambda: advance(a0, a0["root"], 3))
    # Build and run in separate processes: runner receives only serialized artifact.
    artifact_path = outdir / "synthetic_deployment.json"
    build_command = [sys.executable, str(Path(__file__).resolve()), "build",
                     "--initial", "63", "--horizon", str(horizon), "--output", str(artifact_path)]
    subprocess.run(build_command, check=True, capture_output=True, text=True)
    run_command = [sys.executable, str(Path(__file__).resolve()), "run",
                   "--artifact", str(artifact_path), "--commands", "0,1,2"]
    process = subprocess.run(run_command, check=True, capture_output=True, text=True)
    assert json.loads(process.stdout)["outputs"] == [ACK, ACK, 1]
    real_artifact = json.loads(artifact_path.read_text())
    assert set(real_artifact) == {"format", "horizon", "commands", "root", "records"}
    exact_costs = []
    for h in [2, 3, 4, 5, 8, 10, 20, 40]:
        internal, edges = counts(h)
        exact_costs.append({"horizon": h, "branching": B, "internal_nodes": internal,
                           "edges": edges, "aes_gcm_encryptions_setup": edges,
                           "ciphertext_record_bytes": 49, "raw_ciphertext_bytes": 49 * edges,
                           "node_key_bytes_setup": 32 * (edges + 1),
                           "aead_decryptions_per_step": 1,
                           "note": "counts only; large horizons not built" if h > 8 else "counts"})
    report = {"classification": "executed bounded behavioral compilation; not raw-state encryption",
              "environment": {"python": sys.version, "platform": platform.platform(),
                              "cryptography": importlib.metadata.version("cryptography")},
              "horizon": horizon, "alphabet": list(COMMANDS), "states_checked": 256,
              "legal_edges_checked": total_edges, "equivalence_classes": len(classes),
              "class_sizes": sorted(len(g) for g in classes.values()),
              "zero_equivalence_class": equivalent, "coupled_exact_artifact_equalities": coupled_checks,
              "private_pair": [0, 1], "pair_distinguisher_outside_horizon": {"horizon": 8, "commands": longpath},
              "two_update_positive": {"initial": 63, "commands": [0, 1, 2], "outputs": plus_then_double},
              "order_sensitivity": {"commands": [1, 0, 2], "outputs": double_then_plus},
              "falsifiers": {"merged_state_token_equality_distinguishes_private_pair": True,
                             "private_command_recovered_from_selected_token": ingress_recovered,
                             "private_command_recovered_from_node_index_alone": metadata_only_recovered,
                             "root_key_holder_forges_42": True,
                             "restore_selects_different_outward_answer": True},
              "controls": {"unkeyed_ciphertext_mutation_refused": invalid_tag_refused,
                           "wrong_key_refused": True, "unlisted_command_refused": True,
                           "horizon_exhaustion_refused": True,
                           "full_tree_decryption_matches_ideal": True},
              "subprocess_commands": [build_command, run_command], "subprocess_stdout": process.stdout,
              "serialized_artifact_bytes": artifact_path.stat().st_size,
              "serialized_artifact_sha256": hashlib.sha256(artifact_path.read_bytes()).hexdigest(),
              "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
              "costs": exact_costs,
              "residuals": ["honest setup erasure assumed, not verified",
                            "test coins public; synthetic initial values public",
                            "no compact indefinite continuation", "no private future ingress",
                            "forkable ideal; no quota or single-history release", "no PQ security theorem"]}
    (outdir / "results.json").write_text(json.dumps(report, indent=2) + "\n")
    return report


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)
    ap = sub.add_parser("audit")
    ap.add_argument("--outdir", type=Path, default=Path(__file__).parent / "results")
    bp = sub.add_parser("build")
    bp.add_argument("--initial", type=int, required=True)
    bp.add_argument("--horizon", type=int, required=True)
    bp.add_argument("--output", type=Path, required=True)
    rp = sub.add_parser("run")
    rp.add_argument("--artifact", type=Path, required=True)
    rp.add_argument("--commands", required=True)
    args = parser.parse_args()
    if args.mode == "audit":
        result = audit(args.outdir)
        print(json.dumps({k: result[k] for k in ["states_checked", "legal_edges_checked",
                         "equivalence_classes", "coupled_exact_artifact_equalities",
                         "serialized_artifact_bytes", "falsifiers"]}, indent=2))
    elif args.mode == "build":
        args.output.write_bytes(wire(compile_tree(args.initial, args.horizon)))
    else:
        artifact = json.loads(args.artifact.read_bytes())
        commands = [int(c) for c in args.commands.split(",") if c]
        print(json.dumps({"outputs": run_path(artifact, commands)}))


if __name__ == "__main__":
    main()
