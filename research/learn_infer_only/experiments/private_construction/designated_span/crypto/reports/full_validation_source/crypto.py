#!/usr/bin/env python3
"""Designated fixed-span DDH research backend. No production/PQ/constant-time claim."""
from __future__ import annotations
import argparse
import hashlib
import json
import math
import os
from pathlib import Path
import secrets
import stat
import struct
import subprocess
import sys
import tempfile
import time

from group import P, Q, G
from native_pow import NativePow

HERE = Path(__file__).resolve().parent
D, W, K, WIDTH = 577, 32, 16, 256
MAGIC = b"RSDDH001"
HEADER = struct.Struct(">8sB32s32sH32s32s32sQ")
STATE, OUTPUT, SECRET = 1, 2, 3
NO_ROW = 65535
ZERO_HASH = "0" * 64
COUNTS = {"native_modexp": 0, "subgroup_checks": 0, "context_consistency_rows": 0}
ENGINE = None


class Refusal(Exception):
    pass


def require(ok, reason):
    if not ok:
        raise Refusal(reason)


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(",", ":"), ensure_ascii=True, allow_nan=False).encode()


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def digest(obj):
    return sha(canonical(obj))


def parse(raw):
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "duplicate JSON key")
            result[key] = value
        return result
    def bad_number(_):
        raise Refusal("integer JSON numbers only")
    return json.loads(raw, object_pairs_hook=pairs, parse_float=bad_number, parse_constant=bad_number)


def read_json(path, cap=1_000_000, exact=False):
    raw = read(path, cap)
    result = parse(raw)
    if exact:
        require(raw == canonical(result), "noncanonical JSON")
    return result


def read(path, cap):
    with Path(path).open("rb") as inp:
        raw = inp.read(cap + 1)
    require(len(raw) <= cap, "file size cap")
    return raw


def exact(obj, fields):
    require(type(obj) is dict and set(obj) == set(fields), "schema fields")


def hx(value):
    return value.to_bytes(WIDTH, "big").hex()


def unhex(value, scalar=False):
    require(type(value) is str and len(value) == WIDTH * 2 and all(c in "0123456789abcdef" for c in value), "fixed width hex")
    number = int(value, 16)
    require(0 <= number < Q if scalar else 1 <= number < P, "scalar/group range")
    return number


def exp(base, exponent):
    COUNTS["native_modexp"] += 1
    return ENGINE(base, exponent, P)


def subgroup(value):
    COUNTS["subgroup_checks"] += 1
    require(1 <= value < P and exp(value, Q) == 1, "subgroup element")


def save(path, raw, private=False):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True, mode=0o700 if private else 0o755)
    if path.exists() or path.is_symlink():
        status = path.lstat()
        require(stat.S_ISREG(status.st_mode), "existing output must be regular")
        if private:
            require(status.st_mode & 0o077 == 0, "existing private file permissions")
        require(path.read_bytes() == raw, "refuse differing existing output")
        return
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    fd = os.open(path, flags, 0o600 if private else 0o644)
    with os.fdopen(fd, "wb") as out:
        out.write(raw)
        out.flush()
        os.fsync(out.fileno())


def vector(path):
    row = read_json(path)
    require(type(row) is list and len(row) == D and all(type(v) is int and -127 <= v <= 127 for v in row), "signed577 int8 vector")
    return row


ROWS = read_json(HERE / "rows.json", exact=True)
require(len(ROWS) == K and all(type(y) is list and len(y) == D and all(type(v) is int and -127 <= v <= 127 for v in y) for y in ROWS), "fixed rows")
ROW_HASHES = [digest(y) for y in ROWS]
BOUNDS = [W * 127 * sum(map(abs, y)) for y in ROWS]
require(len(set(ROW_HASHES)) == K and Q > 2 * max(BOUNDS), "fixed row uniqueness/no-wrap")
PARAMS = {"schema": "resident-designated-ddh-params-v1", "group": "RFC3526-group14-prime-order-subgroup",
          "p_hex": hx(P), "q_hex": hx(Q), "generator": G, "dimension": D, "capacity": W,
          "routes": [0, 1], "fixed_row_count": K, "row_sha256": ROW_HASHES,
          "row_signed_score_bounds": BOUNDS, "width_bytes": WIDTH, "header_bytes": HEADER.size,
          "state_group_elements": D + 1, "output_group_elements": 2,
          "state_bytes": HEADER.size + (D + 1) * WIDTH, "output_bytes": HEADER.size + 2 * WIDTH,
          "recipient_key_bytes": HEADER.size + WIDTH,
          "program_semantics": "signed577-window32-exact-original-expiry-designated-fixed-row-v1"}
PARAMS_ID = digest(PARAMS)
PROGRAM_ID = digest({"semantics": PARAMS["program_semantics"], "params_id": PARAMS_ID})


def bootstrap_body(h):
    return {"schema": "resident-designated-bootstrap-v1", "params_id": PARAMS_ID, "rows": ROWS, "h": h}


def load_bootstrap(path):
    body = read_json(path, exact=True)
    exact(body, ["schema", "params_id", "rows", "h"])
    require(body["schema"] == "resident-designated-bootstrap-v1" and body["params_id"] == PARAMS_ID and canonical(body["rows"]) == canonical(ROWS), "bootstrap params")
    require(type(body["h"]) is list and len(body["h"]) == D, "public dimension")
    public = [unhex(h) for h in body["h"]]
    for h in public:
        subgroup(h)
    return body, public


def registration(setup_id, row_id, A, tau):
    recipient_id = digest({"domain": "dedicated-designated-recipient-v1", "setup_id": setup_id,
                           "row_id": row_id, "row_sha256": ROW_HASHES[row_id], "A": hx(A)})
    token = {"row_id": row_id, "row_sha256": ROW_HASHES[row_id], "recipient_id": recipient_id,
             "A": hx(A), "tau": hx(tau)}
    return {**token, "token_sha256": digest(token)}


def load_context(path):
    raw = read(path, 1_000_000)
    body = parse(raw)
    require(raw == canonical(body), "context canonical JSON")
    exact(body, ["schema", "params_id", "setup_id", "rows", "h", "recipients"])
    require(body["schema"] == "resident-designated-context-v1" and body["params_id"] == PARAMS_ID and canonical(body["rows"]) == canonical(ROWS), "context params")
    require(type(body["h"]) is list and len(body["h"]) == D, "context dimension")
    require(body["setup_id"] == digest(bootstrap_body(body["h"])), "setup identity")
    h = [unhex(x) for x in body["h"]]
    for value in h:
        subgroup(value)
    require(type(body["recipients"]) is list and len(body["recipients"]) == K, "recipient count")
    for i, record in enumerate(body["recipients"]):
        exact(record, ["row_id", "row_sha256", "recipient_id", "A", "tau", "token_sha256"])
        A, tau = unhex(record["A"]), unhex(record["tau"], scalar=True)
        require(canonical(record) == canonical(registration(body["setup_id"], i, A, tau)), "recipient token identity")
        subgroup(A)
        projected = 1
        for base, coefficient in zip(h, ROWS[i], strict=True):
            if coefficient:
                projected = projected * exp(base, coefficient) % P
        require(exp(G, tau) * A % P == projected, "public token consistency")
        COUNTS["context_consistency_rows"] += 1
    return {"body": body, "id": sha(raw), "h": h}


def pack(ctx, kind, values, row_id=NO_ROW):
    record = None if row_id == NO_ROW else ctx["body"]["recipients"][row_id]
    identities = [ZERO_HASH] * 3 if record is None else [record[x] for x in ("row_sha256", "recipient_id", "token_sha256")]
    payload = b"".join(v.to_bytes(WIDTH, "big") for v in values)
    return HEADER.pack(MAGIC, kind, bytes.fromhex(PARAMS_ID), bytes.fromhex(ctx["id"]), row_id,
                       *(bytes.fromhex(x) for x in identities), len(payload)) + payload


def unpack(ctx, path, expected=None):
    raw = read(path, PARAMS["state_bytes"])
    require(len(raw) >= HEADER.size, "envelope header")
    magic, kind, params, context, row_id, row_hash, recipient, token, size = HEADER.unpack(raw[:HEADER.size])
    require(magic == MAGIC and kind in (STATE, OUTPUT, SECRET), "envelope domain/type")
    require(expected is None or kind == expected, "required envelope type")
    require(params.hex() == PARAMS_ID and context.hex() == ctx["id"], "envelope context")
    count = {STATE: D + 1, OUTPUT: 2, SECRET: 1}[kind]
    require(size == count * WIDTH and len(raw) == HEADER.size + size, "envelope exact width/count")
    if kind == STATE:
        require(row_id == NO_ROW and row_hash == recipient == token == bytes(32), "state row fields")
    else:
        require(0 <= row_id < K, "designated row")
        record = ctx["body"]["recipients"][row_id]
        require([row_hash.hex(), recipient.hex(), token.hex()] == [record[k] for k in ("row_sha256", "recipient_id", "token_sha256")], "designated identities")
    values = [int.from_bytes(raw[i:i + WIDTH], "big") for i in range(HEADER.size, len(raw), WIDTH)]
    if kind == SECRET:
        require(0 <= values[0] < Q, "recipient scalar range")
        require(exp(G, values[0]) == int(ctx["body"]["recipients"][row_id]["A"], 16), "recipient scalar registration")
    else:
        for value in values:
            subgroup(value)
    require(raw == pack(ctx, kind, values, row_id), "envelope canonical encoding")
    return values, kind, row_id, raw


def metadata(ctx, raw, kind, row_id=NO_ROW):
    result = {"canonical": True, "sha256": sha(raw), "bytes": len(raw), "params_id": PARAMS_ID,
              "key_id": ctx["id"], "context_id": ctx["id"], "object_type": {STATE: "state", OUTPUT: "recipient_output", SECRET: "recipient_secret"}[kind],
              "group_elements": {STATE: D + 1, OUTPUT: 2, SECRET: 0}[kind], "row_id": None if row_id == NO_ROW else row_id}
    if row_id != NO_ROW:
        result.update({k: ctx["body"]["recipients"][row_id][k] for k in ("row_sha256", "recipient_id", "token_sha256")})
    return result


def query_obj(ctx, row_id):
    r = ctx["body"]["recipients"][row_id]
    return {"schema": "resident-designated-query-v1", "params_id": PARAMS_ID, "context_id": ctx["id"],
            **{k: r[k] for k in ("row_id", "row_sha256", "recipient_id", "token_sha256")}, "coefficients": ROWS[row_id]}


def load_query(ctx, path):
    query = read_json(path, exact=True)
    require(type(query) is dict and type(query.get("row_id")) is int and 0 <= query["row_id"] < K, "query row")
    require(canonical(query) == canonical(query_obj(ctx, query["row_id"])), "registered exact query")
    return query["row_id"]


def decode(group_value, bound):
    # Variable-time bounded BSGS. It is an honest integer decoder, not a leakage gate.
    m = math.isqrt(2 * bound + 1)
    if m * m < 2 * bound + 1:
        m += 1
    start = time.perf_counter_ns()
    baby, v = {}, 1
    for j in range(m):
        baby[v] = j
        v = v * G % P
    factor, target = exp(G, -m), group_value * exp(G, bound) % P
    table_ns = time.perf_counter_ns() - start
    start = time.perf_counter_ns()
    for i in range(2 * bound // m + 1):
        j = baby.get(target)
        if j is not None and i * m + j <= 2 * bound:
            value = i * m + j - bound
            require(exp(G, value) == group_value, "decoder equality")
            return value, {"bsgs_baby_entries": m, "bsgs_giant_iterations": i + 1,
                           "bsgs_table_ns": table_ns, "bsgs_decode_ns": time.perf_counter_ns() - start}
        target = target * factor % P
    raise Refusal("outside honest bounded integer interval")


def child(command, **flags):
    argv = [sys.executable, "-B", str(Path(__file__).resolve()), command]
    for key, value in flags.items():
        argv += ["--" + key.replace("_", "-"), str(value)]
    start = time.perf_counter_ns()
    out = subprocess.run(argv, capture_output=True, timeout=180)
    require(out.returncode == 0, "private setup child failed")
    result = parse(out.stdout)
    return {"command": command, "elapsed_ns": time.perf_counter_ns() - start,
            "process_work_ns": result["process_work_ns"], "counts": result["counts"]}


def run(args):
    if args.command == "params":
        result = {**PARAMS, "params_id": PARAMS_ID, "program_id": PROGRAM_ID}
        if args.context:
            ctx = load_context(args.context)
            result.update(key_id=ctx["id"], context_id=ctx["id"])
        return result
    if args.command == "initializer":
        private = Path(args.deliveries)
        private.mkdir(mode=0o700, parents=True, exist_ok=False)
        # This is the only process that holds s. It never serializes s.
        master = [secrets.randbelow(Q) for _ in range(D)]
        h = [hx(exp(G, x)) for x in master]
        save(args.bootstrap, canonical(bootstrap_body(h)))
        for i, row in enumerate(ROWS):
            ki = sum(a * b for a, b in zip(master, row, strict=True)) % Q
            save(private / f"k{i:02d}.delivery", ki.to_bytes(WIDTH, "big"), True)
        return {"master_serialized": False, "private_projection_deliveries": K, "rng": "secrets.randbelow; OS-backed SystemRandom"}
    if args.command == "recipient-register":
        body, _ = load_bootstrap(args.bootstrap)
        i = args.row
        require(0 <= i < K, "recipient row")
        raw = read(args.delivery, WIDTH)
        require(len(raw) == WIDTH, "projection scalar width")
        ki = int.from_bytes(raw, "big")
        require(ki < Q, "projection scalar range")
        ai = secrets.randbelow(Q)
        record = registration(digest(body), i, exp(G, ai), (ki - ai) % Q)
        save(args.secret, ai.to_bytes(WIDTH, "big"), True)
        save(args.registration, canonical(record))
        return {"row_id": i, "recipient_id": record["recipient_id"], "retained_scalar_count": 1, "projection_key_retained": False}
    if args.command == "recipient-finalize":
        ctx = load_context(args.context)
        raw = read(args.secret, WIDTH)
        require(len(raw) == WIDTH, "pending recipient scalar width")
        ai = int.from_bytes(raw, "big")
        require(0 <= ai < Q and exp(G, ai) == int(ctx["body"]["recipients"][args.row]["A"], 16), "recipient registration match")
        save(args.out, pack(ctx, SECRET, [ai], args.row), True)
        return {"row_id": args.row, "recipient_id": ctx["body"]["recipients"][args.row]["recipient_id"], "retained_scalar_count": 1}
    if args.command == "keygen":
        secret_dir = Path(args.sk)
        require(not secret_dir.exists(), "new recipient directory required")
        secret_dir.mkdir(parents=True, mode=0o700)
        phases = []
        with tempfile.TemporaryDirectory(prefix=".designated-setup-", dir=secret_dir) as temporary:
            tmp = Path(temporary)
            bootstrap = tmp / "bootstrap.json"
            phases.append(child("initializer", bootstrap=bootstrap, deliveries=tmp / "deliveries"))
            for i in range(K):
                phases.append(child("recipient-register", bootstrap=bootstrap, delivery=tmp / "deliveries" / f"k{i:02d}.delivery",
                                    row=i, secret=tmp / f"a{i:02d}.pending", registration=tmp / f"r{i:02d}.json"))
                (tmp / "deliveries" / f"k{i:02d}.delivery").unlink()
            boot = read_json(bootstrap, exact=True)
            context = {"schema": "resident-designated-context-v1", "params_id": PARAMS_ID, "setup_id": digest(boot),
                       "rows": ROWS, "h": boot["h"], "recipients": [read_json(tmp / f"r{i:02d}.json", exact=True) for i in range(K)]}
            save(args.pk, canonical(context))
            ctx = load_context(args.pk)
            for i in range(K):
                phases.append(child("recipient-finalize", context=args.pk, row=i, secret=tmp / f"a{i:02d}.pending", out=secret_dir / f"r{i:02d}.key"))
                (tmp / f"a{i:02d}.pending").unlink()
        zero = pack(ctx, STATE, [1] * (D + 1))
        save(args.zero, zero)
        return {"params_id": PARAMS_ID, "program_id": PROGRAM_ID, "key_id": ctx["id"], "context_id": ctx["id"],
                "public_key_sha256": ctx["id"], "public_key_bytes": len(canonical(context)), "zero_ct_sha256": sha(zero),
                "zero_ct": metadata(ctx, zero, STATE), "recipient_key_pattern": "r%02d.key", "recipient_count": K,
                "master_serialized": False, "projection_delivery_files_remaining": 0, "private_pending_files_remaining": 0,
                "physical_erasure_verified": False, "phases": phases}
    require(args.context is not None, "--context required")
    ctx = load_context(args.context)
    if args.command == "encode-query":
        row = vector(args.vector)
        candidates = [i for i, fixed in enumerate(ROWS) if row == fixed]
        require(len(candidates) == 1, "one fixed registered query required")
        raw = canonical(query_obj(ctx, candidates[0]))
        save(args.out, raw)
        return {"sha256": sha(raw), "bytes": len(raw), **{k: v for k, v in query_obj(ctx, candidates[0]).items() if k != "coefficients"}}
    if args.command == "issuer-encrypt":
        require(sha(read(args.pk, 1_000_000)) == ctx["id"], "public key/context identity")
        x = vector(args.vector)
        table, value = {}, exp(G, -127)
        for coordinate in range(-127, 128):
            table[coordinate] = value
            value = value * G % P
        r = secrets.randbelow(Q)
        values = [exp(G, r)] + [exp(h, r) * table[v] % P for h, v in zip(ctx["h"], x, strict=True)]
        raw = pack(ctx, STATE, values)
        save(args.out, raw)
        return metadata(ctx, raw, STATE)
    if args.command in ("inspect", "normalize", "inspect-recipient"):
        expected = SECRET if args.command == "inspect-recipient" else None
        values, kind, row_id, raw = unpack(ctx, args.sk if expected == SECRET else args.ct, expected)
        require(expected == SECRET or kind != SECRET, "public inspect ciphertext type")
        if args.command == "normalize":
            save(args.out, raw)
        meta = metadata(ctx, raw, kind, row_id)
        if kind == SECRET:
            # Never emit a hash of a private key file.
            meta.pop("sha256")
        return meta
    if args.command == "host-learn":
        acc = unpack(ctx, args.acc, STATE)[0]
        fresh = unpack(ctx, args.fresh, STATE)[0]
        values = [a * b % P for a, b in zip(acc, fresh, strict=True)]
        if args.old:
            old = unpack(ctx, args.old, STATE)[0]
            values = [a * pow(b, -1, P) % P for a, b in zip(values, old, strict=True)]
        raw = pack(ctx, STATE, values)
        save(args.out, raw)
        return {**metadata(ctx, raw, STATE), "expired_exact_supplied_original": args.old is not None,
                "queue_capacity_and_old_identity_enforced_by_caller": True}
    if args.command == "host-infer":
        acc = unpack(ctx, args.acc, STATE)[0]
        row_id = load_query(ctx, args.query)
        record = ctx["body"]["recipients"][row_id]
        projection = 1
        for c, y in zip(acc[1:], ROWS[row_id], strict=True):
            if y:
                projection = projection * exp(c, y) % P
        transformed = projection * pow(exp(acc[0], int(record["tau"], 16)), -1, P) % P
        raw = pack(ctx, OUTPUT, [acc[0], transformed], row_id)
        save(args.out, raw)
        return metadata(ctx, raw, OUTPUT, row_id)
    if args.command == "reader-decrypt":
        secret, _, row_id, _ = unpack(ctx, args.sk, SECRET)
        values, _, out_row, raw = unpack(ctx, args.ct, OUTPUT)
        require(row_id == out_row, "recipient output identity")
        group_value = values[1] * pow(exp(values[0], secret[0]), -1, P) % P
        answer, timing = decode(group_value, BOUNDS[row_id])
        return {"signed_score": answer, "sign": (answer > 0) - (answer < 0), "key_id": ctx["id"], "params_id": PARAMS_ID,
                "ciphertext_sha256": sha(raw), "row_id": row_id, "recipient_id": ctx["body"]["recipients"][row_id]["recipient_id"],
                "signed_score_bound": BOUNDS[row_id], **timing}
    raise Refusal("unknown command")


def main():
    global ENGINE
    parser = argparse.ArgumentParser(description=__doc__, allow_abbrev=False)
    sub = parser.add_subparsers(dest="command", required=True)
    specifications = {
        "params": [], "keygen": ["pk", "sk", "zero"],
        "initializer": ["bootstrap", "deliveries"],
        "recipient-register": ["bootstrap", "delivery", "row", "secret", "registration"],
        "recipient-finalize": ["row", "secret", "out"],
        "encode-query": ["vector", "out"], "issuer-encrypt": ["pk", "vector", "out"],
        "inspect": ["ct"], "inspect-recipient": ["sk"], "normalize": ["ct", "out"],
        "host-learn": ["acc", "fresh", "out"], "host-infer": ["acc", "query", "out"],
        "reader-decrypt": ["sk", "ct"]}
    for command, flags in specifications.items():
        p = sub.add_parser(command, allow_abbrev=False)
        p.add_argument("--context")
        for flag in flags:
            p.add_argument("--" + flag, required=True, type=int if flag == "row" else str)
        if command == "host-learn":
            p.add_argument("--old")
    args = parser.parse_args()
    start = time.perf_counter_ns()
    try:
        ENGINE = NativePow(P)
        result = run(args)
        result["process_work_ns"] = time.perf_counter_ns() - start
        result["counts"] = dict(COUNTS)
        print(canonical(result).decode(), flush=True)
    except (Refusal, OSError, ValueError, KeyError, TypeError, struct.error, subprocess.SubprocessError) as error:
        # Reasons carry no plaintext/scalar values or private file bytes.
        print(canonical({"ok": False, "error": type(error).__name__, "reason": str(error) if isinstance(error, Refusal) else "input/runtime failure"}).decode(), file=sys.stderr)
        raise SystemExit(2)
    finally:
        if ENGINE is not None:
            ENGINE.close()


if __name__ == "__main__":
    main()
