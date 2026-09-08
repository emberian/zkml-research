#!/usr/bin/env python3
"""Concrete public seed setup using frozen direct-setup algebra and registration."""
from pathlib import Path
import argparse
import json
import sys
import time
import derive

HERE = Path(__file__).resolve().parent
FROZEN = HERE / "source/public_setup"
sys.path.insert(0, str(FROZEN))
import setup as original
c = original.c


def descriptor(reg, announcements):
    public_A = original.check_announcements(reg, announcements)
    c.require(len(public_A) == c.K, "complete fixed registry before derivation")
    for value in public_A:
        c.subgroup(value)
    original.matrices()
    return {
        "schema": "designated-complete-seed-domain-v1", "suite": derive.SUITE,
        "p_hex": c.hx(c.P), "q_hex": c.hx(c.Q), "generator": c.G,
        "dimension": c.D, "row_count": c.K, "capacity": c.W,
        "rows": c.ROWS, "pivot_columns": list(range(c.K)),
        "rejection_cap": derive.CAP,
        "complete_registry": [dict(reg["slots"][i], A=c.hx(public_A[i])) for i in range(c.K)],
    }, public_A


def source_identity():
    manifest = (HERE / "SOURCE_PINS.json").read_bytes()
    return {"manifest_sha256": c.sha(manifest), "seed_setup_sha256": c.sha(Path(__file__).read_bytes()),
            "derive_sha256": c.sha((HERE / "derive.py").read_bytes()),
            "frozen_direct_setup_sha256": c.sha((FROZEN / "setup.py").read_bytes()),
            "crypto_sources": original.freeze(), "native_dependency": original.native_pin()}


def make_transcript(reg, reg_sha, announcements):
    domain, public_A = descriptor(reg, announcements)
    try:
        derived = derive.derive(domain)
    except derive.SeedRejected as error:
        error.partial = {"schema": "designated-public-seed-rejected-v1", "status": "rejected",
                         "params_id": c.PARAMS_ID, "registry_sha256": reg_sha,
                         "announcements": announcements, "complete_domain": domain,
                         "source_identity": source_identity(), "derivation": error.partial,
                         "context_created": False, "retry_permitted": False}
        raise
    tau = [c.unhex(t, scalar=True) for t in derived["tau"]]
    values = [c.unhex(u) for u in derived["U"]]
    h, det = original.complete(public_A, tau, values)
    context = original.context_body(h, public_A, tau)
    return {
        "schema": "designated-public-seed-transcript-v1", "status": "accepted",
        "context_id": c.digest(context), "params_id": c.PARAMS_ID,
        "registry_sha256": reg_sha, "announcements": announcements,
        "complete_domain": domain, "domain_sha256_for_inventory_only": c.digest(domain),
        "derivation": derived, "integer_pivot_determinant": det,
        "source_identity": source_identity(),
        "scope": "SHAKE256 deterministic public recipe; ROM theorem conditional, no concrete-hash/QROM/timing privacy claim",
    }, context


def execute(a):
    if a.command in ("auth-init", "recipient-init"):
        return original.execute(a)
    reg, reg_sha = original.registry(a.registry, a.registry_sha256)
    if a.command == "public-build":
        announcements = [c.read_json(Path(a.announcements)/f"r{i:02d}.json", exact=True) for i in range(c.K)]
        transcript, context = make_transcript(reg, reg_sha, announcements)
        original.saved(a.context, context)
        ctx = {"body": context, "id": c.digest(context)}
        c.save(a.zero, c.pack(ctx, c.STATE, [1]*(c.D+1)))
        original.saved(a.transcript, transcript)
        return {"context_id": ctx["id"], "transcript_sha256": c.digest(transcript),
                "public_seed_candidates": 1, "fresh_recipient_count_required": c.K,
                "hash_words": sum(len(t["raw_words_hex"]) for t in transcript["derivation"]["tapes"]),
                "scalar_master_computed": False, "scalar_projection_delivery_computed": False}
    if a.command == "verify-public":
        observed = c.read_json(a.transcript, cap=60_000_000, exact=True)
        c.require(observed["registry_sha256"] == reg_sha, "registry identity")
        expected, context = make_transcript(reg, reg_sha, observed["announcements"])
        c.require(c.canonical(observed) == c.canonical(expected), "complete hash transcript replay")
        c.require(c.read(a.context, 1_000_000) == c.canonical(context), "complete context replay")
        return {"ok": True, "complete_raw_hash_tape_match": True, "complete_context_byte_match": True,
                "context_id": c.digest(context), "transcript_sha256": c.digest(expected),
                "public_inputs_only": True}
    raise ValueError("command")


def main():
    parser = argparse.ArgumentParser(allow_abbrev=False)
    subs = parser.add_subparsers(dest="command", required=True)
    specs = {"auth-init": ["private", "out"],
             "recipient-init": ["registry", "registry-sha256", "row", "auth-key", "pending", "out"],
             "public-build": ["registry", "registry-sha256", "announcements", "context", "transcript", "zero"],
             "verify-public": ["registry", "registry-sha256", "context", "transcript"]}
    for command, flags in specs.items():
        sub = subs.add_parser(command, allow_abbrev=False)
        for flag in flags:
            sub.add_argument("--"+flag, required=True, type=int if flag == "row" else str)
    a = parser.parse_args()
    started = time.perf_counter_ns()
    c.ENGINE = c.NativePow(c.P)
    try:
        result = execute(a)
        result.update(process_work_ns=time.perf_counter_ns()-started, counts=dict(c.COUNTS))
        print(json.dumps(result), flush=True)
    except derive.SeedRejected as error:
        if a.command == "public-build":
            original.saved(a.transcript, error.partial)
        print(json.dumps({"ok": False, "reason": "fixed public cap exhausted; no retry"}), file=sys.stderr)
        raise SystemExit(2)
    finally:
        c.ENGINE.close()


if __name__ == "__main__":
    main()
