#!/usr/bin/env python3
"""Replay retained public operations with two independent integer algorithms."""
import argparse
import gzip
import json
from math import isqrt
from pathlib import Path
import platform
import sys
import time
from reference import (N, MODULI, WIDTH, bitrev, cyclic_ntt, decode_ct, decode_query,
                       infer, learn, negacyclic_direct, negacyclic_ntt,
                       primitive_root, require, sha, source_indexed_backward,
                       source_indexed_forward)

HERE = Path(__file__).resolve().parent


def transform_checks():
    records = []
    for size, p in [(8, 97), (16, 193), (32, 257)]:
        psi = primitive_root(p, size)
        bits = size.bit_length() - 1
        checked = 0
        for exponent in (1, 3):
            root = pow(psi, exponent, p)
            for monomial in range(size):
                values = [int(i == monomial) for i in range(size)]
                transformed = source_indexed_forward(values, root, p)
                expected = [pow(root, (2 * bitrev(k, bits) + 1) * monomial, p) for k in range(size)]
                require(transformed == expected, "indexed source schedule / odd-root evaluation")
                require(source_indexed_backward(transformed, root, p) == values, "source schedule inverse")
                checked += 1
            a = [(i * 37 + 5) % p for i in range(size)]
            b = [(i * i - 3) % p for i in range(size)]
            direct = negacyclic_direct(a, b, p)
            require(negacyclic_ntt(a, b, p, root) == direct, "twisted cyclic versus schoolbook")
            fa, fb = source_indexed_forward(a, root, p), source_indexed_forward(b, root, p)
            require(source_indexed_backward([x * y % p for x, y in zip(fa, fb)], root, p) == direct, "indexed schedule ring multiplication")
        # Positive wrap convention: X^(N-1)*X = -1 in the chosen quotient ring.
        a, b = [0] * size, [0, 1]
        a[-1] = 1
        require(negacyclic_direct(a, b, p) == [p - 1] + [0] * (size - 1), "negacyclic sign convention")
        records.append({"degree": size, "modulus": p, "independent_primitive_root": psi,
                        "basis_vectors_checked": checked, "two_roots_product_and_inverse_match": True})
    return records


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--run", default="run_001")
    parser.add_argument("--manifest", default="fixtures.json", choices=["fixtures.json", "utility-fixtures.json"])
    args = parser.parse_args()
    require(args.run.startswith("run_") and args.run[4:].isdigit(), "run label")
    target = HERE / "results" / args.run
    target.mkdir(parents=True, exist_ok=False)
    start = time.monotonic()
    manifest_bytes = (HERE / args.manifest).read_bytes()
    manifest = json.loads(manifest_bytes)
    decoded, raw, queries = {}, {}, {}
    for identity, record in manifest["blobs"].items():
        compressed = (HERE / record["path"]).read_bytes()
        require(sha(compressed) == record["gzip_sha256"], "retained gzip identity")
        data = gzip.decompress(compressed)
        require(sha(data) == identity and len(data) == record["bytes"], "retained object identity")
        raw[identity] = data
        if record["kind"] == "public_ciphertext":
            decoded[identity] = decode_ct(data)
        else:
            queries[identity] = decode_query(data)
    small = transform_checks()
    prime_checks = []
    for p in MODULI:
        trial_count = 0
        require(p % 2 == 1, "odd modulus")
        for divisor in range(3, isqrt(p) + 1, 2):
            require(p % divisor != 0, "prime modulus by exhaustive trial division")
            trial_count += 1
        psi = primitive_root(p, N)
        prime_checks.append({"modulus": p, "odd_trial_divisors_checked": trial_count,
                             "trial_division_through_integer_sqrt": True,
                             "independent_primitive_8192_root": psi,
                             "root_power_4096": pow(psi, N, p), "root_power_8192": pow(psi, 2*N, p)})
    events, source_schedule_checks = [], []
    total_coefficients = 0
    for event in manifest["events"]:
        hashes = event["hashes"]
        acc = decoded[hashes["acc"]]
        begin = time.monotonic()
        if event["kind"] == "Learn":
            result = learn(acc, decoded[hashes["fresh"]], decoded[hashes["old"]] if "old" in hashes else None)
            alternate_seconds = None
        else:
            query = queries[hashes["query"]]
            result = infer(acc, query)
            alt_start = time.monotonic()
            transformed = infer(acc, query, negacyclic_ntt)
            alternate_seconds = time.monotonic() - alt_start
            require(transformed.components == result.components, "full independent NTT/schoolbook agreement")
            if not source_schedule_checks:
                for c in range(2):
                    for j, p in enumerate(MODULI):
                        a = acc.components[c][j]
                        psi = primitive_root(p, N)
                        fs = source_indexed_forward(a, psi, p)
                        twist = [a[i] * pow(psi, i, p) % p for i in range(N)]
                        standard = cyclic_ntt(twist, psi * psi % p, p)
                        require(fs == [standard[bitrev(k, 12)] for k in range(N)], "full source ordering relation")
                        require(source_indexed_backward(fs, psi, p) == a, "full source-indexed inverse")
                        q = list(reversed(query)) + [0] * (N - WIDTH)
                        fq = source_indexed_forward(q, psi, p)
                        source_product = source_indexed_backward([x * y % p for x, y in zip(fs, fq)], psi, p)
                        require(source_product == result.components[c][j], "full source-indexed convolution")
                        source_schedule_checks.append({"event_id": event["event_id"], "component": c,
                            "limb": j, "modulus": p, "independent_root": psi, "source_odd_root_ordering": True,
                            "source_equation_inverse": True, "source_equation_product_matches_direct": True})
                # Reproduce the source's separate nonnegative plaintext
                # products, then subtract. This is a valid-operation identity.
                plus = [max(x, 0) for x in reversed(query)]
                minus = [max(-x, 0) for x in reversed(query)]
                for c in range(2):
                    for j, p in enumerate(MODULI):
                        pos = negacyclic_direct(acc.components[c][j], plus, p)
                        neg = negacyclic_direct(acc.components[c][j], minus, p)
                        require([(x - y) % p for x, y in zip(pos, neg)] == result.components[c][j], "source plus/minus query decomposition")
        expected = decoded[hashes["result"]]
        require(result.components == expected.components, "every public ciphertext coefficient agrees")
        wire = result.encode()
        require(wire == raw[hashes["result"]], "full ciphertext serialization agrees")
        checked = 2 * len(MODULI) * N
        total_coefficients += checked
        record = {"event_id": event["event_id"], "kind": event["kind"], "expiry": "old" in hashes,
                  "coefficients_checked": checked, "all_coefficients_match": True, "all_85103_bytes_match": True,
                  "result_sha256": sha(wire), "elapsed_seconds": time.monotonic() - begin,
                  "independent_ntt_seconds": alternate_seconds}
        if event["kind"] == "Infer":
            record["public_query_support"] = {"width": len(query), "positive": sum(x > 0 for x in query),
                "negative": sum(x < 0 for x in query), "zero": sum(x == 0 for x in query),
                "first_coefficient": query[0], "last_coefficient": query[-1]}
        events.append(record)
        print(json.dumps(record), flush=True)
    report = {"schema": "independent-public-bfv-arithmetic-v1", "ok": True,
              "suite": manifest.get("suite", "host_runtime_public_synthetic_run_001"), "fixture_manifest_file": args.manifest,
              "scope": "Sampled public BFV operation and serialized-byte correspondence; no secret keys, private ingress vectors, decryption, adversarial extraction/routing tests, production arithmetic calls or universal Rust/compiler/noise refinement",
              "degree": N, "ciphertext_moduli": MODULI, "query_width": WIDTH,
              "events": events, "learns": sum(e["kind"] == "Learn" for e in events),
              "expiries": sum(e["expiry"] for e in events), "infers": sum(e["kind"] == "Infer" for e in events),
              "ciphertext_objects_decoded_and_reencoded": len(decoded), "public_queries_decoded": len(queries),
              "total_output_coefficients_checked": total_coefficients,
              "total_output_bytes_checked": sum(len(raw[e["hashes"]["result"]]) for e in manifest["events"]),
              "small_transform_basis_checks": small, "full_source_indexed_equation_checks": source_schedule_checks,
              "prime_and_root_checks": prime_checks,
              "fixture_manifest_sha256": sha(manifest_bytes), "reference_source_sha256": sha((HERE / "reference.py").read_bytes()),
              "checker_source_sha256": sha(Path(__file__).read_bytes()), "python": sys.version,
              "platform": platform.platform(), "elapsed_seconds": time.monotonic() - start}
    (target / "report.json").write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({"ok": True, "report": str(target / "report.json"), "coefficients": total_coefficients, "seconds": report["elapsed_seconds"]}), flush=True)


if __name__ == "__main__":
    main()
