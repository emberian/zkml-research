#!/usr/bin/env python3
"""One 577D DDH-IPFE public-fixture micro-measurement, not a full benchmark.

Calls only the approved control's group constants. Private setup/issuer roles
exit before the evaluator. CPython arithmetic and lookup are not constant-time.
"""
from pathlib import Path
import argparse
import hashlib
import importlib.util
import json
import math
import platform
import resource
import secrets
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
EXPERIMENTS = HERE.parents[2]
UTILITY = EXPERIMENTS / "end_to_end/utility"
sys.path.insert(0, str(HERE.parents[1]))
from additive_ipfe import P, Q, G

D, K, WIDTH = 577, 16, 256


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def dump(path, values):
    Path(path).write_bytes(b"".join(v.to_bytes(WIDTH, "big") for v in values))


def load(path, count):
    raw = Path(path).read_bytes()
    assert len(raw) == count*WIDTH
    return tuple(int.from_bytes(raw[i:i+WIDTH], "big") for i in range(0, len(raw), WIDTH))


def queries():
    rows = [json.loads(p.read_text()) for p in sorted((UTILITY / "public_queries").glob("q*.json"))]
    assert len(rows) == K and all(len(y) == D for y in rows)
    return rows


def finish(report):
    report["role_peak_rss_bytes_macos"] = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    print(json.dumps(report), flush=True)


def setup(out):
    start = time.perf_counter_ns()
    master = tuple(secrets.randbelow(Q) for _ in range(D))
    public = tuple(pow(G, s, P) for s in master)
    keys = tuple(sum(a*b for a, b in zip(master, y, strict=True)) % Q for y in queries())
    elapsed = time.perf_counter_ns()-start
    dump(out / "public.bin", public)
    dump(out / "fixed_keys.bin", keys)
    # No master serialization. Exit is not proof of physical secure erasure.
    finish({"role": "honest_private_setup", "elapsed_ns": elapsed,
            "exports": ["public.bin", "fixed_keys.bin"], "master_exported": False})


def issue(out, vector_path):
    public = load(out / "public.bin", D)
    vector = json.loads(Path(vector_path).read_text())
    assert len(vector) == D and all(type(x) is int and abs(x) <= 127 for x in vector)
    # Same source equation, public bounded-message table avoids full exponents
    # for tiny signed coordinates. This lookup is not constant-time.
    start = time.perf_counter_ns()
    encodings = {}
    value = pow(G, -127, P)
    for x in range(-127, 128):
        encodings[x] = value
        value = value*G % P
    encoding_ns = time.perf_counter_ns()-start
    start = time.perf_counter_ns()
    randomness = secrets.randbelow(Q)
    ciphertext = (pow(G, randomness, P),) + tuple(
        pow(h, randomness, P)*encodings[x] % P for h, x in zip(public, vector, strict=True))
    encrypt_ns = time.perf_counter_ns()-start
    dump(out / "input.bin", ciphertext)
    finish({"role": "private_issuer_public_key_only", "encrypted_vectors": 1,
            "encoding_table_ns": encoding_ns, "encryption_ns": encrypt_ns,
            "ciphertext_bytes": (D+1)*WIDTH,
            "diagnostic_scope": "private synthetic micro-log; not a deployed host API"})


def evaluate(out):
    keys = load(out / "fixed_keys.bin", K)
    ciphertext = load(out / "input.bin", D+1)
    rows = queries()
    start = time.perf_counter_ns()
    assert all(1 <= c < P and pow(c, Q, P) == 1 for c in ciphertext)
    validate_ns = time.perf_counter_ns()-start
    # Only the first preauthorized fixed query is measured, not all 16 reads.
    y = rows[0]
    start = time.perf_counter_ns()
    projection = pow(pow(ciphertext[0], keys[0], P), -1, P)
    for c, exponent in zip(ciphertext[1:], y, strict=True):
        projection = projection*pow(c, exponent, P) % P
    projection_ns = time.perf_counter_ns()-start
    bound = max(sum(map(abs, y)) for y in rows)*32*127
    m = math.isqrt(2*bound+1)
    if m*m < 2*bound+1:
        m += 1
    start = time.perf_counter_ns()
    baby = {}
    value = 1
    for j in range(m):
        baby[value] = j
        value = value*G % P
    factor = pow(G, -m, P)
    shift = pow(G, bound, P)
    table_ns = time.perf_counter_ns()-start
    start = time.perf_counter_ns()
    target = projection*shift % P
    answer = None
    for i in range((2*bound)//m+1):
        j = baby.get(target)
        if j is not None and i*m+j <= 2*bound:
            answer = i*m+j-bound
            break
        target = target*factor % P
    decode_ns = time.perf_counter_ns()-start
    assert answer is not None
    table_bytes = sys.getsizeof(baby)+sum(sys.getsizeof(k)+sys.getsizeof(v) for k,v in baby.items())
    finish({"role": "host_fixed_key_evaluator", "validation_ns": validate_ns,
            "validated_ciphertext_elements": D+1, "fixed_projection_ns": projection_ns,
            "fixed_query_index": 0, "fixed_projection_reads": 1, "score": answer,
            "bsgs_table_ns": table_ns, "bsgs_decode_ns": decode_ns,
            "bsgs_common_bound": bound, "bsgs_baby_entries": m,
            "bsgs_giant_iterations_actual": i+1,
            "bsgs_python_table_bytes_shallow_plus_entries": table_bytes,
            "master_or_plaintext_input": False})


def run():
    out = HERE / "micro_results"
    out.mkdir(exist_ok=True)
    vector = UTILITY / "issuer_oracle/vectors/h0-e0001.json"
    phases = []
    for role in ("setup", "issue", "evaluate"):
        args = [sys.executable, "-I", "-B", str(Path(__file__).resolve()), role, "--out", str(out)]
        if role == "issue":
            args += ["--vector", str(vector)]
        print(json.dumps({"event": "starting", "role": role}), flush=True)
        start = time.perf_counter_ns()
        completed = subprocess.run(args, check=True, capture_output=True, text=True)
        phase = json.loads(completed.stdout)
        phase["subprocess_wall_ns"] = time.perf_counter_ns()-start
        phases.append(phase)
        print(json.dumps(phase), flush=True)
    # Separate public-fixture test oracle, not an evaluator input.
    x, y = json.loads(vector.read_text()), queries()[0]
    expected = sum(a*b for a,b in zip(x,y,strict=True))
    assert phases[-1]["score"] == expected
    report = {"passed": True, "scope": "one actual public-fixture encryption and one authorized fixed projection",
        "script_sha256": sha(__file__), "approved_group_control_sha256": sha(HERE.parents[1]/"additive_ipfe.py"),
        "linear_audit_sha256": sha(HERE/"linear_audit.py"),
        "linear_results_sha256": sha(HERE/"linear_results.json"),
        "input_public_fixture_sha256": sha(vector),
        "input_public_fixture_path": str(vector),
        "query0_sha256": sha(UTILITY/"public_queries/q00.json"),
        "python": sys.version, "platform": platform.platform(), "machine": platform.machine(),
        "phases": phases, "full_384_input_benchmark": False,
        "constant_time": False, "numerical_security_bits_claimed": None,
        "no_master_export": True, "physical_erasure_verified": False,
        "outputs": {p.name: {"bytes": p.stat().st_size, "sha256": sha(p)}
                    for p in out.iterdir() if p.suffix == ".bin"},
        "searches": {"scry_sql": 0, "web": 0, "package_installs": 0}}
    (HERE/"micro_results.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"passed": True, "score_matches_separate_oracle": True,
                      "encrypted_vectors": 1, "fixed_projection_reads": 1}), flush=True)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("role", nargs="?", default="run", choices=["run", "setup", "issue", "evaluate"])
    parser.add_argument("--out", type=Path)
    parser.add_argument("--vector", type=Path)
    args = parser.parse_args()
    if args.role == "run": run()
    elif args.role == "setup": setup(args.out)
    elif args.role == "issue": issue(args.out, args.vector)
    elif args.role == "evaluate": evaluate(args.out)
