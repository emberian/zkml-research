#!/usr/bin/env python3
"""Independent fixed-span positive algebra and adaptive-hybrid verification.

Small groups test exact equations/distributions only, not DDH hardness. Events
below inspect public ciphertext labels; no plaintext recovery is implemented.
The old additive_ipfe.main is never called. The approved positive audit is run
only from byte-identical copies in this review's owned directory.
"""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import product
from pathlib import Path
import json
import platform
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
TASK = HERE.parents[2]
AUTHOR = TASK / "experiments/private_construction/fixed_span"
PDF = Path("/Users/ember/dev/gh/forks/IACR-eprint-mirror/2015/017.pdf")
EXPECTED_NOTE = "091403d6f3e1a7a65e5baef3977dc789595584582d17bbbf2190878fa18874d9"
Y = ((1, 1, 0), (0, 1, 1))
W = (1, -1, 1)


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def dot(x, y, q):
    return sum(a*b for a, b in zip(x, y)) % q


def setup(q, p, g, t0, t1, a):
    s = ((t0+a) % q, (t1-a) % q, a)
    return tuple(pow(g, v, p) for v in s), ((t0+t1) % q, t1)


def encrypt(q, p, g, public, x, r):
    return (pow(g, r, p),) + tuple(pow(h, r, p)*pow(g, v % q, p) % p for h, v in zip(public, x))


def embed(q, p, g, t0, t1, B, C, x):
    return (B, pow(B, t0, p)*C*pow(g, x[0] % q, p) % p,
            pow(B, t1, p)*pow(C, -1, p)*pow(g, x[1] % q, p) % p,
            C*pow(g, x[2] % q, p) % p)


def algebra():
    map_cases = kernel_cases = embedding_cases = uniform_cases = 0
    for q, p, g in ((3, 7, 2), (5, 11, 3), (7, 29, 7)):
        assert pow(g, q, p) == 1 and len({pow(g, a, p) for a in range(q)}) == q
        seen = Counter()
        for t0, t1, a in product(range(q), repeat=3):
            s = ((t0+a) % q, (t1-a) % q, a)
            seen[s] += 1
            _, keys = setup(q, p, g, t0, t1, a)
            assert tuple(dot(s, y, q) for y in Y) == keys
            map_cases += 1
        assert len(seen) == q**3 and set(seen.values()) == {1}
        for d in product(range(q), repeat=3):
            in_kernel = all(dot(d, y, q) == 0 for y in Y)
            assert in_kernel == (d == (d[0], -d[0] % q, d[0]))
            kernel_cases += 1
        for t0, t1, a, b in product(range(q), repeat=4):
            public, keys = setup(q, p, g, t0, t1, a)
            # A message determined from the public setup, rather than prechosen.
            x0 = tuple((sum(public)+sum(keys)+j) % q for j in range(3))
            B = pow(g, b, p)
            assert embed(q, p, g, t0, t1, B, pow(g, a*b, p), x0) == encrypt(q, p, g, public, x0, b)
            embedding_cases += 1
            left = Counter(embed(q, p, g, t0, t1, B, pow(g, c, p), x0) for c in range(q))
            for k in range(q):
                x1 = tuple((v+k*w) % q for v, w in zip(x0, W))
                assert all(dot(x0, y, q) == dot(x1, y, q) for y in Y)
                right = Counter(embed(q, p, g, t0, t1, B, pow(g, c, p), x1) for c in range(q))
                assert left == right
                for c in range(q):
                    assert embed(q, p, g, t0, t1, B, pow(g, (c-k) % q, p), x1) == embed(q, p, g, t0, t1, B, pow(g, c, p), x0)
                uniform_cases += 1
    return {"setup_bijection_cases": map_cases, "kernel_equivalence_cases": kernel_cases,
            "real_DDH_embedding_identities": embedding_cases,
            "conditioned_uniform_C_multiset_equalities": uniform_cases,
            "scope": "exact finite public group algebra; no hardness claim"}


def pair_from_public_history(q, public, keys, transcript):
    checksum = sum(public) + sum(keys) + sum(sum(c) for c in transcript)
    left = ((checksum+len(transcript)) % q, checksum % q, len(transcript) % q)
    k = (1+checksum+len(transcript)) % q
    right = tuple((v+k*w) % q for v, w in zip(left, W))
    assert all(dot(left, y, q) == dot(right, y, q) for y in Y)
    return left, right


def run_public_strategy(q, p, g, public, keys, coins, boundary, selected=None, mu=0, selected_ct=None):
    transcript = []
    reached = False
    for rank, r in enumerate(coins, 1):
        pair = pair_from_public_history(q, public, keys, transcript)
        if rank == selected:
            ciphertext = selected_ct(pair[mu])
            reached = True
        else:
            side = 0 if rank <= boundary else 1
            ciphertext = encrypt(q, p, g, public, pair[side], r)
        transcript.append(ciphertext)
        # Public stopping rule exercises selected ranks that are never reached.
        if rank == 1 and ciphertext[0] == 1:
            break
    # A public encoding event, not a decryption/recovery operation.
    output = int((sum(transcript[-1]) + sum(public)) % 2 == 0)
    return output, reached


def adaptive_hybrid():
    q, p, g, T, M = 3, 7, 2, 3, 4
    random_tapes = tuple(product(range(q), repeat=T))
    probabilities = []
    for boundary in range(T+1):
        ones = total = 0
        for t0, t1, a in product(range(q), repeat=3):
            public, keys = setup(q, p, g, t0, t1, a)
            for coins in random_tapes:
                output, _ = run_public_strategy(q, p, g, public, keys, coins, boundary)
                ones += output
                total += 1
        probabilities.append(Fraction(ones, total))
    ddh_probabilities = []
    missing_rank_cases = []
    for random_C in (False, True):
        twice_ones = total = missing = 0
        for t0, t1, a, b in product(range(q), repeat=4):
            public, keys = setup(q, p, g, t0, t1, a)
            c_values = range(q) if random_C else ((a*b) % q,)
            for c in c_values:
                callback = lambda x: embed(q, p, g, t0, t1, pow(g, b, p), pow(g, c, p), x)
                for coins, rank, mu in product(random_tapes, range(1, M+1), (0, 1)):
                    output, reached = run_public_strategy(q, p, g, public, keys, coins,
                                                          boundary=rank-1, selected=rank, mu=mu,
                                                          selected_ct=callback)
                    # All dummy or never-reached selections return a fair bit.
                    twice_ones += 2*int(output == mu) if reached else 1
                    missing += int(not reached)
                    total += 1
        ddh_probabilities.append(Fraction(twice_ones, 2*total))
        missing_rank_cases.append(missing)
    delta = probabilities[-1] - probabilities[0]
    assert ddh_probabilities[1] == Fraction(1, 2)
    assert ddh_probabilities[0] - ddh_probabilities[1] == -delta/(2*M)
    assert all(missing_rank_cases)
    return {"field_order": q, "max_queries_T": T, "padded_ranks_M": M,
            "hybrid_acceptance_probabilities": list(map(str, probabilities)),
            "DDH_real_acceptance": str(ddh_probabilities[0]),
            "DDH_independent_acceptance": str(ddh_probabilities[1]),
            "signed_telescoping_identity": True,
            "absolute_endpoint_gap": str(abs(delta)),
            "dummy_or_unreached_cases": missing_rank_cases,
            "strategy": "admissible pairs depend on public setup and actual prior ciphertexts; public early stop",
            "scope": "finite verification of reduction identity, not finite-group security"}


def snapshots():
    note = AUTHOR / "ADAPTIVE_FIXED_SPAN.md"
    assert digest(note) == EXPECTED_NOTE
    saved = json.loads((AUTHOR / "results/results.json").read_text())
    expected = saved["source_manifest"]
    assert digest(PDF) == expected["paper_sha256"]
    assert digest(AUTHOR / "span.py") == expected["span_source_sha256"]
    assert digest(AUTHOR / "audit.py") == expected["audit_source_sha256"]
    assert digest(AUTHOR.parent / "additive_ipfe.py") == expected["approved_control_sha256"]
    paths = [note, AUTHOR / "span.py", AUTHOR / "audit.py", AUTHOR / "README.md",
             AUTHOR / "results/results.json", AUTHOR / "results/public.bin",
             AUTHOR / "results/projection_keys.bin", AUTHOR / "results/synthetic_final.window",
             AUTHOR.parent / "additive_ipfe.py", PDF]
    return [{"path": str(path), "sha256": digest(path)} for path in paths]


def positive_reference_replay():
    target = HERE / "reference/fixed_span"
    target.mkdir(parents=True, exist_ok=True)
    for name in ("span.py", "audit.py"):
        shutil.copyfile(AUTHOR / name, target / name)
        assert digest(AUTHOR / name) == digest(target / name)
    shutil.copyfile(AUTHOR.parent / "additive_ipfe.py", target.parent / "additive_ipfe.py")
    command = [sys.executable, "-B", str(target / "audit.py")]
    result = subprocess.run(command, text=True, capture_output=True, check=False)
    (HERE / "positive_audit.stdout.txt").write_text(result.stdout)
    (HERE / "positive_audit.stderr.txt").write_text(result.stderr)
    assert result.returncode == 0 and not result.stderr
    saved = json.loads((AUTHOR / "results/results.json").read_text())
    replayed = json.loads((target / "results/results.json").read_text())
    keys = ["status", "bounded_input_states", "observable_classes", "ordered_equivalence_checks",
            "equivalent_ordered_pairs_including_diagonal", "expected_visible_trace_both_histories",
            "actual_fixed_projection_outputs_compared", "exact_queue_product_checks",
            "normal_checkpoint_continuations", "exact_old_ciphertext_expirations",
            "ciphertext_traffic_both_histories_bytes", "framed_checkpoint_bytes"]
    assert all(saved[key] == replayed[key] for key in keys)
    return {"command": command, "returncode": result.returncode,
            "source_copies_byte_identical": True, "matched_result_fields": keys,
            "approved_positive_audit_replayed": True, "old_additive_main_called": False,
            "timings": "new local measurements are retained but not compared as deterministic facts"}


def main():
    before = snapshots()
    result = {"classification": "EXECUTED independent positive fixed-span proof review",
              "command": [sys.executable, "-B", str(Path(__file__).resolve())],
              "python": platform.python_version(), "script_sha256": digest(Path(__file__)),
              "algebra": algebra(), "adaptive_hybrid": adaptive_hybrid(),
              "positive_reference_replay": positive_reference_replay(),
              "input_hashes_before": before,
              "fresh_local_extract_sha256": digest(HERE / "extracts/2015-017.txt")}
    after = snapshots()
    assert before == after
    result["input_hashes_after_equal_before"] = True
    result["accounting"] = {"Scry_queries": 0, "Kagi_queries": 0, "web_queries": 0,
                             "PDF_downloads": 0, "local_PDF_extractions": 1,
                             "recovery_or_extraction_experiments": 0}
    text = json.dumps(result, indent=2) + "\n"
    (HERE / "results.json").write_text(text)
    print(text, end="")


if __name__ == "__main__":
    main()
