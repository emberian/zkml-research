"""[EXECUTED] Public aggregate sampler tests; never writes sampled coefficients."""
import hashlib
import json
import math
from pathlib import Path
import platform
import sys
import time
from unittest.mock import patch

from flint import arb, ctx
import flint
import sampler

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def verify():
    ctx.prec = 420
    low, high = sampler.squeeze_table()
    counts = {"exact_integer_threshold_checks": 0, "arb_interval_checks": 0,
              "squeeze_enclosure_checks": 0, "prefix_decision_boundary_checks": 0}
    inputs = [(k, 1024) for k in range(8193)]
    # Deterministic, public points across every key-width table cell.
    for j in range(sampler.CELLS):
        for offset in (0, 32767, 65535):
            inputs.append((j * 65536 + offset, 2 ** 25))
    for k, sigma in inputs:
        vl, vu = sampler.rho_interval(k, sigma)
        truth = (-arb.pi() * k * k / (sigma * sigma)).exp()
        assert arb((vl, -320)) <= truth.lower()
        assert truth.upper() <= arb((vu, -320))
        counts["arb_interval_checks"] += 1
        level = sampler.threshold(k, sigma)
        assert level == vl >> 64
        assert sampler.threshold(-k, sigma) == level
        counts["exact_integer_threshold_checks"] += 1
        if k == 8 * sigma:
            continue
        cell = k * sampler.GRID // sigma
        assert low[cell] <= level <= high[cell]
        counts["squeeze_enclosure_checks"] += 1
        # These edge inequalities certify all possible suffixes for each
        # nonempty fast-accept/reject prefix region, not sampled coin tests.
        lp = low[cell] >> sampler.SUFFIX_BITS
        hp = (high[cell] + (1 << sampler.SUFFIX_BITS) - 1) >> sampler.SUFFIX_BITS
        if lp:
            assert (lp << sampler.SUFFIX_BITS) - 1 < level
        assert hp << sampler.SUFFIX_BITS >= level
        counts["prefix_decision_boundary_checks"] += 1

    s = sampler.GaussianSampler()
    # Boundary rejection must actually exhaust the 4096-attempt cap.
    with patch.object(sampler.os, "urandom", lambda n: bytes(n)):
        assert s.sample(1024, 1) == [0]
    assert s.last_stats["proposals"] == 4096
    assert s.last_stats["boundary_rejections"] == 4096
    assert s.last_stats["cap_fallbacks"] == 1
    cap_stats = dict(s.last_stats)

    # Force the rare suffix comparison on both sides of the exact threshold.
    suffix_stats = []
    k, sigma = 513, 1024
    level = sampler.threshold(k, sigma)
    top, rem = divmod(level, 1 << sampler.SUFFIX_BITS)
    assert rem > 0
    for suffix, expected in ((rem - 1, k), (rem, 0)):
        def tape(n):
            if n == 28:
                return suffix.to_bytes(28, "little")
            first = (8 * sigma + k).to_bytes(2, "little") + top.to_bytes(4, "little")
            zero = (8 * sigma).to_bytes(2, "little") + bytes(4)
            assert n % 6 == 0
            return first + zero * (n // 6 - 1)
        with patch.object(sampler.os, "urandom", tape):
            assert s.sample(sigma, 1) == [expected]
        assert s.last_stats["suffix_draws"] == 1
        assert s.last_stats["direct_threshold_evaluations"] == 1
        assert s.last_stats["cap_fallbacks"] == 0
        suffix_stats.append(dict(s.last_stats))

    invalid = 0
    for sigma, count in ((0, 1), (-1, 1), (3, 1), (True, 1), (1024, -1), (1024, True)):
        try:
            s.sample(sigma, count)
        except ValueError:
            invalid += 1
        else:
            raise AssertionError("invalid input accepted")
    assert s.sample(1024, 0) == []
    return {"all_passed": True, **counts, "invalid_inputs_rejected": invalid,
            "forced_cap": cap_stats, "forced_suffix_comparisons": suffix_stats,
            "arb_precision_bits": ctx.prec,
            "oracle_scope": "420-bit Arb exp/pi enclosure at the named finite public points; no random-law proof inferred from empirical moments"}


def benchmark(s, sigma, count):
    values = s.sample(sigma, count)
    stats = dict(s.last_stats)
    total = sum(values)
    sum_squares = sum(k * k for k in values)
    mean = total / count
    second_moment = sum_squares / count
    target_variance = sigma * sigma / (2 * math.pi)
    stats.update({
        "mean_over_sigma": mean / sigma,
        "second_moment_over_sigma_squared": second_moment / (sigma * sigma),
        "reference_continuous_second_moment": 1 / (2 * math.pi),
        "mean_standard_errors": mean / math.sqrt(target_variance / count),
        "min_over_sigma": min(values) / sigma,
        "max_over_sigma": max(values) / sigma,
        "all_within_support": all(abs(k) < 8 * sigma for k in values),
        "sample_bytes_persisted": 0,
    })
    assert stats["all_within_support"]
    # Broad gross-error controls only, explicitly not a randomness certificate.
    assert abs(stats["mean_standard_errors"]) < 8
    assert 0.15 < stats["second_moment_over_sigma_squared"] < 0.17
    del values
    return stats


def main():
    start = time.perf_counter()
    source_before = {p.name: sha(p) for p in (HERE / "sampler.py", Path(__file__))}
    setup_start = time.perf_counter()
    s = sampler.GaussianSampler()
    table_seconds = time.perf_counter() - setup_start
    tests = verify()
    measured = [benchmark(s, width, count)
                for count in (100_000, 1_000_000)
                for width in (2 ** 10, 2 ** 25)]
    source_after = {p.name: sha(p) for p in (HERE / "sampler.py", Path(__file__))}
    assert source_before == source_after
    result = {
        "claim_label": "EXECUTED",
        "command": "research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_implementation/.venv/bin/python -B research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_implementation/sampling/verify_and_benchmark.py",
        "completed_utc": time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime()),
        "python": sys.version, "platform": platform.platform(),
        "python_flint": flint.__version__, "source_sha256": source_after,
        "table_build_seconds": table_seconds,
        "table_cells": sampler.CELLS,
        "table_integer_payload_bytes": 2 * sampler.CELLS * 32,
        "python_table_objects_bytes": sum(sys.getsizeof(t) + sum(sys.getsizeof(x) for x in t)
                                          for t in (s._low, s._high, s._prefix_low, s._prefix_high)),
        "tests": tests, "benchmarks": measured,
        "sampled_coefficients": sum(x["count"] for x in measured),
        "raw_samples_written": 0,
        "secrets_keys_ciphertexts_written": 0,
        "search_queries": 0,
        "elapsed_seconds": time.perf_counter() - start,
        "qualification": "Exact specified finite output law under independent unbiased OS-byte idealization; OS generator security, side channels, host memory exposure, and production audit remain separate. Empirical moments are gross-error controls only.",
    }
    (HERE / "MEASUREMENTS.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"all_passed": True, "samples": result["sampled_coefficients"],
                      "threshold_checks": tests["exact_integer_threshold_checks"],
                      "seconds": result["elapsed_seconds"],
                      "benchmarks": [{k: b[k] for k in ("sigma", "count", "seconds", "coefficients_per_second", "proposals", "direct_threshold_evaluations", "suffix_draws", "cap_fallbacks", "os_random_bytes_requested")} for b in measured]}, sort_keys=True))


if __name__ == "__main__":
    main()
