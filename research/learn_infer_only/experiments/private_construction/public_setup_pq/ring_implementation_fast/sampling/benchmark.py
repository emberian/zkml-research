"""[EXECUTED] Focused differential/cap tests and actual 1M-coefficient timing."""
import hashlib
import json
import math
from pathlib import Path
import platform
import sys
import time
from unittest.mock import patch

import sampler

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


class PublicTape:
    """Synthetic public test data only; never used in the normal sampling API."""
    def __init__(self, label, size=4_000_000):
        self.data = hashlib.shake_256(label).digest(size)
        self.offset = 0

    def __call__(self, n):
        assert self.offset + n <= len(self.data)
        out = self.data[self.offset:self.offset + n]
        self.offset += n
        return out


def verify(fast, slow):
    invariant_fields = ("count", "proposals", "squeeze_accepts", "squeeze_rejects",
                        "direct_threshold_evaluations", "boundary_rejections",
                        "cap_fallbacks", "random_bytes_consumed_in_proposals", "suffix_draws")
    differential = []
    for width, count in [(1024, 10000), (2 ** 25, 10000)] + [(2 ** a, 32) for a in (0, 1, 7, 8, 9, 59)]:
        label = f"public native differential sigma={width}".encode()
        with patch.object(sampler.os, "urandom", PublicTape(label)):
            actual = fast.sample(width, count)
        with patch.object(sampler.os, "urandom", PublicTape(label)):
            expected = slow.sample(width, count)
        assert actual == expected
        for field in invariant_fields:
            assert fast.last_stats[field] == slow.last_stats[field], field
        differential.append({"sigma": width, "count": count, "outputs_equal": True,
                             "counter_fields_equal": list(invariant_fields)})
        del actual, expected

    controls = []
    for target_at, suffix_accept in ((None, False), (0, True), (0, False), (4095, True), (4095, False)):
        k, width = 513, 1024
        top, remainder = divmod(sampler.threshold(k, width), 1 << sampler.SUFFIX_BITS)
        class ForcedTape:
            def __init__(self):
                self.position = 0

            def __call__(self, n):
                if n == 28:
                    return (remainder - int(suffix_accept)).to_bytes(28, "little")
                assert n % 6 == 0
                values = []
                for _ in range(n // 6):
                    i = self.position
                    self.position += 1
                    if target_at is None or i < target_at:
                        values.append(bytes(6))  # boundary rejection
                    elif i == target_at:
                        values.append((8 * width + k).to_bytes(2, "little") + top.to_bytes(4, "little"))
                    else:
                        values.append((8 * width).to_bytes(2, "little") + bytes(4))
                return b"".join(values)
        for implementation in (fast, slow):
            with patch.object(sampler.os, "urandom", ForcedTape()):
                result = implementation.sample(width, 1)
            assert result == [k if target_at is not None and suffix_accept else 0]
        for field in invariant_fields:
            assert fast.last_stats[field] == slow.last_stats[field], field
        expected_cap = int(target_at is None or (target_at == 4095 and not suffix_accept))
        assert fast.last_stats["cap_fallbacks"] == expected_cap
        if target_at is None or target_at == 4095:
            assert fast.last_stats["proposals"] == 4096
        controls.append({"target_at_zero_based_proposal": target_at,
                         "suffix_accept": suffix_accept,
                         "outputs_and_counters_equal": True,
                         "stats": dict(fast.last_stats)})
    invalid = 0
    for width, count in ((0, 1), (3, 1), (2 ** 60, 1), (True, 1), (1024, -1), (1024, True)):
        try:
            fast.sample(width, count)
        except ValueError:
            invalid += 1
        else:
            raise AssertionError("invalid input accepted")
    assert fast.sample(1024, 0) == []
    return {"all_passed": True, "public_tape_differential": differential,
            "forced_cap_suffix_controls": controls, "invalid_inputs_rejected": invalid}


def measure(implementation, width, count):
    values = implementation.sample(width, count)
    record = dict(implementation.last_stats)
    mean = sum(values) / count
    record.update({"mean_over_sigma": mean / width,
                   "mean_standard_errors": mean / math.sqrt(width * width / (2 * math.pi * count)),
                   "second_moment_over_sigma_squared": sum(x * x for x in values) / count / (width * width),
                   "all_within_support": all(abs(x) < 8 * width for x in values),
                   "raw_samples_persisted": 0})
    assert record["all_within_support"]
    assert abs(record["mean_standard_errors"]) < 8
    assert 0.15 < record["second_moment_over_sigma_squared"] < 0.17
    del values
    return record


def main():
    start = time.perf_counter()
    source_names = ("sampler.py", "reference.py", "proposal_screen.c", "benchmark.py", "__init__.py")
    before = {name: sha(HERE / name) for name in source_names}
    frozen_baseline = HERE.parent.parent / "ring_implementation/sampling"
    baseline_before = {name: sha(frozen_baseline / name) for name in ("sampler.py", "MANIFEST.json", "MEASUREMENTS.json")}
    fast = sampler.GaussianSampler()
    slow = sampler.reference.GaussianSampler()
    tests = verify(fast, slow)
    rows = []
    for width in (1024, 2 ** 25):
        slow_row = measure(slow, width, 1_000_000)
        fast_row = measure(fast, width, 1_000_000)
        rows.append({"sigma": width, "count": 1_000_000,
                     "baseline": slow_row, "native": fast_row,
                     "speedup": slow_row["seconds"] / fast_row["seconds"]})
    after = {name: sha(HERE / name) for name in source_names}
    baseline_after = {name: sha(frozen_baseline / name) for name in baseline_before}
    assert before == after and baseline_before == baseline_after
    result = {"claim_label": "EXECUTED", "all_passed": True,
              "command": "research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_implementation/.venv/bin/python -B research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_implementation_fast/sampling/benchmark.py",
              "completed_utc": time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime()),
              "source_sha256": after, "frozen_baseline_sha256": baseline_after,
              "sources_unchanged_during_run": True, "python": sys.version,
              "platform": platform.platform(), "tests": tests, "benchmarks": rows,
              "table_seconds": fast.table_seconds, "native_load_seconds": fast.native_load_seconds,
              "native_library_path": str(fast.library_path), "native_library_sha256": sha(fast.library_path),
              "native_build_command": fast.build_command,
              "sampled_random_benchmark_coefficients": 4_000_000,
              "raw_samples_persisted": 0, "search_queries": 0,
              "elapsed_seconds": time.perf_counter() - start,
              "qualification": "Single runs on a shared machine; source/math refinement is derived, differential tests finite, OS entropy computational security and variable-time side channels separate. Sampler timing is not whole-ring timing."}
    (HERE / "MEASUREMENTS.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    summary = {"all_passed": True, "benchmarks": [{"sigma": row["sigma"],
               "baseline_seconds": row["baseline"]["seconds"],
               "native_seconds": row["native"]["seconds"], "speedup": row["speedup"],
               "native_coefficients_per_second": row["native"]["coefficients_per_second"]} for row in rows],
               "seconds": result["elapsed_seconds"], "differential_cases": len(tests["public_tape_differential"]),
               "forced_controls": len(tests["forced_cap_suffix_controls"])}
    stdout = json.dumps(summary, sort_keys=True)
    (HERE / "RUN.log").write_text("[EXECUTED] " + result["command"] + "\n[EXECUTED] Exit code: 0\n" + stdout + "\n")
    print(stdout)


if __name__ == "__main__":
    main()
