"""[EXECUTED] One finite exhaustive classical transcript-programming model.

No cryptographic expansion, entropy sampling, keys, ciphertexts or estimator.
"""
from collections import Counter
import hashlib
from itertools import product
import json
from pathlib import Path
import time

HERE = Path(__file__).resolve().parent
RAW_BITS, LOW_BITS, Q, N, CHUNK_WORDS, CAP_CHUNKS = 3, 2, 3, 2, 2, 2
M = CHUNK_WORDS * CAP_CHUNKS
MASK = (1 << LOW_BITS) - 1


def output(table):
    values = [word & MASK for word in table if (word & MASK) < Q]
    return tuple(values[:N]) if len(values) >= N else None


def program(table, target, *, erase_high=False, erase_tail=False):
    accepted = [i for i, word in enumerate(table) if (word & MASK) < Q]
    if len(accepted) < N:
        return table, False
    result = list(table)
    for j, slot in enumerate(accepted[:N]):
        high = 0 if erase_high else table[slot] & ~MASK
        result[slot] = high | target[j]
    if erase_tail:
        for slot in range(accepted[N - 1] + 1, M):
            result[slot] = 0
    return tuple(result), True


def main():
    source_before = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    tables = list(product(range(1 << RAW_BITS), repeat=M))
    targets = list(product(range(Q), repeat=N))
    mixed = Counter()
    fixed = {u: Counter() for u in targets}
    abort_counts = Counter()
    bad_high, bad_tail = Counter(), Counter()
    trailing_whole_chunk_cases = 0
    successful_pairs = 0
    for table in tables:
        original_output = output(table)
        accepted = [i for i, word in enumerate(table) if (word & MASK) < Q]
        if original_output is not None and accepted[N - 1] < CHUNK_WORDS:
            trailing_whole_chunk_cases += 1
        for target in targets:
            result, success = program(table, target)
            mixed[result] += 1
            fixed[target][result] += 1
            if success:
                successful_pairs += 1
                assert output(result) == target
                first = set(accepted[:N])
                for i in range(M):
                    assert result[i] >> LOW_BITS == table[i] >> LOW_BITS
                    if i not in first:
                        assert result[i] == table[i]
            else:
                abort_counts[target] += 1
                assert result == table and original_output is None
            bad_high[program(table, target, erase_high=True)[0]] += 1
            bad_tail[program(table, target, erase_tail=True)[0]] += 1

    assert len(tables) == 4096 and len(targets) == 9
    assert set(mixed) == set(tables)
    assert all(mixed[t] == len(targets) for t in tables)
    assert set(abort_counts.values()) == {208}
    for target in targets:
        for table in tables:
            value = output(table)
            expected = 1 if value is None else (Q ** N if value == target else 0)
            assert fixed[target][table] == expected
    assert any(bad_high[t] != len(targets) for t in tables)
    assert any(bad_tail[t] != len(targets) for t in tables)
    assert trailing_whole_chunk_cases > 0

    actual_N, words, extra, word_bytes = 16384, 1024, 16, 37
    cap = (4 * actual_N + words - 1) // words + extra
    costs = {"N": actual_N, "candidate_bits": 289, "raw_word_bits": 296,
             "high_padding_bits": 7, "candidate_words_per_chunk": words,
             "cap_chunks": cap, "cap_candidate_words": cap * words,
             "full_cap_random_bytes_per_row": cap * words * word_bytes,
             "full_cap_random_bits_per_row": cap * words * word_bytes * 8,
             "lazy_expected_bytes_strict_upper_bound_per_row": (2 * actual_N + words) * word_bytes,
             "target_uniform_coefficients_supplied_externally": actual_N}
    source_after = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    assert source_before == source_after
    result = {"claim_label": "EXECUTED", "all_passed": True,
              "command": "python3 -B research/learn_infer_only/experiments/private_construction/public_setup_pq/ring_seed_security_successor/transcript_programming/check_kernel.py",
              "completed_utc": time.strftime("%Y-%m-%d %H:%M:%S UTC", time.gmtime()),
              "source_sha256": source_after, "source_unchanged": True,
              "model": {"raw_bits": RAW_BITS, "low_bits": LOW_BITS, "q": Q, "N": N,
                        "words_per_chunk": CHUNK_WORDS, "cap_chunks": CAP_CHUNKS},
              "enumerated_tables": len(tables), "uniform_targets": len(targets),
              "table_target_pairs": len(tables) * len(targets),
              "successful_pairs": successful_pairs,
              "mixed_preimages_per_table": len(targets),
              "abort_tables_per_target": 208, "abort_probability_exact": "13/256",
              "fixed_target_success_density_multiplier": Q ** N,
              "fixed_target_abort_density_multiplier": 1,
              "fixed_target_wrong_output_density_multiplier": 0,
              "tables_with_unused_whole_final_chunk": trailing_whole_chunk_cases,
              "zero_high_bits_control_refuted": True,
              "zero_unused_tail_control_refuted": True,
              "derived_actual_expander_costs": costs,
              "actual_crypto_executions": 0, "private_artifact_reads": 0,
              "search_queries": 0, "scope": "One exact finite transcript model and integer cost arithmetic; general classical proof in KERNEL.md; no QROM claim."}
    (HERE / "CHECKS.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    stdout = json.dumps({"all_passed": True, "table_target_pairs": result["table_target_pairs"],
                         "mixed_preimages_per_table": len(targets),
                         "abort_probability_exact": "13/256", "actual_costs": costs}, sort_keys=True)
    (HERE / "RUN.log").write_text("[EXECUTED] " + result["command"] + "\n[EXECUTED] Exit code: 0\n" + stdout + "\n")
    print(stdout)


if __name__ == "__main__":
    main()
