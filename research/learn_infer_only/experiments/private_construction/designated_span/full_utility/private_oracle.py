#!/usr/bin/env python3
"""Private post-protocol utility comparison; emit counts/booleans, never scores."""
from pathlib import Path
import argparse
import json
import sqlite3
import sys

HERE = Path(__file__).resolve().parent
sys.dont_write_bytecode = True


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--runtime", required=True, type=Path)
    parser.add_argument("--out", required=True, type=Path)
    args = parser.parse_args()
    runtime = args.runtime.resolve()
    sys.path.insert(0, str(HERE / "journal"))
    from common import read_json, write_json, require
    events = read_json(runtime / ".private_fixture/input_index.json")["events"]
    expected = read_json(runtime / ".private_fixture/expected_scalars.json")["queries"]
    totals = {"all_correct": 0, "all_total": 0, "nonempty_correct": 0, "nonempty_total": 0,
              "final_correct": 0, "final_total": 0, "known_empty": 0}
    histories, event_results = [], []
    for history in (0, 1):
        selected = [e for e in events if e["event_id"].startswith(f"h{history}-")]
        require(len(selected) == 240, "frozenHistorySize")
        database = runtime / f"history_{history}/.private/reader/answers.sqlite3"
        with sqlite3.connect(database) as db:
            actual = {row[0]: json.loads(row[1]) for row in db.execute("SELECT request_id,answer FROM private_decodes")}
            require(db.execute("SELECT count(*),sum(decode_count) FROM private_decodes").fetchone() == (48, 48), "privateExactlyOnceCount")
        queues = {0: [], 1: []}
        nquery = nlearn = expiry = 0
        phase_tallies = {}
        for ordinal, event in enumerate(selected, 1):
            route = event["route"]
            if event["kind"] == "Learn":
                x = read_json(event["issuer_vector_path"])
                require(len(x) == 577 and all(type(v) is int and -127 <= v <= 127 for v in x), "frozenVectorRange")
                queues[route].append(x)
                if len(queues[route]) > 32:
                    queues[route].pop(0)
                    expiry += 1
                nlearn += 1
                continue
            query = read_json(event["public_query_vector_path"])
            # Independent exact integer reconstruction; no crypto module imported.
            coordinates = [sum(x[j] for x in queues[route]) for j in range(577)]
            score = sum(a * b for a, b in zip(coordinates, query, strict=True))
            row = expected[event["event_id"]]
            received = actual[event["event_id"]]
            require(received["signed_score"] == score == row["expected_scalar"], "receivedDirectAndFrozenIntegerEquality")
            sign = 1 if score >= 0 else -1  # Original utility tie rule, not mathematical signum.
            correct = sign == row["target_label"]
            require(sign == row["sign"] and correct == row["correct"], "sameOriginalUtilityOutcome")
            empty = len(queues[route]) == 0
            require(empty == row["public_structural_zero"], "sameStructuralEmptyControl")
            phase = (ordinal - 1) // 80 + 1
            key = f"phase_{phase}_route_{route}"
            tally = phase_tallies.setdefault(key, {"queries": 0, "correct": 0, "known_empty": 0})
            tally["queries"] += 1
            tally["correct"] += int(correct)
            tally["known_empty"] += int(empty)
            totals["all_total"] += 1
            totals["all_correct"] += int(correct)
            totals["known_empty"] += int(empty)
            if not empty:
                totals["nonempty_total"] += 1
                totals["nonempty_correct"] += int(correct)
            if phase == 3:
                totals["final_total"] += 1
                totals["final_correct"] += int(correct)
            nquery += 1
            event_results.append({"event_id": event["event_id"], "history": history, "route": route, "phase": phase,
                                  "direct_and_frozen_integer_match": True, "original_utility_correct": correct,
                                  "public_structural_zero": empty})
        require(nlearn == 192 and nquery == 48 and expiry == 128, "completePrivateOracleHistory")
        require(set(actual) == {e["event_id"] for e in selected if e["kind"] == "Infer"}, "exactSelectedOutputSet")
        histories.append({"history": history, "integer_matches": 48, "learns": 192, "infers": 48, "expiries": 128,
                          "phase_route_counts": phase_tallies})
    require(totals == {"all_correct": 52, "all_total": 96, "nonempty_correct": 44, "nonempty_total": 80,
                       "final_correct": 18, "final_total": 32, "known_empty": 16}, "unchangedOriginalUtilityDenominators")
    result = {"ok": True, "all_96_direct_and_frozen_integer_matches": True, "private_output_count": 96,
              "histories": histories, "utility_counts": totals, "event_outcomes": event_results,
              "original_errors_retained": 44, "private_values_and_decode_timings_omitted": True,
              "scope": "post-protocol trusted comparison of the complete existing public fixture; no new model or utility estimate"}
    write_json(args.out, result, True)
    print(json.dumps({"ok": True, "integer_matches": 96, "original_utility_counts_unchanged": True}))


if __name__ == "__main__":
    main()
