#!/usr/bin/env python3
"""Finite controls for source-game premises. NO encryption or obfuscation."""
from __future__ import annotations

from collections import defaultdict
from fractions import Fraction
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
MIRROR = Path("/Users/ember/dev/gh/forks/IACR-eprint-mirror")


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit() -> dict:
    domain = 256
    known_unlock = 0
    independent_fixed_input_acceptances = 0
    conditional_targets = defaultdict(set)
    # f_shift is an ordinary public finite permutation. This is deliberately
    # not called encryption; the predictor argument uses only evaluation of f.
    for shift in range(domain):
        f = lambda x: (x + shift) % domain
        fixed_input = 17
        for target in range(domain):
            unlock_input = (target - shift) % domain
            predicted = f(unlock_input)
            assert predicted == target
            known_unlock += 1
            conditional_targets[(shift, unlock_input)].add(target)
            independent_fixed_input_acceptances += int(f(fixed_input) == target)
    assert known_unlock == 65536
    assert all(len(targets) == 1 for targets in conditional_targets.values())
    assert Fraction(independent_fixed_input_acceptances, known_unlock) == Fraction(1, 256)
    # Random padding inside the full function description is not secret advice
    # to the source-game predictor; it is literally part of that description.
    masked_predictors = 0
    for lock in range(domain):
        for approved_bit in (0, 1):
            function_description = {"lock": lock, "approved_bit": approved_bit}
            predicted = function_description["lock"]
            assert predicted == lock
            masked_predictors += 1
    # An entire retained future package matters: marginally uniform locks can
    # be fully predictable given a related released lock and public relation.
    joint_auxiliary_predictions = 0
    for first_lock in range(domain):
        for public_delta in range(16):
            second_lock = first_lock ^ public_delta
            auxiliary = (first_lock, public_delta)
            assert auxiliary[0] ^ auxiliary[1] == second_lock
            joint_auxiliary_predictions += 1
    # A single MBCC releases a fixed z on every accepting input. It cannot
    # realize two different accepted answers without a further construction.
    required_release = {"approved-zero-case": 0, "approved-one-case": 1}
    constant_message_failures = {}
    for message in (0, 1):
        failures = sum(message != output for output in required_release.values())
        assert failures == 1
        constant_message_failures[str(message)] = failures
    # Idealized binding control, not a proof-system implementation. It shows
    # that statement binding and the obfuscation's target entropy are distinct.
    unbound_recoveries = 0
    bound_routing_rejections = 0
    for state in range(domain):
        bits = [(state >> bit) & 1 for bit in range(8)]
        assert sum(value << bit for bit, value in enumerate(bits)) == state
        unbound_recoveries += 1
        for bit in range(8):
            proposed_program = ("extract-bit", bit)
            assert proposed_program != ("authorized-parity", None)
            bound_routing_rejections += 1
        output = state.bit_count() % 2
        # Target (valid=1, output=0/1) is public for each branch program.
        for branch in (0, 1):
            target = (1, branch)
            assert (1, branch) == target
            assert ((1, output) == target) == (output == branch)
    assert unbound_recoveries == 256 and bound_routing_rejections == 2048
    sources = []
    locations = {
        (2017, 276): {"title": "Obfuscating Compute-and-Compare Programs under LWE",
                      "access": "full local text; games, constructions 5.3/5.7, theorem statements/proofs 5.4/5.8 and applications inspected; core matrix reduction not reverified",
                      "pages": [2, 3, 9, 10, 12, 13, 14, 23, 24, 25, 26, 27, 29]},
        (2017, 274): {"title": "Lockable Obfuscation",
                      "access": "full local text; Def3.1-3.4, main construction syntax/parameters, one-sided PE application and Appendix D introduction inspected; matrix reduction not reverified",
                      "pages": [2, 3, 15, 16, 17, 18, 67]},
        (2019, 1010): {"title": "On Perfect Correctness in (Lockable) Obfuscation",
                       "access": "local September9,2019 version; abstract/introduction and §2.6 Def2.1-2.2 inspected; construction/reduction not audited",
                       "pages": [1, 2, 13, 14]}}
    for (year, identifier), metadata in locations.items():
        path = MIRROR / str(year) / f"{identifier}.pdf"
        extracted = HERE / "source" / f"{year}-{identifier}.txt"
        sources.append({"path": str(path), "url": f"https://eprint.iacr.org/{year}/{identifier}",
                        "pdf_sha256": digest(path), "extracted_text_sha256": digest(extracted),
                        **metadata})
    search_records = []
    for name in ("scry_discovery.json", "scry_refined.json"):
        record = json.loads((HERE / name).read_text())
        search_records.append({"file": name, "record_id": record["record_id"],
                               "rows": record["row_count"], "spend_nanodollars": record["spend_nanodollars"]})
    result = {"status": "PASS", "model": "finite source-premise controls, not encryption/obfuscation",
              "known_unlock_prediction_cases": known_unlock,
              "known_unlock_prediction_probability": "1",
              "max_target_support_given_full_function_and_unlock": max(map(len, conditional_targets.values())),
              "fixed_input_before_independent_lock_acceptance_probability": "1/256",
              "masked_function_description_predictors": masked_predictors,
              "joint_future_auxiliary_predictors": joint_auxiliary_predictions,
              "single_fixed_message_mismatches": constant_message_failures,
              "unbound_arbitrary_predicate_full_byte_recoveries": unbound_recoveries,
              "ideal_binding_predicate_substitution_rejections": bound_routing_rejections,
              "public_bit_branch_target_prediction_probability": "1",
              "source_manifest": sources, "script_sha256": digest(Path(__file__)),
              "searches_this_tranche": {"scry_sql": 2, "schema": 0, "web_search_queries": 2,
                                         "kagi": 0, "scry_records": search_records},
              "cumulative_lane_search_count": {"scry_sql": 10, "schema": 1, "web": 30, "kagi": 0}}
    (HERE / "results.json").write_text(json.dumps(result, indent=2) + "\n")
    return {key: value for key, value in result.items() if key not in ("source_manifest", "searches_this_tranche")}


if __name__ == "__main__":
    print(json.dumps(audit(), indent=2))
