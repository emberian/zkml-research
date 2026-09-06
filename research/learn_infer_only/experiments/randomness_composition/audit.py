#!/usr/bin/env python3
"""Exact finite selection experiments. Ideal coins and receipts; no encryption.

All distributions enumerate their complete sample space with Fraction arithmetic.
Failure controls intentionally attack stronger claims, not the modeled primitive.
"""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import product
from pathlib import Path
import json
import platform
import subprocess
import sys

HERE = Path(__file__).resolve().parent


def ratio(n, d):
    return None if d == 0 else str(Fraction(n, d))


def distribution(worlds, run):
    worlds = list(worlds)
    counts = Counter(run(w) for w in worlds)
    n = len(worlds)
    delivered = n - counts[None]
    return {
        "worlds": n,
        "counts": {str(k): v for k, v in sorted(counts.items(), key=lambda kv: str(kv[0]))},
        "release_probability": ratio(delivered, n),
        "one_probability": ratio(counts[1], n),
        "one_given_release": ratio(counts[1], delivered),
    }


def randomness_attacks():
    result = {}
    result["bound_but_host_chosen_seed"] = distribution(range(2), lambda _: 1)
    result["one_coin_per_reserved_transition_all_counted"] = distribution(range(2), lambda r: r)
    result["same_reserved_coin_repeated_8_times"] = distribution(range(2), lambda r: max([r] * 8))
    result["reserve_before_draw_but_host_filters_delivery"] = distribution(range(2), lambda r: 1 if r else None)
    result["blind_precommit_with_independent_availability"] = distribution(product(range(2), repeat=2), lambda rh: rh[0] if rh[1] else None)
    for k in (1, 2, 4, 8):
        worlds = list(product(range(2), repeat=k))
        result[f"fresh_retries_{k}_forced_result"] = distribution(worlds, lambda rs: int(any(rs)))
        result[f"unique_coins_across_{k}_contexts_selected_after_view"] = distribution(worlds, lambda rs: int(any(rs)))
        result[f"fresh_retries_{k}_only_favorable_release"] = distribution(worlds, lambda rs: 1 if any(rs) else None)
        expected = str(1 - Fraction(1, 2**k))
        assert result[f"fresh_retries_{k}_forced_result"]["one_probability"] == expected
        assert result[f"unique_coins_across_{k}_contexts_selected_after_view"]["one_probability"] == expected
        assert result[f"fresh_retries_{k}_only_favorable_release"]["one_given_release"] == "1"
    assert result["one_coin_per_reserved_transition_all_counted"]["one_probability"] == "1/2"
    assert result["same_reserved_coin_repeated_8_times"]["one_probability"] == "1/2"
    assert result["reserve_before_draw_but_host_filters_delivery"]["one_given_release"] == "1"
    assert result["blind_precommit_with_independent_availability"]["one_given_release"] == "1/2"
    return result


def all_selection_policies():
    # Coin r is independent of prior host history h; both are unbiased bits.
    worlds = list(product(range(2), repeat=2))
    hidden_rows = []
    for policy in product(range(2), repeat=2):
        row = distribution(worlds, lambda rh: rh[0] if policy[rh[1]] else None)
        row["policy_by_history"] = list(policy)
        if row["release_probability"] != "0":
            assert row["one_given_release"] == "1/2"
        hidden_rows.append(row)
    exposed_rows = []
    for policy in product(range(2), repeat=4):
        row = distribution(worlds, lambda rh: rh[0] if policy[2 * rh[0] + rh[1]] else None)
        row["policy_by_coin_and_history"] = list(policy)
        exposed_rows.append(row)
    # A one-bit metadata channel reports r correctly for 3 of 4 noise values.
    noisy_worlds = list(product(range(2), range(4)))
    noisy_rows = []
    for policy in product(range(2), repeat=2):
        def run(rn):
            r, noise = rn
            leak = r ^ int(noise == 0)
            return r if policy[leak] else None
        row = distribution(noisy_worlds, run)
        row["policy_by_noisy_leak"] = list(policy)
        noisy_rows.append(row)
    assert max(Fraction(x["one_given_release"]) for x in noisy_rows if x["one_given_release"] is not None) == Fraction(3, 4)
    return {
        "all_four_coin_blind_policies": hidden_rows,
        "all_sixteen_coin_aware_policies": exposed_rows,
        "all_four_noisy_leak_policies": noisy_rows,
        "coin_aware_nonempty_biased_policy_count": sum(x["one_given_release"] not in (None, "1/2") for x in exposed_rows),
    }


def rfe_ideal_cache():
    # The same semantic plaintext x may have four valid distinct ciphertext encodings.
    worlds = list(product(range(2), repeat=4))
    traces = []
    for bits in worlds:
        cache = {}
        def dec(key_index, ciphertext_encoding):
            address = (key_index, ciphertext_encoding)
            if address not in cache:
                cache[address] = bits[ciphertext_encoding]
            return cache[address]
        first = dec(0, 0)
        repeat = dec(0, 0)
        assert first == repeat
        answers = [dec(0, c) for c in range(4)]
        traces.append({"ideal_coins": list(bits), "same_tuple_repeats": [first, repeat], "same_plaintext_distinct_encodings": answers, "selected_output": max(answers)})
    return {
        "game_model": "Def.4.5: cache by stored key index and exact ciphertext tuple",
        "same_ciphertext_repeated": distribution(worlds, lambda bits: max([bits[0]] * 4)),
        "same_plaintext_four_distinct_ciphertexts": distribution(worlds, lambda bits: max(bits)),
        "traces": traces,
    }


def fixed_and_adaptive_contexts():
    # This is a toy false-accepting gate, not Stage-0 or an attack on its theorem.
    # Each context c has an independent uniformly random answer in {0,1,2,3}.
    # A false receipt in context c passes exactly when H(c)=0.
    n = 4
    worlds = list(product(range(4), repeat=n))
    fixed = [sum(w[c] == 0 for w in worlds) for c in range(n)]
    assert fixed == [len(worlds) // 4] * n
    rows = []
    for q in range(n):
        successes = 0
        transcripts = []
        for w in worlds:
            queried = list(range(q))
            selected = next((c for c in queried if w[c] == 0), q)
            accepts = w[selected] == 0
            successes += accepts
            transcripts.append({"oracle": list(w), "queried": queried, "selected": selected, "accepts_false": accepts})
        expected = 1 - Fraction(3, 4)**(q + 1)
        assert Fraction(successes, len(worlds)) == expected
        assert expected <= Fraction(q + 1, 4)
        rows.append({"preverification_queries": q, "verification_unqueried_address_budget": 1,
                     "finalized_context_count": 1, "false_accept_probability": str(expected),
                     "all_opportunities_union_bound": str(Fraction(q + 1, 4)),
                     "wrong_bound_counting_only_finalized_contexts": "1/4",
                     "transcripts": transcripts})
    # Pointwise fixed-context bounds cannot be retained under correlated selection.
    diagonal = {"worlds": 2, "each_fixed_context_probability": "1/2",
                "bad_event": "bad(c,w) iff c=w", "adaptive_selector": "c=w",
                "selected_bad_probability": "1", "two_context_union_bound": "1"}
    # Exhaust every four-history selector chosen independently of a NEW coin.
    # Each context succeeds on exactly one of four fresh values, even if selected
    # context is a function of arbitrarily correlated earlier transcript/history.
    positive = []
    for select in product(range(4), repeat=4):
        successes = sum(r == select[h] for h in range(4) for r in range(4))
        assert successes == 4
        positive.append(list(select))
    return {"oracle_worlds": len(worlds), "fixed_context_counts": fixed,
            "query_selection": rows, "diagonal_counterexample": diagonal,
            "fresh_after_selection_positive": {"all_selectors_checked": len(positive), "worlds_per_selector": 16,
                                               "bad_probability_every_selector": "1/4"}}


def irreversible_reservation():
    traces = []
    for r in range(2):
        authority = {"parent": "p0", "reserved": None, "durable_result": None}
        def reserve(command):
            if authority["reserved"] is not None:
                return False
            authority["reserved"] = command
            return True
        assert reserve("infer-to-authorized-recipient")
        reservation = dict(authority)
        assert not reserve("alternate-command")
        # Drawing now does not make the result available. This model separately
        # assumes the completion worker can finish independent of the host.
        authority["durable_result"] = r
        saved_host_manifest = {"parent": "p0"}
        del saved_host_manifest
        assert not reserve("infer-to-authorized-recipient")
        host_delivers = bool(r)
        # Authorized recipient can retrieve the already durable result even if
        # host refuses its own transport. This is an added availability resource.
        recipient_retrieves = authority["durable_result"]
        traces.append({"coin": r, "reservation_before_coin": reservation,
                       "host_delivers": host_delivers, "recipient_retrieves": recipient_retrieves,
                       "retry_resamples": False, "authority": authority})
    return {"traces": traces,
            "host_transport": distribution(range(2), lambda r: r if r else None),
            "independent_completion_and_retrieval": distribution(range(2), lambda r: r)}


def finalization_cache_boundary():
    # Each toy receipt uses one final verifier query. This exposes why several
    # independent single-output games are not automatically one shared ROM.
    worlds = list(product(range(2), repeat=2))
    same_address_real = [(w[0], w[0]) for w in worlds]
    same_address_resampled = [(w[0], w[1]) for w in worlds]
    distinct_addresses_real = [(w[0], w[1]) for w in worlds]
    distinct_addresses_shared_position = [(w[0], w[0]) for w in worlds]
    def disagreement(rows):
        return ratio(sum(a != b for a, b in rows), len(rows))
    assert disagreement(same_address_real) == "0"
    assert disagreement(same_address_resampled) == "1/2"
    assert disagreement(distinct_addresses_real) == "1/2"
    assert disagreement(distinct_addresses_shared_position) == "0"
    trials = []
    for m in range(1, 5):
        tables = list(product(range(4), repeat=m))
        accepts = sum(any(x == 0 for x in table) for table in tables)
        probability = Fraction(accepts, len(tables))
        assert probability == 1 - Fraction(3, 4)**m
        trials.append({"preverification_queries": 0, "new_verification_queries": m,
                       "total_charged_queries_after_verification": m,
                       "receipts": m, "any_false_accept_probability": str(probability)})
    return {"same_address_shared_cache_disagreement": disagreement(same_address_real),
            "same_address_independent_final_coins_disagreement": disagreement(same_address_resampled),
            "distinct_addresses_shared_rom_disagreement": disagreement(distinct_addresses_real),
            "distinct_addresses_shared_fallback_position_disagreement": disagreement(distinct_addresses_shared_position),
            "unqueried_many_receipts_need_verifier_query_charge": trials}


def main():
    result = {"scope": "Exhaustive finite ideal-functionality and probability experiments; no cryptography or neural model",
              "command": [sys.executable, str(Path(__file__).resolve())], "python": platform.python_version(),
              "script_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
              "randomness": randomness_attacks(), "selection_policies": all_selection_policies(),
              "rfe_ideal": rfe_ideal_cache(), "receipt_composition": fixed_and_adaptive_contexts(),
              "reservation": irreversible_reservation(), "finalization_cache": finalization_cache_boundary()}
    output = HERE / "results.json"
    output.write_text(json.dumps(result, indent=2) + "\n")
    summary = {"status": "all assertions passed", "results": str(output),
               "unique_8_contexts_bias": result["randomness"]["unique_coins_across_8_contexts_selected_after_view"],
               "rfe_four_encodings": result["rfe_ideal"]["same_plaintext_four_distinct_ciphertexts"],
               "three_queries_one_final_context": {k: v for k, v in result["receipt_composition"]["query_selection"][3].items() if k != "transcripts"},
               "fresh_after_selection": result["receipt_composition"]["fresh_after_selection_positive"]}
    print(json.dumps(summary, indent=2))


if __name__ == "__main__":
    main()
