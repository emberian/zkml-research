#!/usr/bin/env python3
"""Independent finite parameter/distribution checks; no cryptography or recovery.

The author module is imported with bytecode disabled and only its pure functions
are called. Its main(), which writes author-owned files, is never called.
"""
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import importlib.util
import json
import platform
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
TASK = HERE.parents[2]
AUTHOR = TASK / "experiments/private_ingress/provenance_review"
PDF = Path("/Users/ember/dev/gh/forks/IACR-eprint-mirror/2025/330.pdf")


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def positive_compositions(total, length):
    if length == 1:
        yield (total,)
        return
    for first in range(1, total - length + 2):
        for rest in positive_compositions(total - first, length - 1):
            yield (first,) + rest


def collision_checks():
    checked = 0
    # Exhaust all positive dyadic histograms in this bounded support family.
    # The unused output symbols include a nonempty, disjoint right support.
    for width in range(1, 5):
        alphabet = 2**width
        for tape_bits in range(5):
            samples = 2**tape_bits
            for support in range(1, min(alphabet - 1, samples, 4) + 1):
                for histogram in positive_compositions(samples, support):
                    collision = sum((Fraction(c, samples)**2 for c in histogram), Fraction())
                    assert collision >= Fraction(1, support)
                    assert collision >= Fraction(1, alphabet - 1) > Fraction(1, alphabet)
                    checked += 1
    boundary = []
    for exponent in range(1, 6):
        # h=E can attain gap exactly epsilon in a larger separating alphabet.
        left = [Fraction(1, 2**exponent)] * (2**exponent)
        collision = sum((p*p for p in left), Fraction())
        assert collision == Fraction(1, 2**exponent)
        boundary.append({"effective_seed_bits": exponent,
                         "projection_width": exponent + 1,
                         "fixed_atom_and_collision_gap": str(collision)})
    # Failed-premise sibling: identical (overlapping) supports have zero gap.
    law = [Fraction(1, 4), Fraction(3, 4)]
    left_collision = sum((p*p for p in law), Fraction())
    right_against_left_sample = sum((p*q for p, q in zip(law, law)), Fraction())
    assert left_collision == right_against_left_sample == Fraction(5, 8)
    return {"positive_dyadic_histograms_checked": checked,
            "strict_width_bound": "gap >= 1/(2^L-1) > 2^-L when both supports are nonempty and disjoint",
            "equality_L_E": "incompatible with exact gap <= 2^-E",
            "equality_h_E_positive_boundary": boundary,
            "overlap_failed_premise_gap": str(left_collision - right_against_left_sample)}


def seed_checks():
    checked = 0
    # Arbitrary deterministic maps of short uniform seeds, including collisions.
    # Repeat patterns of output labels to model deterministic expansion only.
    for bits in range(7):
        for modulus in range(1, 10):
            values = [tuple([seed % modulus] * 128) for seed in range(2**bits)]
            fixed_mass = Fraction(values.count(values[0]), len(values))
            assert fixed_mass >= Fraction(1, 2**bits)
            checked += 1
    return {"deterministic_seed_maps_checked": checked,
            "claim": "deterministic expansion cannot reduce the fixed-seed output atom below 2^-h"}


def sizing_checks():
    count = 0
    for base in (2, 3, 4, 8, 16, 32):
        message = 16 * base**3
        metadata = 4*base**3 + 4*base + 2*base**2 + 32
        assert metadata < message
        current = base
        additive = 8*message + 2*base + 1
        for layer in range(9):
            closed = 18**layer * base + additive * ((18**layer - 1)//17)
            assert current == closed
            s = 2*current + message
            exponent = 4*s + current
            next_parameter = 18*current + additive
            assert next_parameter == 2*exponent + 2*base + 1
            next_s = 2*next_parameter + message
            fresh_coins = base + 2*next_parameter + base**3
            assert min(next_s, fresh_coins, base + next_parameter) > exponent
            current = next_parameter
            count += 1
    return {"layer_inequality_cases": count,
            "closed_form": "lambda_i = 18^i*k + (8*M+2*k+1)*(18^i-1)/17, M=16*k^3",
            "scope": "dimension model only; fixed i gives degree 3 in k; no primitive implementation or entropy realization",
            "metadata_domain": "k >= 2 in checked family; no k=1 claim"}


def rate_checks():
    witnesses = []
    for degree in range(1, 17):
        # lambda=2^m, t=lambda^d. This picks an explicit sufficiently large m.
        m = max(64, 4*degree)
        assert (degree*m)**2 < 2**m
        witnesses.append({"degree": degree, "log2_lambda": m,
                          "log2_inverse_negligible_rate": (degree*m)**2,
                          "lower_bound_E": 2**m})
    numeric = []
    for E in (128, 1024, 262288, 4983625):
        t = (2*E)**2
        ceil_log2 = (t-1).bit_length()
        conservative_exponent = 2*E - 3*ceil_log2
        assert conservative_exponent >= E
        numeric.append({"E": E, "t": t, "conservative_exponent": conservative_exponent})
    return {"slow_negligible_examples": witnesses,
            "hypothetical_subexponential_rate_examples": numeric,
            "scope": "arithmetic controls; no cryptographic upper bound supplied"}


def check_sources():
    pins = json.loads((AUTHOR / "parameter_hashes.json").read_text())
    checked = []
    for item in pins["files"]:
        path = Path(item["path"])
        actual = digest(path)
        assert actual == item["sha256"], path
        checked.append({"path": str(path), "sha256": actual})
    source = json.loads((AUTHOR / "parameter_sources.json").read_text())["source"]
    assert digest(PDF) == source["pdf_sha256"]
    retained = Path(source["retained_extract_path"])
    fresh = HERE / "extracts/2025-330.txt"
    assert digest(fresh) == digest(retained) == source["extract_sha256"]
    pages = fresh.read_text().split("\f")
    anchors = {"Definition 4.1": 21, "Definition 4.3": 22,
               "Ciphertexts of length s on inputs": 48,
               "Theorem 6.1": 50, "Here s denotes the length of the PKE ciphertexts": 51,
               "Lemma 6.7": 65}
    for phrase, page in anchors.items():
        assert phrase in pages[page-1], (phrase, page)
    for page in (57, 58):
        assert "r∗ ← {0, 1}λ" in pages[page-1]
    extra_paths = [AUTHOR / "parameter_hashes.json", AUTHOR / "DUAL_MODE.md",
                   TASK / "experiments/private_ingress/provenance/PROVENANCE.md", PDF, retained]
    checked += [{"path": str(path), "sha256": digest(path)} for path in extra_paths]
    return checked, {"pdf_sha256": digest(PDF), "fresh_extract_sha256": digest(fresh),
                     "fresh_extract_equals_retained": True, "anchors_pdf_pages_1based": anchors}


def reproduce_pure_author_controls():
    spec = importlib.util.spec_from_file_location("frozen_parameter_audit", AUTHOR / "parameter_audit.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    saved = json.loads((AUTHOR / "parameter_results.json").read_text())
    fresh = {"short_seed_falsifier": module.seeded_support_control(),
             "collision_bound": module.collision_control(),
             "sizing_escape": module.sizing_family(16),
             "hypothetical_quantitative_sizing": module.sizing_family(16, True),
             "negligible_does_not_mean_exponentially_small": module.negligible_rate_control()}
    for key, value in fresh.items():
        assert value == saved[key], key
    return {"pure_function_result_groups_matching_saved_json": len(fresh),
            "author_main_called": False, "author_files_written": False}


def main():
    before, source = check_sources()
    result = {"classification": "EXECUTED independent finite analytic controls only",
              "command": f"python3 {Path(__file__).resolve()}",
              "python": platform.python_version(), "script_sha256": digest(Path(__file__)),
              "author_pure_reproduction": reproduce_pure_author_controls(),
              "independent_collision": collision_checks(), "independent_seed": seed_checks(),
              "independent_sizing": sizing_checks(), "independent_rates": rate_checks(),
              "source": source, "input_hashes_before": before}
    after, _ = check_sources()
    assert before == after
    result["input_hashes_after_equal_before"] = True
    result["accounting"] = {"Scry_queries": 0, "Kagi_queries": 0, "web_queries": 0,
                             "local_PDF_extractions": 1, "PDF_downloads": 0,
                             "state_recovery_or_extraction_experiments": 0}
    output = json.dumps(result, indent=2) + "\n"
    (HERE / "results.json").write_text(output)
    print(output, end="")


if __name__ == "__main__":
    main()
