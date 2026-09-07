#!/usr/bin/env python3
"""Small algebraic controls for the conditional transcript argument; no crypto game."""
import hashlib
import json
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
NOTE = HERE.parents[1] / "end_to_end" / "PRIVACY_SCOPE.md"


def dot(x, y):
    return sum(a * b for a, b in zip(x, y, strict=True))


def add(x, y):
    return tuple(a + b for a, b in zip(x, y, strict=True))


def main():
    e0 = (1, 0) + (0,) * 575
    e1 = (0, 1) + (0,) * 575
    zero = (0,) * 577
    permitted_q = add(e0, e1)
    assert e0 != e1
    assert dot(e0, permitted_q) == dot(e1, permitted_q) == 1
    assert dot(zero, permitted_q) == 0
    left = [e0, e1]
    right = [e1, e0]
    endpoint = [dot(add(*stream), e0) for stream in (left, right)]
    mixed = [dot(add(*stream), e0) for stream in ([e0, e0], [e1, e1])]
    assert endpoint == [1, 1] and mixed == [2, 0]
    substituted = [dot(v, e0) for v in (e0, e1)]
    assert substituted == [1, 0]
    result = {
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "classification": "EXECUTED finite integer controls, DERIVED conditional argument review",
        "source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "reviewed_note": str(NOTE),
        "reviewed_note_sha256": hashlib.sha256(NOTE.read_bytes()).hexdigest(),
        "width": 577,
        "all_fresh_coordinates_in_declared_range": all(-127 <= x <= 127 for v in (e0, e1) for x in v),
        "nonvacuity": {
            "distinct_private_vectors": True,
            "one_learn_then_fixed_sum_query_scores": [1, 1],
            "zero_state_score": 0,
            "scope": "Illustrative range-only issuance and one fixed query, not the actual feature-policy or a claim about all deployed query continuations."
        },
        "mixed_hybrid": {
            "public_schedule": ["Learn", "Learn", "Infer(first-coordinate)"],
            "endpoint_scores": endpoint,
            "one_ciphertext_switched_plaintext_scores": mixed,
            "simulated_reader_score_in_every_hybrid": 1,
            "scope": "A common efficient output simulator matches both endpoints despite mixed histories having different actual outputs; the reduction need not decrypt them."
        },
        "authority_substitution": {
            "authorized_sum_scores": [1, 1],
            "unauthorized_first_coordinate_scores": substituted,
            "scope": "Derived sensitivity at one valid release opportunity if a reader trusts a compromised finalizer's substituted ciphertext. No service/signature exploit is executed here; no unlimited authorization or read-all conclusion."
        },
        "encryption_instantiated": False,
        "formal_crypto_reduction": False,
        "adaptive_fresh_input_generator_established": False,
        "earlier_separate_disclosure_task_resumed": False,
        "passed": True,
    }
    out = HERE / "privacy_scope_review_001.json"
    out.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"record": str(out), "passed": True, "reviewed_note_sha256": result["reviewed_note_sha256"]}))


if __name__ == "__main__":
    main()
