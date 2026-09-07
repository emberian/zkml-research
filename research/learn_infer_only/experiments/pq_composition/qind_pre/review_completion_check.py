#!/usr/bin/env python3
"""Check review provenance and replay existing finite controls without rewriting them."""

import hashlib
import json
from pathlib import Path
import re
import runpy
import sys

HERE = Path(__file__).resolve().parent
REVIEW = HERE.parents[1] / "adversarial_review" / "qind_pre"
EXPECTED = "78b5140be6fd2b2cd7d15706eabad4ee2da476b437ef310f1feb77ec5d3dbd66"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    frozen = HERE / "QIND_PRE_LIFT.pre-closeout.md"
    current = HERE / "QIND_PRE_LIFT.md"
    assert sha(frozen) == EXPECTED
    prefix, body = current.read_bytes().split(b"\n\n", 1)
    assert prefix.startswith(b"[OPEN closeout]")
    assert body == frozen.read_bytes(), "current body differs from reviewed bytes"
    controls_path = REVIEW / "controls.py"
    saved = json.loads((REVIEW / "results.json").read_text())
    assert saved["reviewed_target"]["sha256"] == EXPECTED
    assert saved["script_sha256"] == sha(controls_path)
    assert sha(Path(saved["primary_source"]["path"])) == saved["primary_source"]["sha256"]
    assert json.loads((REVIEW / "stdout.txt").read_text()) == saved

    # Importing with runpy's default name does not execute controls.main(), whose
    # current-file pin correctly rejects the later closeout wrapper. Invoke only
    # the pure finite control functions; preserve every reviewer-owned artifact.
    controls = runpy.run_path(str(controls_path))
    names = {
        "qualified_QIO": "qualified_gap_control",
        "joint_quantum_advice": "joint_quantum_advice_control",
        "delayed_signature": "delayed_signature_control",
        "bad_history": "bad_history_control",
    }
    replay = {key: controls[function]() for key, function in names.items()}
    for key, value in replay.items():
        assert value == saved[key], key
    completion = HERE / "REVIEW_COMPLETION.md"
    links = re.findall(r"\]\(([^)]+)\)", completion.read_text())
    for link in links:
        assert (HERE / link).is_file(), link
    result = {
        "label": "EXECUTED",
        "role": "author-side provenance verification and replay; not a second independent review",
        "frozen_sha256": sha(frozen),
        "current_sha256": sha(current),
        "current_difference": "one OPEN closeout paragraph; remainder byte-identical to reviewed target",
        "completion_note_sha256": sha(completion),
        "completion_local_links_checked": len(links),
        "reviewer_controls_sha256": sha(controls_path),
        "reviewer_results_sha256": sha(REVIEW / "results.json"),
        "reviewer_stdout_matches_results": True,
        "reviewer_primary_pdf_hash_matches": True,
        "pure_control_groups_replayed": list(names),
        "replay_matches_saved_results": True,
        "qualified_rational_cases": replay["qualified_QIO"]["exact_rational_cases"],
        "frozen_note_and_reviewer_artifacts_written": False,
        "queries": {"SQL": 0, "schema": 0, "web": 0, "Kagi": 0},
        "network_pdf_downloads": 0,
        "script_sha256": sha(Path(__file__)),
        "python": sys.version,
    }
    (HERE / "review_completion_check.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
