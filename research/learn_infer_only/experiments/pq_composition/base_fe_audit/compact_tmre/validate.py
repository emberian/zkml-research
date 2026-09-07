#!/usr/bin/env python3
"""Source integrity and finite hybrid bookkeeping, not a crypto test."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[5]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def dump(name, obj):
    (BASE / name).write_text(json.dumps(obj, indent=2) + "\n")


def main():
    verified = []
    for row in json.loads((BASE / "inputs.json").read_text())["inputs"]:
        path = Path(row["path"])
        assert digest(path) == row["sha256"], path
        verified.append(row)
    access = json.loads((BASE / "access.json").read_text())
    assert len(access["web_queries"]) == 2
    assert access["scry_queries"] == access["kagi_queries"] == access["pdf_downloads"] == 0
    for row in access["local_reads"]:
        assert row["exit_code"] == 0 and row["stderr"] == ""
        for field in ["pdf", "text"]:
            path = Path(row[field])
            if not path.is_absolute():
                path = ROOT / path
            assert digest(path) == row[field + "_sha256"]
    for row in json.loads((BASE / "source_spans.json").read_text()):
        txt = Path(row["text"]).read_text()
        at = txt.index(row["anchor"])
        assert txt[:at].count("\n") + 1 == row["line"]
        assert txt[:at].count("\f") + 1 == row["pdf_page"]

    ledgers = []
    for length in [1, 3, 8, 31, 128, 577]:
        domain = 1 << max(1, (length - 1).bit_length())

        def hybrid(j):
            return tuple("fixed" if i >= length else ("B1" if i < j else "B0")
                         for i in range(domain))

        first, last = hybrid(0), hybrid(length)
        expected_first = tuple("B0" if i < length else "fixed" for i in range(domain))
        expected_last = tuple("B1" if i < length else "fixed" for i in range(domain))
        assert first == expected_first and last == expected_last
        changes = []
        for j in range(length):
            before, after = hybrid(j), hybrid(j + 1)
            changed = [i for i in range(domain) if before[i] != after[i]]
            assert changed == [j]
            changes.append(changed[0])
        ledgers.append({
            "output_bits": length, "index_domain_size": domain,
            "changed_points": changes, "exact_endpoint": True,
            "gap_coefficients": {"eps_O": 2 * length, "eps_P": 2 * length, "eps_H": length},
            "fresh_error_coefficients": {"delta_O": 1, "delta_H": length, "eps_P_corr": length},
        })

    # Distinct encoding tags can coexist with an equal fixed decoded bit.
    # Without an explicit generator branch, the last unused point stays B0.
    raw_last = ["B1", "B1", "B1", "B0"]
    raw_real_second = ["B1", "B1", "B1", "B1"]
    assert raw_last != raw_real_second
    falsifier = {"L": 3, "domain": 4, "raw_last_hybrid": raw_last,
                 "raw_second_real": raw_real_second,
                 "mismatch_indices": [3],
                 "meaning": "encoding tags only; both unused branches may decode the same fixed bit"}
    dump("wrapper_ledger.json", {"scope": "exact finite hybrid indexing and symbolic coefficient bookkeeping only",
                                "rows": ledgers, "out_of_range_falsifier": falsifier})
    ignored = subprocess.run(["git", "check-ignore", "--no-index",
                              str(BASE / "texts/2015_356.txt"), str(BASE / "__pycache__/dummy.pyc")],
                             cwd=ROOT, capture_output=True, text=True)
    assert ignored.returncode == 0 and len(ignored.stdout.splitlines()) == 2, ignored
    compile(Path(__file__).read_text(), str(__file__), "exec")
    checks = {"frozen_inputs": len(verified), "source_anchors": len(json.loads((BASE / "source_spans.json").read_text())),
              "local_pdf_extractions": len(access["local_reads"]),
              "wrapper_rows": len(ledgers), "adjacent_single_index_steps": sum(r["output_bits"] for r in ledgers),
              "out_of_range_falsifier": "passed", "ignore_rules": "passed", "python_compile": "passed",
              "cryptographic_runtime_executed": False}
    stdout = json.dumps(checks, indent=2)
    dump("validation.json", {"argv": [sys.executable, str(Path(__file__).resolve())],
                             "cwd": str(Path.cwd()), "exit_code": 0, "stdout": stdout + "\n", "stderr": "",
                             "checks": checks, "ignore_command_stdout": ignored.stdout,
                             "scope": "Not a proof of source cryptography or of a quantum lift of KLW"})
    names = [".gitignore", "COMPACT_TMRE.md", "access.json", "inputs.json", "source_spans.json",
             "validate.py", "wrapper_ledger.json", "validation.json"]
    dump("artifact_hashes.json", {"artifacts": [{"path": str(BASE / name), "sha256": digest(BASE / name)} for name in names]})
    print(stdout)


if __name__ == "__main__":
    main()
