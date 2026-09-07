"""Read-only public CSV/error-table and final frozen-manifest review."""
from pathlib import Path
import csv
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1] / "end_to_end/utility/semantic_axis_successor"
PRIOR = ROOT.parent / "semantic_axis_selection"


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text())


def inventory(root):
    manifest = load(root / "manifest.json")
    files = []
    for name, spec in sorted(manifest["files"].items()):
        path = root / name
        assert sha(path) == spec["sha256"], name
        assert path.stat().st_size == spec["bytes"], name
        files.append({"path": name, **spec})
    return {"root": str(root), "manifest_sha256": sha(root / "manifest.json"),
            "file_count": len(files), "total_bytes": sum(x["bytes"] for x in files),
            "all_declared_files_match": True, "files": files}


records = {r["id"]: r for r in load(ROOT / "records.json")}
oracle = {r["record_id"]: r for r in load(ROOT / "test_oracle.json")}
predictions = {r["record_id"]: r for r in load(ROOT / "test_predictions.json")}
raw = {(r["record_id"], r["axis"]): r for r in load(ROOT / "raw_scores.json")}
with (ROOT / "test_decisions.csv").open(newline="") as f:
    rows = list(csv.DictReader(f))
assert [int(r["record_id"]) for r in rows] == list(range(256, 384))
errors = []
for row in rows:
    i = int(row["record_id"])
    r, o, p = records[i], oracle[i], predictions[i]
    assert row["task"] == o["task"] == ("plant", "letter")[r["skill"]]
    assert int(row["template"]) == r["template"]
    assert row["entity"] == r["entity"] and row["text"] == r["text"]
    for axis in ("a", "b"):
        x = raw[i, axis]
        assert int(row["gold_" + axis]) == o[axis] == r[axis]
        bit = int(x["logits_in_bit_order"][0] < x["logits_in_bit_order"][1])
        assert int(row["predicted_" + axis]) == p[axis] == x["predicted_bit"] == bit
    correct = p["a"] == o["a"] and p["b"] == o["b"]
    assert int(row["both_correct"]) == int(correct)
    if not correct:
        errors.append(i)

md_rows = []
for line in (ROOT / "ERRORS.md").read_text().splitlines():
    if re.match(r"^\| \d+ \|", line):
        cells = [s.strip() for s in line.split("|")[1:-1]]
        i = int(cells[0])
        assert json.loads(cells[1]) == [oracle[i]["a"], oracle[i]["b"]]
        assert [float(cells[2]), float(cells[3])] == raw[i, "b"]["logits_in_bit_order"]
        assert cells[4] == records[i]["text"]
        assert oracle[i]["b"] == 0 and predictions[i]["b"] == 1
        assert oracle[i]["a"] == predictions[i]["a"]
        assert records[i]["template"] == 0
        md_rows.append(i)
assert md_rows == errors and len(errors) == 15

out = {"schema": "semantic-successor-final-provenance-review-v1", "passed": True,
       "script_sha256": sha(Path(__file__)), "target": inventory(ROOT),
       "prior_selection": inventory(PRIOR), "csv_rows_checked": len(rows),
       "all_error_rows_text_pair_logits_checked": len(md_rows), "error_ids": errors,
       "model_calls": 0, "crypto_calls": 0,
       "scope": "Final source and retained public-data hashes; CSV/error-table agreement only."}
(HERE / "provenance_details.json").write_text(json.dumps(out, indent=2) + "\n")
print(json.dumps({k: v for k, v in out.items() if k not in {"target", "prior_selection"}}, indent=2))
