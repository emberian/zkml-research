#!/usr/bin/env python3
"""Preserve as-run micro record; annotate later independent matrix refinements."""
from pathlib import Path
import hashlib
import json
HERE=Path(__file__).resolve().parent
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def main():
    current=HERE/"micro_results.json";archived=HERE/"micro_results.as_run.json"
    if not archived.exists():archived.write_bytes(current.read_bytes())
    original=json.loads(archived.read_text())
    assert original["script_sha256"]==sha(HERE/"micro.py")
    report=dict(original)
    report["linear_audit_sha256"]=sha(HERE/"linear_audit.py")
    report["linear_results_sha256"]=sha(HERE/"linear_results.json")
    report["metadata_revision"]={"script_sha256":sha(__file__),"as_run_record_sha256":sha(archived),
        "reason":"Independent matrix audit later added all561 basis checks and a shifted-fixture pair; same query matrix. Original micro record preserved; no crypto rerun.",
        "timing_or_crypto_result_changed":False}
    assert report["phases"]==original["phases"] and report["outputs"]==original["outputs"]
    current.write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"passed":True,"as_run_record_sha256":sha(archived),
        "annotated_record_sha256":sha(current),"crypto_measurements_unchanged":True},indent=2))
if __name__=="__main__":main()
