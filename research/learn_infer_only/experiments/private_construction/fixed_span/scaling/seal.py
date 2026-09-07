#!/usr/bin/env python3
"""Check recorded source/artifact links, then pin the owned evidence package."""
from pathlib import Path
import hashlib
import json

HERE=Path(__file__).resolve().parent
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def read(path):return json.loads(Path(path).read_text())


def main():
    linear=read(HERE/"linear_results.json")
    assert linear["script_sha256"]==sha(HERE/"linear_audit.py")
    for path,digest in linear["query_files_sha256"].items():assert sha(path)==digest
    for filename,script,output_dir in [("micro_results.json","micro.py","micro_results"),
        ("native_micro_results.json","native_micro.py","native_micro_outputs")]:
        report=read(HERE/filename)
        assert report["script_sha256"]==sha(HERE/script)
        for name,item in report["outputs"].items():
            path=HERE/output_dir/name
            assert path.stat().st_size==item["bytes"] and sha(path)==item["sha256"]
    python=read(HERE/"micro_results.json")
    assert python["linear_audit_sha256"]==sha(HERE/"linear_audit.py")
    assert python["linear_results_sha256"]==sha(HERE/"linear_results.json")
    assert python["phases"]==read(HERE/"micro_results.as_run.json")["phases"]
    native=read(HERE/"native_micro_results.json")
    assert native["backend_sha256"]==sha(HERE/"native_pow.py")
    assert native["base_micro_sha256"]==sha(HERE/"micro.py")
    assert sha(native["library_path"])==native["library_sha256"]
    full=HERE/"full_run/outputs"
    manifest=read(full/"run_manifest.json")
    assert manifest["script_sha256"]==sha(HERE/"full_run/run.py")
    assert manifest["native_backend_sha256"]==sha(HERE/"native_pow.py")
    assert manifest["general_lemma_sha256"]==sha(HERE/"GENERAL_FIXED_SPAN.md")
    assert manifest["micro_equality_evidence_sha256"]==sha(HERE/"native_micro_results.json")
    summary=read(full/"SUMMARY.json");assert summary["passed"]
    for name,entry in summary["artifact_files"].items():
        path=full/name
        assert path.stat().st_size==entry["bytes"] and sha(path)==entry["sha256"]
    frozen={"span.py":"a0ce6572e3e2f49d94aadc5e1182c9b4a9d5006e106a685a08d74a3bcff22290",
        "audit.py":"2ad9807b7d54dc3e5b4899b734b63bc309c5a7e716e2b2142a7efde1c3bf6451",
        "ADAPTIVE_FIXED_SPAN.md":"091403d6f3e1a7a65e5baef3977dc789595584582d17bbbf2190878fa18874d9"}
    for name,digest in frozen.items():assert sha(HERE.parent/name)==digest
    source=Path("/Users/ember/dev/gh/forks/IACR-eprint-mirror/2015/017.pdf")
    assert sha(source)=="353f454857a5ef421ab7b17545b9657f5d192dc0a37f022cca7b71e916f84712"
    files={str(p.relative_to(HERE)):{"bytes":p.stat().st_size,"sha256":sha(p)} for p in sorted(HERE.rglob("*"))
        if p.is_file() and p.suffix in (".py",".md",".json",".jsonl",".txt")
        and p.name not in ("EVIDENCE_MANIFEST.json","seal_stdout.txt")}
    report={"passed":True,"source_and_artifact_links_checked":True,
        "full_run_source_or_theorem_changed":False,"frozen_3d_files":frozen,
        "primary_source":{"absolute_path":str(source),"sha256":sha(source),
            "access":"local construction and selective game/theorem; Fig2 and printedpp7-9"},
        "files":files,"script_sha256":sha(__file__)}
    (HERE/"EVIDENCE_MANIFEST.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"passed":True,"recorded_files":len(files),"frozen_3D_files_unchanged":True},indent=2))


if __name__=="__main__":main()
