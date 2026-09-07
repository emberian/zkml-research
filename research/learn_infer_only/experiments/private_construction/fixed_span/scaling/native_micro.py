#!/usr/bin/env python3
"""One native same-equation micro, followed by private Python-pow equality checks."""
from pathlib import Path
import argparse
import json
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import micro
from native_pow import NativePow, LIBRARY


def role(name, out, vector=None):
    backend = NativePow(micro.P, record_for_private_verification=True)
    records = []
    micro.pow = backend
    micro.finish = records.append
    try:
        if name == "setup": micro.setup(out)
        elif name == "issue": micro.issue(out,vector)
        elif name == "evaluate": micro.evaluate(out)
        report = records[0]
        # These checks run AFTER the measured phase, in the same private role.
        # Exponents/coins/master-related values are never serialized or printed.
        start = time.perf_counter_ns()
        for a,e,m,value in backend.calls:
            assert pow(a,e,m) == value
        report["python_pow_equality_checks"] = len(backend.calls)
        report["python_pow_verification_ns_separate"] = time.perf_counter_ns()-start
        report["arithmetic_backend"] = "installed OpenSSL BN_mod_exp_mont_consttime + Python inversions"
        report["private_verification_values_exported"] = False
        print(json.dumps(report),flush=True)
    finally:
        backend.close()


def run():
    out = HERE/"native_micro_outputs"
    out.mkdir(exist_ok=True)
    vector = micro.UTILITY/"issuer_oracle/vectors/h0-e0001.json"
    phases = []
    for name in ("setup", "issue", "evaluate"):
        args = [sys.executable,"-I","-B",str(Path(__file__).resolve()),name,"--out",str(out)]
        if name == "issue": args += ["--vector",str(vector)]
        print(json.dumps({"event":"starting", "role":name}),flush=True)
        start = time.perf_counter_ns()
        result = subprocess.run(args,check=True,capture_output=True,text=True)
        report = json.loads(result.stdout)
        report["subprocess_wall_ns_including_separate_checks"] = time.perf_counter_ns()-start
        phases.append(report)
        print(json.dumps(report),flush=True)
    expected = sum(a*b for a,b in zip(json.loads(vector.read_text()),micro.queries()[0],strict=True))
    assert phases[-1]["score"] == expected
    report = {"passed":True,"scope":"one native public-fixture encryption and fixed-query read; same group and equations",
        "script_sha256":micro.sha(__file__),"base_micro_sha256":micro.sha(HERE/"micro.py"),
        "backend_sha256":micro.sha(HERE/"native_pow.py"),"library_path":str(LIBRARY),
        "library_sha256":micro.sha(LIBRARY),"input_sha256":micro.sha(vector),
        "public_queries":json.loads((HERE/"linear_results.json").read_text())["query_files_sha256"],
        "phases":phases,"constant_time_protocol_claim":False,"full_384_run":False,
        "outputs":{p.name:{"bytes":p.stat().st_size,"sha256":micro.sha(p)} for p in out.iterdir() if p.suffix==".bin"},
        "master_exported":False,"private_pow_check_operands_exported":False,
        "searches":{"web":0,"scry_sql":0,"package_installs":0}}
    (HERE/"native_micro_results.json").write_text(json.dumps(report,indent=2)+"\n")
    print(json.dumps({"passed":True,"score_matches_separate_oracle":True,
        "total_python_pow_checks":sum(p["python_pow_equality_checks"] for p in phases)}),flush=True)


if __name__ == "__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("role",nargs="?",default="run",choices=["run","setup","issue","evaluate"])
    parser.add_argument("--out",type=Path)
    parser.add_argument("--vector",type=Path)
    args=parser.parse_args()
    if args.role=="run":run()
    else:role(args.role,args.out,args.vector)
