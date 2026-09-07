#!/usr/bin/env python3
"""Observe RSS of this run's own processes; sampled RSS is not true peak memory."""
from pathlib import Path
import hashlib
import json
import shlex
import subprocess
import time

HERE=Path(__file__).resolve().parent
OUT=HERE/"outputs"
PATTERN="fixed_span/scaling/full_run/run.py"


def main():
    samples=[]
    while True:
        matches=subprocess.run(["pgrep","-f",PATTERN],capture_output=True,text=True)
        rows=[]
        for token in matches.stdout.split():
            pid=int(token)
            command=subprocess.run(["ps","-p",str(pid),"-o","command="],capture_output=True,text=True).stdout.strip()
            arguments=shlex.split(command)
            indices=[i for i,arg in enumerate(arguments) if arg.endswith(PATTERN)]
            if not indices:continue
            index=indices[0]
            role=arguments[index+1] if index+1<len(arguments) and arguments[index+1] in ("setup","issue","evaluate") else "driver"
            fields=subprocess.run(["ps","-p",str(pid),"-o","pid=,ppid=,rss="],capture_output=True,text=True).stdout.split()
            if len(fields)==3:rows.append({"pid":int(fields[0]),"ppid":int(fields[1]),"rss_kib":int(fields[2]),"role":role})
        samples.append({"unix_time":time.time(),"processes":rows})
        maxima={}
        for sample in samples:
            for row in sample["processes"]:maxima[row["role"]]=max(maxima.get(row["role"],0),row["rss_kib"])
        report={"scope":"10-second RSS samples of this run only, started after setup; not an OS high-water mark",
            "script_sha256":hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            "max_observed_rss_kib_by_role":maxima,"samples":samples}
        destination=OUT/"observed_memory.json"
        temporary=destination.with_suffix(".tmp")
        temporary.write_text(json.dumps(report,indent=2)+"\n");temporary.replace(destination)
        if (OUT/"crypto_execution.json").exists() or (OUT/"STOPPED.json").exists():
            print(json.dumps({"finished":True,"samples":len(samples),"max_observed_rss_kib_by_role":maxima}));return
        time.sleep(10)


if __name__=="__main__":main()
