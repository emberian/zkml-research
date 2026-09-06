#!/usr/bin/env python3
"""Link a small API probe to the existing pinned rlib; no HE rerun or cargo rebuild."""
import gzip,hashlib,json,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent;deps=ROOT.parent/'engine_probe/target/release/deps';build=ROOT/'.build';build.mkdir(exist_ok=True)
rlibs=list(deps.glob('libfhe_math-*.rlib'));assert len(rlibs)==1
src=ROOT/'word_probe.rs';exe=build/'word_probe';records=[]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
for cmd in [['rustc','--version'],['rustc','--edition=2021',str(src),'-L','dependency='+str(deps),'--extern','fhe_math='+str(rlibs[0]),'-o',str(exe)], [str(exe)]]:
 st=time.monotonic();r=subprocess.run(cmd,capture_output=True,text=True);record=dict(command=cmd,exit_code=r.returncode,elapsed_seconds=time.monotonic()-st,stderr=r.stderr)
 if cmd==[str(exe)]:
  payload=r.stdout.encode();(ROOT/'actual-words.jsonl.gz').write_bytes(gzip.compress(payload,mtime=0));record['stdout_gzip']='actual-words.jsonl.gz';record['rows']=len(r.stdout.splitlines());record['stdout_sha256']=hashlib.sha256(payload).hexdigest()
 else:record['stdout']=r.stdout
 records.append(record);(ROOT/'probe-run.json').write_text(json.dumps(dict(label='EXECUTED actual cached fhe-math API word probe',source_sha256=sha(src),rlib_sha256=sha(rlibs[0]),records=records),indent=2)+'\n')
 assert r.returncode==0,r.stderr
print(json.dumps(records[-1],indent=2))
