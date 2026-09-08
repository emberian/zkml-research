#!/usr/bin/env python3
"""Execute the one frozen paired native attempt; no retry path."""
from pathlib import Path
import datetime, hashlib, json, os, signal, subprocess, time

root=Path(__file__).resolve().parent
source=root/'matvecmul'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins_path=root/'source_pins.json'
assert sha(pins_path)=='a10d6d94678b5435b388ebbcfcad3dd4d599195ba3b7d52ddd2ceb3ce52bfa85'
pins=json.loads(pins_path.read_text())
for rel,digest in pins['all_source_files'].items():assert sha(source/rel)==digest,rel
for name,digest in pins['binaries'].items():assert sha(source/'target/release/examples'/name)==digest,name
record_path=root/'command.json'
assert not record_path.exists(), 'one attempt only'
output=root/'paired_001'
assert not output.exists()
command=[str(source/'target/release/examples/matched_proof'),str(output)]
record={'command':command,'cwd':str(source),'timeout_seconds':600,'source_pins_sha256':sha(pins_path),
        'driver_sha256':sha(Path(__file__)),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
record_path.write_text(json.dumps(record,indent=2)+'\n')
with (root/'paired_001.log').open('xb') as stdout, (root/'paired_001.stderr').open('xb') as stderr:
    started=time.monotonic()
    process=subprocess.Popen(command,cwd=source,stdout=stdout,stderr=stderr,start_new_session=True)
    record['pid']=process.pid
    record_path.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'started_utc':record['started_utc'],'pid':process.pid}),flush=True)
    try:
        record['exit_code']=process.wait(timeout=600)
        record['timed_out']=False
    except subprocess.TimeoutExpired:
        os.killpg(process.pid,signal.SIGKILL)
        record['exit_code']=process.wait()
        record['timed_out']=True
    record['wall_seconds']=time.monotonic()-started
record['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
record['source_unchanged']=all(sha(source/rel)==digest for rel,digest in pins['all_source_files'].items())
record['stdout_sha256']=sha(root/'paired_001.log')
record['stderr_sha256']=sha(root/'paired_001.stderr')
record_path.write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2),flush=True)
raise SystemExit(0 if record['exit_code']==0 and record['source_unchanged'] else 1)
