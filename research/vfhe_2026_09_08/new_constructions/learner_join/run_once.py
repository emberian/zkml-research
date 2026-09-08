#!/usr/bin/env python3
"""The one frozen learner join attempt; there is no retry path."""
from pathlib import Path
import datetime,hashlib,json,os,signal,subprocess,time
root=Path(__file__).resolve().parent;src=root/'matvecmul'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(root/'source_pins.json')=='17fc4dfc740f59f327fa5b7dc191e8c9b081c12e93d6c1d902a570aee1ad1fc5'
pins=json.loads((root/'source_pins.json').read_text())
for rel,digest in pins['all_source_files'].items():assert sha(src/rel)==digest,rel
for rel,digest in pins['public_inputs_and_contract'].items():assert sha(root/rel)==digest,rel
for name,digest in pins['binaries'].items():assert sha(src/'target/release/examples'/name)==digest,name
record_path=root/'command.json';assert not record_path.exists(),'one attempt only'
output=root/'normal_001';assert not output.exists()
command=[str(src/'target/release/examples/learner_proof'),str(root/'learner_inputs.bin'),str(output)]
record={'command':command,'cwd':str(src),'timeout_seconds':600,'source_pins_sha256':sha(root/'source_pins.json'),
        'driver_sha256':sha(Path(__file__)),'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'rayon_num_threads_environment':os.getenv('RAYON_NUM_THREADS')}
record_path.write_text(json.dumps(record,indent=2)+'\n')
with (root/'normal_001.log').open('xb') as stdout,(root/'normal_001.stderr').open('xb') as stderr:
    started=time.monotonic()
    process=subprocess.Popen(command,cwd=src,stdout=stdout,stderr=stderr,start_new_session=True)
    record['pid']=process.pid;record_path.write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps({'started_utc':record['started_utc'],'pid':process.pid}),flush=True)
    try:record['exit_code']=process.wait(timeout=600);record['timed_out']=False
    except subprocess.TimeoutExpired:
        os.killpg(process.pid,signal.SIGKILL);record['exit_code']=process.wait();record['timed_out']=True
    record['wall_seconds']=time.monotonic()-started
record['finished_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
record['source_unchanged']=all(sha(src/rel)==digest for rel,digest in pins['all_source_files'].items())
record['inputs_unchanged']=all(sha(root/rel)==digest for rel,digest in pins['public_inputs_and_contract'].items())
record['stdout_sha256']=sha(root/'normal_001.log');record['stderr_sha256']=sha(root/'normal_001.stderr')
record_path.write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2),flush=True)
raise SystemExit(0 if record['exit_code']==0 and record['source_unchanged'] and record['inputs_unchanged'] else 1)
