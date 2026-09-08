#!/usr/bin/env python3
"""Retain a bounded command's exact public build/execution output."""
import argparse, hashlib, json, os, pathlib, subprocess, time
p=argparse.ArgumentParser();p.add_argument('name');p.add_argument('--lean',action='store_true');p.add_argument('--timeout',type=int,default=180);p.add_argument('command',nargs=argparse.REMAINDER);a=p.parse_args()
root=pathlib.Path(__file__).resolve().parent;cmd=a.command
if cmd and cmd[0]=='--':cmd=cmd[1:]
env=os.environ.copy()
if a.lean:
 pins=json.load(open(root/'results/lean-001.json'));env['LEAN_PATH']=pins['lean_path']
 cmd=[pins['command'][0]]+cmd
start=time.monotonic();record={'command':cmd,'cwd':str(root),'timeout_seconds':a.timeout}
if a.lean:record['lean_path']=env['LEAN_PATH']
with open(root/f'results/{a.name}.stdout','wb') as out,open(root/f'results/{a.name}.stderr','wb') as err:
 try:run=subprocess.run(cmd,cwd=root,env=env,stdout=out,stderr=err,timeout=a.timeout);record['exit']=run.returncode
 except subprocess.TimeoutExpired:record.update(exit=None,timed_out=True)
record['seconds']=time.monotonic()-start
for kind in ['stdout','stderr']:
 path=root/f'results/{a.name}.{kind}';record[kind]={'path':str(path.relative_to(root)),'bytes':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
(root/f'results/{a.name}.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record));raise SystemExit(record['exit'] if record['exit'] is not None else 124)
