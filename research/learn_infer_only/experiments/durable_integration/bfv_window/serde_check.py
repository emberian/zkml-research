#!/usr/bin/env python3
from pathlib import Path
import hashlib,json,os,subprocess,time
E=Path(__file__).resolve().parent;R=E.parents[2];repo=R.parents[1];P=E/'serde_probe'
paths=[P/'src/main.rs',P/'Cargo.toml',P/'Cargo.lock',
Path('/Users/ember/dev/breadstuffs/vendor/fhe-dregg/src/bfv/ciphertext.rs'),
Path('/Users/ember/dev/breadstuffs/vendor/fhe-dregg/src/bfv/ops/mod.rs')]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
before={str(p):sha(p) for p in paths}
env=dict(os.environ,CARGO_TARGET_DIR=str(P/'target'))
cmd=['cargo','run','--offline','--release','--manifest-path',str(P/'Cargo.toml')];t=time.time()
p=subprocess.run(cmd,cwd=repo,env=env,capture_output=True,text=True)
n=len(list(E.glob('serde_check_*.json')))+1
rec=dict(command=cmd,cwd=str(repo),cargo_target_dir=env['CARGO_TARGET_DIR'],exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr,elapsed_seconds=time.time()-t,source_sha256=before,inputs_unchanged=all(sha(Path(f))==h for f,h in before.items()),scope='Actual serialization/canonicalization fixture; full key retained by test reader; no library correctness proof')
(E/f'serde_check_{n:02}.json').write_text(json.dumps(rec,indent=2)+'\n');(E/'serde_check.json').write_text(json.dumps(rec,indent=2)+'\n')
(E/'serde_run.log').write_text(p.stdout);(E/'serde_build_and_stderr.log').write_text(p.stderr)
print(json.dumps(rec,indent=2));raise SystemExit(p.returncode)
