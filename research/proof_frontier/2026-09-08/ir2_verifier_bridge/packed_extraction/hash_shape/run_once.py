#!/usr/bin/env python3
"""One public native hash-pair constructor; preserve exact sources/command/output."""
from pathlib import Path
import datetime,hashlib,json,subprocess,time
root=Path(__file__).resolve().parent
repo=root.parents[5]
p3=Path('/Users/ember/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7')
paths=[root/'src/main.rs',root/'Cargo.toml',root/'Cargo.lock',root/'run_once.py',root/'target/release/actual-poseidon-leaf-shape-alias',p3/'symmetric/src/sponge.rs',p3/'symmetric/src/compression.rs',p3/'baby-bear/src/poseidon2.rs',p3/'merkle-tree/src/hiding_mmcs.rs',p3/'merkle-tree/src/mmcs.rs',repo/'research/vfhe_2026_09_08/proved_operation/backend/src/lib.rs',repo/'research/vfhe_2026_09_08/query_runtime/Cargo.lock',repo/'research/vfhe_2026_09_08/query_runtime/acceptance_bridge/run.py']
def pin(p):
 b=p.read_bytes();return {'path':str(p),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
pins={'before_run_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'sources':[pin(p) for p in paths]}
pp=root/'SOURCE_PINS.json';assert not pp.exists();pp.write_text(json.dumps(pins,indent=2)+'\n')
cmd=['target/release/actual-poseidon-leaf-shape-alias'];start=time.monotonic()
with (root/'results/result.json').open('xb') as out,(root/'results/run.stderr').open('xb') as err:r=subprocess.run(cmd,cwd=root,stdout=out,stderr=err,timeout=15)
record={'argv':cmd,'cwd':str(root),'exit':r.returncode,'seconds':time.monotonic()-start,'source_pins_sha256':pin(pp)['sha256'],'output':pin(root/'results/result.json'),'stderr':pin(root/'results/run.stderr'),'sources_unchanged':all(pin(p)==q for p,q in zip(paths,pins['sources']))}
(root/'results/command.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record));assert r.returncode==0 and record['sources_unchanged']
