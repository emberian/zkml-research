"""Freeze all executable sources, declared runtime, fixture and public keys."""
import datetime
import os
import subprocess
import sys
from common import *


def main():
    assert not (ROOT/'freeze.json').exists() and not RUNTIME.exists()
    preflight=load(ROOT/'preflight.json');assert preflight['counts']=={'Learn':384,'Infer':96}
    source_manifest=load(PRIOR/'source_manifest.json')
    for name,binary in [('issuer',ISSUER),('reader',READER)]:assert sha(binary)==source_manifest['binary_hashes'][name]
    assert sha(HOST)=='6c0954fae626940e720c47bfb535347ecd3c3fc0b19b36d0834b70465b02d197'
    assert sha(FORMAL/'artifacts/learn.json')=='94e8369ffc8fcdf57b8351b278d5af90dc49a26d83600d40f0bd6a0da359dde8'
    assert sha(FORMAL/'artifacts/infer.json')=='b742ed7710d2680119eceeff0c553d675e1ce187a503981fc500a6a4a683b80c'
    assert CK.is_file() and CK.stat().st_mode&0o777==0o600
    files={str(p) for p in ROOT.glob('*.py')}
    files.update(str(ROOT/name) for name in ['CONTRACT.md','preflight.json'])
    files.update(str(p) for p in [HOST,ISSUER,READER,PK,SK,FIXTURE,PRIOR/'utility/manifest.json',PRIOR/'source_manifest.json',
                                 PRIOR/'Cargo.toml',PRIOR/'Cargo.lock',PRIOR/'src/lib.rs',PRIOR/'src/bin/issuer.rs',PRIOR/'src/bin/reader.rs'])
    files.update(str(FIXED/name) for name in ['Cargo.toml','Cargo.lock','build_pins.json','build.events.jsonl','feature_source.txt','freeze.json'])
    files.update(str(p) for p in (FIXED/'src').glob('*.rs'))
    files.update(str(FORMAL/name) for name in ['SCHEMA.md','artifacts/learn.json','artifacts/infer.json',
                    'EmitPrivateAddressEma.lean','Compiler/PrivateAddressEmaSchedule.lean','results/verification.json'])
    syntax=subprocess.run([sys.executable,'-m','py_compile',*sorted(str(p) for p in ROOT.glob('*.py'))],capture_output=True,text=True)
    assert syntax.returncode==0,syntax.stderr
    value={'claim':'EXECUTED','schema':'emitted-fixed-fft-full-workload-freeze-v1','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
           'files':{path:meta(path) for path in sorted(files)},'python':sys.version,'python_executable':sys.executable,
           'prelaunch_syntax_check':{'returncode':syntax.returncode,'stdout':syntax.stdout,'stderr':syntax.stderr},
           'counts':preflight['counts'],'expiry':0,'host_invocations':960,'issuer_invocations':404,'replay_pairs':480,
           'private_opens':preflight['private_opens'],'key_custody':{'reuse':'prior two-step public/client/server material, read-only',
           'private_key_path':str(CK),'private_key_bytes':CK.stat().st_size,'private_key_read_or_hashed':False,'full_reader_retained':True},
           'runtime_environment':{'RAYON_NUM_THREADS':'1'},'six_hour_cap':True,'hard_utc_cutoff':'2026-09-08T15:00:00+00:00',
           'post_drain_provenance_only_sealing_permitted':True,'no_retries':True}
    save(ROOT/'freeze.json',value);print(__import__('json').dumps({'freeze_sha256':sha(ROOT/'freeze.json'),'files':len(files),'host_invocations':960,'private_opens':484}))


if __name__=='__main__':main()
