#!/usr/bin/env python3
"""Compile the isolated optimization proposal without changing prior artifacts."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
FORMAL=ROOT/'formal/integer_certificate_emission/optimization'
COMPANION=Path('/Users/ember/dev/minidregg')
LEAN='/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean'

def main():
    envlog=json.loads((ROOT/'experiments/results/environment.json').read_text())
    paths=next(x['stdout'].strip() for x in envlog['checks'] if x['command']==['lake','env','printenv','LEAN_PATH'])
    overlay=FORMAL/'build/Compiler';overlay.mkdir(parents=True,exist_ok=True)
    for source in (COMPANION/'.lake/build/lib/lean/Compiler').iterdir():
        target=overlay/source.name
        if not target.exists() and not target.is_symlink(): target.symlink_to(source)
    for name in ['IntegerCertificateEmission','LargeIntegerCertificateEmission']:
        target=overlay/(name+'.olean')
        if not target.exists() and not target.is_symlink():
            target.symlink_to(ROOT/'formal/integer_certificate_emission/build/Compiler'/(name+'.olean'))
    env=dict(os.environ,LEAN_PATH=str(FORMAL/'build')+':'+paths)
    name=sys.argv[1] if len(sys.argv)>1 else 'AirSimplify'
    dependencies=[] if name=='AirSimplify' else ['AirSimplify']
    if name=='SimplificationChecks': dependencies.append('IntegerCertificateSimplification')
    for dependency in dependencies:
        latest=json.loads(sorted(HERE.glob('compile_'+dependency+'_*.json'))[-1].read_text())
        current=hashlib.sha256((FORMAL/'Compiler'/(dependency+'.lean')).read_bytes()).hexdigest()
        assert latest['exit_code']==0 and latest['source_sha256']==current, 'stale dependency '+dependency
    source=FORMAL/'Compiler'/(name+'.lean');output=overlay/(name+'.olean')
    assert not output.is_symlink()
    source_sha256=hashlib.sha256(source.read_bytes()).hexdigest()
    cmd=[LEAN,'-o',str(output),str(source)]
    p=subprocess.run(cmd,cwd=FORMAL,env=env,capture_output=True,text=True)
    assert source_sha256==hashlib.sha256(source.read_bytes()).hexdigest()
    record=dict(command=cmd,cwd=str(FORMAL),lean_path=env['LEAN_PATH'],source_sha256=source_sha256,
                exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr)
    index=len(list(HERE.glob('compile_'+name+'_*.json')))+1
    (HERE/f'compile_{name}_{index:02}.json').write_text(json.dumps(record,indent=2)+'\n')
    print(p.stdout+p.stderr)
    return p.returncode

if __name__=='__main__': raise SystemExit(main())
