#!/usr/bin/env python3
"""Stage/check the generic optimization patch and preserve first-tranche hashes."""
from pathlib import Path
import difflib
import gzip
import hashlib
import json
import os
import re
import subprocess

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[2]
FORMAL=ROOT/'formal/integer_certificate_emission/optimization'
COMPANION=Path('/Users/ember/dev/minidregg')
LEAN='/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    old=json.loads((ROOT/'experiments/integer_certificate_emission/artifact_hashes.json').read_text())
    changes=[p for p,h in old['artifacts'].items() if sha(ROOT/p)!=h]
    assert not changes,changes
    modules=['AirSimplify','IntegerCertificateSimplification']
    pieces=[];pins={}
    for name in modules:
        p=FORMAL/'Compiler'/(name+'.lean');s=p.read_text()
        latest=json.loads(sorted(HERE.glob('compile_'+name+'_*.json'))[-1].read_text())
        assert latest['exit_code']==0 and latest['source_sha256']==sha(p)
        assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|^#guard\s',s,re.M)
        count=len(re.findall(r'^theorem ',s,re.M))
        assert count==len(re.findall(r'^#guard_msgs .* in #print axioms ',s,re.M))
        pins[name]=count
        rel='Compiler/'+name+'.lean'
        pieces+=['diff --git a/'+rel+' b/'+rel+'\n','new file mode 100644\n']
        pieces.extend(difflib.unified_diff([],s.splitlines(keepends=True),fromfile='/dev/null',tofile='b/'+rel))
    base=(COMPANION/'Compiler.lean').read_text()
    staged=base.rstrip()+'\n'+''.join('import Compiler.'+n+'\n' for n in modules)
    pieces.append('diff --git a/Compiler.lean b/Compiler.lean\n')
    pieces.extend(difflib.unified_diff(base.splitlines(keepends=True),staged.splitlines(keepends=True),
                                     fromfile='a/Compiler.lean',tofile='b/Compiler.lean'))
    patch=FORMAL/'minidregg-air-simplification.patch';patch.write_text(''.join(pieces))
    (FORMAL/'Compiler.lean').write_text(staged)
    envlog=json.loads((ROOT/'experiments/results/environment.json').read_text())
    paths=next(x['stdout'].strip() for x in envlog['checks'] if x['command']==['lake','env','printenv','LEAN_PATH'])
    env=dict(os.environ,LEAN_PATH=str(FORMAL/'build')+':'+paths)
    output=FORMAL/'build/Compiler.olean';assert not output.is_symlink()
    commands=[([LEAN,'-o',str(output),str(FORMAL/'Compiler.lean')],FORMAL),
      (['bash',str(COMPANION/'scripts/check-import-boundary.sh')],COMPANION),
      (['git','apply','--check',str(patch)],COMPANION)]
    checks=[]
    for command,cwd in commands:
        p=subprocess.run(command,cwd=cwd,env=env,text=True,capture_output=True)
        checks.append(dict(command=command,cwd=str(cwd),exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr))
        print(f'{command[0]} exit {p.returncode}\n{p.stdout}{p.stderr}',flush=True)
    # The source is unchanged after all read-only companion checks too.
    assert not [p for p,h in old['artifacts'].items() if sha(ROOT/p)!=h]
    depfiles=['Compiler/Air.lean','Compiler/Signature.lean','Compiler/Emit.lean','Compiler/EmitShare.lean',
      'Compiler/DescriptorEval.lean','Compiler/NativeKernelPlan.lean','Compiler.lean']
    records=dict(checks=checks,pins=pins,patch_sha256=sha(patch),
      first_tranche_unchanged=True,first_tranche_manifest_sha256=sha(ROOT/'experiments/integer_certificate_emission/artifact_hashes.json'),
      companion_sources={p:sha(COMPANION/p) for p in depfiles},
      scope='Isolated umbrella against existing dependency oleans, not a clean full lake build; application module depends on preserved first-tranche patch.')
    index=len(list(HERE.glob('review_*.json')))+1
    (HERE/f'review_{index:02}.json').write_text(json.dumps(records,indent=2)+'\n')
    return 0 if all(x['exit_code']==0 for x in checks) else 1

if __name__=='__main__':raise SystemExit(main())
