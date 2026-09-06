#!/usr/bin/env python3
"""Stage the two compiler modules and inspect their integration without companion writes."""
from pathlib import Path
import difflib
import hashlib
import json
import os
import re
import subprocess

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
FORMAL = ROOT / 'formal/integer_certificate_emission'
COMPANION = Path('/Users/ember/dev/minidregg')
LEAN = '/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    modules = ['IntegerCertificateEmission', 'LargeIntegerCertificateEmission']
    pieces = []
    pins = {}
    for name in modules:
        path = FORMAL / 'Compiler' / (name+'.lean')
        source = path.read_text()
        latest = json.loads(sorted(HERE.glob('compile_'+name+'_*.json'))[-1].read_text())
        assert latest['exit_code'] == 0 and latest['source_sha256'] == sha(path)
        assert not re.search(r'\b(sorry|admit|native_decide)\b|^\s*axiom\s|^#guard\s', source, re.M)
        count = len(re.findall(r'^theorem ', source, re.M))
        assert count == len(re.findall(r'^#guard_msgs .* in #print axioms ', source, re.M))
        pins[name] = count
        rel = 'Compiler/'+name+'.lean'
        pieces += ['diff --git a/'+rel+' b/'+rel+'\n', 'new file mode 100644\n']
        pieces.extend(difflib.unified_diff([], source.splitlines(keepends=True),
                                         fromfile='/dev/null', tofile='b/'+rel))
    base = (COMPANION/'Compiler.lean').read_text()
    staged = base.rstrip()+'\n'+''.join('import Compiler.'+n+'\n' for n in modules)
    pieces.append('diff --git a/Compiler.lean b/Compiler.lean\n')
    pieces.extend(difflib.unified_diff(base.splitlines(keepends=True), staged.splitlines(keepends=True),
                                     fromfile='a/Compiler.lean', tofile='b/Compiler.lean'))
    patch = FORMAL/'minidregg-integer-certificate-emission.patch'
    patch.write_text(''.join(pieces))
    umbrella = FORMAL/'Compiler.lean'
    umbrella.write_text(staged)
    envlog = json.loads((ROOT/'experiments/results/environment.json').read_text())
    paths = next(x['stdout'].strip() for x in envlog['checks']
                 if x['command'] == ['lake', 'env', 'printenv', 'LEAN_PATH'])
    env = dict(os.environ, LEAN_PATH=str(FORMAL/'build')+':'+paths)
    output = FORMAL/'build/Compiler.olean'
    assert not output.is_symlink()
    commands = [([LEAN,'-o',str(output),str(umbrella)],FORMAL),
        (['bash',str(COMPANION/'scripts/check-import-boundary.sh')],COMPANION),
        (['git','apply','--check',str(patch)],COMPANION)]
    checks=[]
    for command,cwd in commands:
        p=subprocess.run(command,cwd=cwd,env=env,text=True,capture_output=True)
        checks.append(dict(command=command,cwd=str(cwd),exit_code=p.returncode,
                           stdout=p.stdout,stderr=p.stderr))
        print(f'{command[0]} exit {p.returncode}\n{p.stdout}{p.stderr}',flush=True)
    deps=['Compiler/BfvSignedAccumulatorAir.lean','Compiler/Emit.lean',
          'Compiler/AirRange.lean','Compiler/AirBignum.lean','Compiler/AirModularView.lean',
          'Compiler/DescriptorEval.lean','Compiler/NativeKernelPlan.lean','Compiler/EmitShare.lean',
          'Compiler/EmitSerialize.lean','Compiler.lean','CLAUDE.md','ATLAS.md']
    evidence=dict(patch_sha256=sha(patch),pins=pins,checks=checks,
        companion_sources={p:sha(COMPANION/p) for p in deps},
        note='Staged umbrella using existing dependency oleans; not a clean full lake build.')
    index=len(list(HERE.glob('review_*.json')))+1
    (HERE/f'review_{index:02}.json').write_text(json.dumps(evidence,indent=2)+'\n')
    return 0 if all(x['exit_code']==0 for x in checks) else 1

if __name__=='__main__':
    raise SystemExit(main())
