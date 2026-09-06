#!/usr/bin/env python3
"""Run via minidregg's `lake env python3`; writes only in this lane's directory."""
import difflib, hashlib, json, os, re, subprocess, tempfile, time
from pathlib import Path
root=Path(__file__).resolve().parent
companion=Path('/Users/ember/dev/minidregg')
source=root/'Compiler/BFVScaleLiftRefinement.lean'
module='Compiler.BFVScaleLiftRefinement'
records=[]

def run(cmd,*,env=None,cwd=companion):
    started=time.monotonic()
    r=subprocess.run(cmd,cwd=cwd,env=env,text=True,capture_output=True)
    records.append(dict(command=[str(x) for x in cmd],cwd=str(cwd),exit_code=r.returncode,
                        stdout=r.stdout,stderr=r.stderr,elapsed_seconds=time.monotonic()-started))
    (root/'validation.json').write_text(json.dumps(records,indent=2)+'\n')
    if r.returncode: raise SystemExit(f'FAILED {cmd[0]}: {r.stdout}\n{r.stderr}')
    return r.stdout

assert os.environ.get('LEAN_PATH'), 'Run through companion lake env.'
assert len(re.findall(r'^theorem ',source.read_text(),re.M))==27
assert source.read_text().count('#guard_msgs in')==27
assert not re.search(r'^\s*(axiom|sorry|admit)\b|\b(native_decide|ofReduceBool)\b',source.read_text(),re.M)
base=(companion/'Compiler.lean').read_text()
assert f'import {module}' not in base
augmented=base+f'\nimport {module}\n'
patch=''.join(difflib.unified_diff(base.splitlines(True),augmented.splitlines(True),fromfile='a/Compiler.lean',tofile='b/Compiler.lean'))
patch+=''.join(difflib.unified_diff([],source.read_text().splitlines(True),fromfile='/dev/null',tofile='b/Compiler/BFVScaleLiftRefinement.lean'))
(root/'minidregg-bfv-lift-refinement.patch').write_text(patch)
run(['git','rev-parse','HEAD'])
run(['lean','--version'])
with tempfile.TemporaryDirectory(prefix='.validation-',dir=root) as tmp:
    tmp=Path(tmp);(tmp/'Compiler').mkdir()
    for obj in (companion/'.lake/build/lib/lean/Compiler').iterdir():
        (tmp/'Compiler'/obj.name).symlink_to(obj)
    (tmp/'Compiler.lean').write_text(augmented)
    env=os.environ.copy();env['LEAN_PATH']=str(tmp)+':'+env['LEAN_PATH']
    run(['lean','-o',str(tmp/'Compiler/BFVScaleLiftRefinement.olean'),str(source)],env=env,cwd=root)
    run(['lean','-o',str(tmp/'Compiler.olean'),str(tmp/'Compiler.lean')],env=env,cwd=tmp)
run(['bash','scripts/check-import-boundary.sh'])
run(['git','apply','--check',str(root/'minidregg-bfv-lift-refinement.patch')])
metadata=dict(label='EXECUTED isolated source and Compiler umbrella validation; no full Minidregg build',
              source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
              patch_sha256=hashlib.sha256((root/'minidregg-bfv-lift-refinement.patch').read_bytes()).hexdigest(),
              declarations=27,axiom_pins=27,all_commands_passed=True,
              source_imports=[s for s in source.read_text().splitlines() if s.startswith('import ')])
(root/'validation-summary.json').write_text(json.dumps(metadata,indent=2)+'\n')
print(json.dumps(metadata,indent=2))
