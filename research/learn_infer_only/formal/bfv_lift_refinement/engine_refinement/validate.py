#!/usr/bin/env python3
"""Run with read-only companion lake env; builds and patches only owned output."""
import difflib,hashlib,json,os,re,subprocess,tempfile,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent;COMP=Path('/Users/ember/dev/minidregg')
SRC=ROOT/'Compiler/FheRnsScaleDecomposition.lean';FIRST=ROOT.parent/'Compiler/BFVScaleLiftRefinement.lean'
records=[]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd,cwd=COMP,env=None):
 start=time.monotonic();r=subprocess.run(list(map(str,cmd)),cwd=cwd,env=env,text=True,capture_output=True)
 records.append(dict(command=list(map(str,cmd)),cwd=str(cwd),exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr,elapsed_seconds=time.monotonic()-start))
 (ROOT/'validation.json').write_text(json.dumps(records,indent=2)+'\n')
 if r.returncode:raise SystemExit(r.stdout+r.stderr)
 return r.stdout
assert digest(FIRST)=='1abe56f822ba911e85b0697887cf2317eecc990433f460dedc95a3085ccab2fd'
assert len(re.findall(r'^theorem ',SRC.read_text(),re.M))==33
assert SRC.read_text().count('#guard_msgs in')==33
assert not re.search(r'^\s*(axiom|sorry|admit)\b|\b(native_decide|ofReduceBool)\b',SRC.read_text(),re.M)
base=(COMP/'Compiler.lean').read_text();lines=base.splitlines(True)
i=next(i for i,l in enumerate(lines) if l.startswith('import Compiler.Placeholder'))
lines.insert(i+1,'import Compiler.FheRnsScaleDecomposition  -- exact selected-lift/fixed-correction arithmetic; runtime proof remains open\n')
second=''.join(lines);combined=second+'\nimport Compiler.BFVScaleLiftRefinement\n'
patch=''.join(difflib.unified_diff(base.splitlines(True),second.splitlines(True),fromfile='a/Compiler.lean',tofile='b/Compiler.lean'))
patch+=''.join(difflib.unified_diff([],SRC.read_text().splitlines(True),fromfile='/dev/null',tofile='b/Compiler/FheRnsScaleDecomposition.lean'))
patchpath=ROOT/'minidregg-fhe-rns-scale-decomposition.patch';patchpath.write_text(patch)
run(['git','rev-parse','HEAD']);run(['lean','--version'])
with tempfile.TemporaryDirectory(prefix='.validation-',dir=ROOT) as td:
 temp=Path(td);(temp/'Compiler').mkdir()
 for obj in (COMP/'.lake/build/lib/lean/Compiler').iterdir():(temp/'Compiler'/obj.name).symlink_to(obj)
 (temp/'Compiler.lean').write_text(combined)
 env=os.environ.copy();env['LEAN_PATH']=str(temp)+':'+env['LEAN_PATH']
 run(['lean','-o',temp/'Compiler/BFVScaleLiftRefinement.olean',FIRST],ROOT.parent,env)
 run(['lean','-o',temp/'Compiler/FheRnsScaleDecomposition.olean',SRC],ROOT,env)
 run(['lean','-o',temp/'Compiler.olean',temp/'Compiler.lean'],temp,env)
run(['bash','scripts/check-import-boundary.sh'])
run(['git','apply','--check',patchpath])
run(['git','apply','--check',ROOT.parent/'minidregg-bfv-lift-refinement.patch',patchpath])
metadata=dict(label='EXECUTED source arithmetic patch, original first patch dependency, and isolated Compiler umbrella; no full Minidregg build',source_sha256=digest(SRC),patch_sha256=digest(patchpath),first_source_sha256=digest(FIRST),declarations=33,exact_axiom_pins=33,all_commands_passed=True)
(ROOT/'validation-summary.json').write_text(json.dumps(metadata,indent=2)+'\n');print(json.dumps(metadata,indent=2))
