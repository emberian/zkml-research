"""Validate the adapter against exact, minimal source slices, not stale oleans.
This is not a whole-project build. No stubs, axioms, or sorry are introduced.
"""
from pathlib import Path
import shutil
import subprocess, os, hashlib, json, sys
root=Path('/Users/ember/dev/minidregg')
base=Path(__file__).resolve().parent
print(subprocess.check_output(['df','-h','/System/Volumes/Data'],text=True),flush=True)
if shutil.disk_usage('/System/Volumes/Data').free < 30 * 2**30:
 raise SystemExit('Disk below 30 GiB; paused')
subprocess.run([sys.executable,str(base/'check_core.py')],check=True)
manifest=json.loads((base/'core-build-manifest.json').read_text())
assert manifest['source_sha256']==hashlib.sha256((base/'source/Selvage/BindingGame.lean').read_bytes()).hexdigest()
assert manifest['olean_sha256']==hashlib.sha256((base/'build/Selvage/BindingGame.olean').read_bytes()).hexdigest()
snippets=[]
def cut(path,start,end):
    original=base/'original'/path
    text=(original if original.exists() else root/path).read_text()
    a=text.index(start); b=text.index(end,a)
    snippet=text[a:b]
    saved=base/'source-slices'/(Path(path).stem+'.lean.txt')
    saved.parent.mkdir(exist_ok=True)
    if saved.exists():
        assert saved.read_text()==snippet, 'Upstream source slice changed: '+path
    else:
        saved.write_text(snippet)
    snippets.append({'path':path,'first_line':text[:a].count('\n')+1,'sha256':hashlib.sha256(snippet.encode()).hexdigest()})
    return snippet
h='import Mathlib\nimport Selvage.BindingGame\nnamespace Minidregg.Selvage\n'
h+=cut('Selvage/Rbr.lean','noncomputable def uniformProb','/-! ## Transcripts')
h+=cut('Selvage/Depth.lean','section UniformProb','/-- The finite union bound over `Fin m`')+'\nend UniformProb\n'
h+=cut('Selvage/Commitment.lean','structure OpeningScheme','/-- **A binding vector commitment')
h+=cut('Selvage/CollisionResistanceROM.lean','def roScheme','/-- A retained `PositionEquivocation`')
h+='\nend Minidregg.Selvage\n'
h+=cut('Selvage/AuditSampling.lean','namespace Minidregg.Selvage','/-! ## 5. Cost:')+'\nend Minidregg.Selvage\n'
a=(base/'source/Selvage/BindingBudget.lean').read_text()
h+=a[a.index('namespace Minidregg.Selvage'):]
p=base/'build/AdapterSourceCheck.lean';p.write_text(h)
(base/'adapter-source-slices.json').write_text(json.dumps(snippets,indent=2)+'\n')
paths=[base/'build',root/'.lake/build/lib/lean']+list((root/'.lake/packages').glob('*/.lake/build/lib/lean'))
env=dict(os.environ,LEAN_PATH=':'.join(map(str,paths)))
cmd=['/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean','-o',str(base/'build/AdapterSourceCheck.olean'),str(p)]
proc=subprocess.Popen(cmd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(base/'build-adapter.pid').write_text(str(proc.pid)+'\n')
output,_=proc.communicate()
(base/'build-adapter.log').write_text('COMMAND '+repr(cmd)+'\n'+output+'\nEXIT '+str(proc.returncode)+'\n')
if proc.returncode==0:
 assert a==(base/'source/Selvage/BindingBudget.lean').read_text(), 'Adapter changed during compilation'
 assert manifest['source_sha256']==hashlib.sha256((base/'source/Selvage/BindingGame.lean').read_bytes()).hexdigest(), 'Core changed during adapter check'
 assert manifest['olean_sha256']==hashlib.sha256((base/'build/Selvage/BindingGame.olean').read_bytes()).hexdigest(), 'Imported core artifact changed'
 (base/'adapter-build-manifest.json').write_text(json.dumps({'adapter_sha256':hashlib.sha256((base/'source/Selvage/BindingBudget.lean').read_bytes()).hexdigest(),'core_source_sha256':manifest['source_sha256'],'harness_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'source_slices':snippets},indent=2)+'\n')
print(output); print('exit',proc.returncode)
raise SystemExit(proc.returncode)
