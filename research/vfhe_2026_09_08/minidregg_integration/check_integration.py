#!/usr/bin/env python3
"""Apply the patch in owned scratch copies, then compile new import glue only."""
from pathlib import Path
import subprocess,json,os,time,hashlib,sys
ROOT=Path(__file__).resolve().parent;MAIN=Path('/Users/ember/dev/minidregg')
provenance=json.loads((ROOT/'PROVENANCE.json').read_text());base=provenance['base_commit']
sha=lambda b:hashlib.sha256(b).hexdigest()
patch=ROOT/'minidregg-fhe-arithmetic.patch'
base_root=subprocess.check_output(['git','show',f'{base}:Compiler.lean'],cwd=MAIN)
dirty_root=(MAIN/'Compiler.lean').read_bytes()
anchor=next(line for line in base_root.decode().splitlines(keepends=True) if line.startswith('import Compiler.AirModularView '))
hook=next(line for line in (ROOT/'proposal/Compiler.lean').read_text().splitlines(keepends=True) if line.startswith('import Compiler.FheArithmetic '))
records=[]
if '--resume-glue' not in sys.argv:
 for kind,original in [('base',base_root),('dirty',dirty_root)]:
  folder=ROOT/f'check_{kind}';folder.mkdir(exist_ok=False);(folder/'Compiler.lean').write_bytes(original)
  commands=[['git','init','--quiet'],['git','apply','--check',str(patch)],['git','apply',str(patch)]]
  for command in commands:
   r=subprocess.run(command,cwd=folder,text=True,capture_output=True)
   records.append({'kind':kind,'command':command,'cwd':str(folder),'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr})
   assert r.returncode==0,(kind,r.stderr)
  expected=original.decode().replace(anchor,anchor+hook).encode()
  assert (folder/'Compiler.lean').read_bytes()==expected
  for rel,info in provenance['files'].items():
   if rel!='Compiler.lean':assert sha((folder/rel).read_bytes())==info['sha256'],rel
 (ROOT/'patch_application.json').write_text(json.dumps({'checks':records,'all_sources_exact':True,'dirty_root_preserved_except_import':True,
  'base_Compiler_sha256':sha(base_root),'observed_dirty_Compiler_sha256':sha(dirty_root),'patch_sha256':sha(patch.read_bytes())},indent=2)+'\n')

build=ROOT/'build';(build/'Compiler').mkdir(parents=True,exist_ok=True)
reused=[]
for rel,info in provenance['files'].items():
 if not rel.startswith('Compiler/') or info['group']=='integration':continue
 source=Path(info['source']);package=source.parent.parent;name=source.stem
 options=[package/'build/Compiler'/f'{name}.olean',package/'.build/Compiler'/f'{name}.olean',ROOT.parent/'arithmetic_rescale/build/Compiler'/f'{name}.olean']
 present=[p for p in options if p.exists()]
 assert present,(rel,'missing retained olean',list(map(str,options)))
 olean=present[0]
 for p in olean.parent.glob(name+'.*'):
  if p.is_file():
   target=build/'Compiler'/p.name
   if target.exists():assert target.resolve()==p.resolve()
   else:target.symlink_to(p.resolve())
 reused.append({'module':rel.removesuffix('.lean').replace('/','.'),'source':str(source),'retained_olean':str(olean),'resolved_olean':str(olean.resolve())})
(ROOT/'reused_oleans.json').write_text(json.dumps({'scope':'Exact retained completed module artifacts; no dependency recompilation or new artifact audit','modules':reused},indent=2)+'\n')
# Lean resolves the first Compiler namespace directory as one overlay root.
# Link existing base cache members without rebuilding or hashing that cache.
for cached in (MAIN/'.lake/build/lib/lean/Compiler').rglob('*'):
 if cached.is_file():
  target=build/'Compiler'/cached.relative_to(MAIN/'.lake/build/lib/lean/Compiler')
  if not target.exists():
   target.parent.mkdir(parents=True,exist_ok=True);target.symlink_to(cached.resolve())
prior=json.loads((ROOT.parent/'arithmetic_coverage/results/checked_modules.json').read_text())
lean=prior['lean'];lean_path=str(build)+':'+':'.join(prior['lean_path'].split(':')[1:])
env=dict(os.environ,LEAN_PATH=lean_path);checks=[]
for name,cwd,source,output in [
 ('new_umbrella',ROOT/'proposal','Compiler/FheArithmetic.lean',build/'Compiler/FheArithmetic.olean'),
 ('base_compiler_import_glue',ROOT/'proposal','Compiler.lean',build/'Compiler.olean'),
 ('dirty_compiler_import_glue',ROOT/'check_dirty','Compiler.lean',build/'DirtyCompiler.olean')]:
 command=[lean,'-o',str(output),source];started=time.monotonic()
 try:
  run=subprocess.run(command,cwd=cwd,env=env,text=True,capture_output=True,timeout=180)
  stdout,stderr,code=run.stdout,run.stderr,run.returncode
 except subprocess.TimeoutExpired as e:stdout=e.stdout or '';stderr=e.stderr or '';code=124
 if isinstance(stdout,bytes):stdout=stdout.decode()
 if isinstance(stderr,bytes):stderr=stderr.decode()
 (ROOT/f'{name}.stdout').write_text(stdout);(ROOT/f'{name}.stderr').write_text(stderr)
 checks.append({'name':name,'command':command,'cwd':str(cwd),'exit':code,'seconds':time.monotonic()-started,
  'stdout':name+'.stdout','stderr':name+'.stderr'})
 (ROOT/'glue_checks.json').write_text(json.dumps({'lean_path':lean_path,'checks':checks},indent=2)+'\n')
 print(json.dumps(checks[-1]),flush=True)
 if code!=0:break
boundary=subprocess.run(['bash',str(MAIN/'scripts/check-import-boundary.sh')],text=True,capture_output=True)
(ROOT/'import_boundary.log').write_text(boundary.stdout+boundary.stderr)
assert (MAIN/'Compiler.lean').read_bytes()==dirty_root,'main root changed during check; inspect concurrent changes'
print(json.dumps({'patch_application':'PASS','glue_successes':sum(c['exit']==0 for c in checks),'boundary_exit':boundary.returncode,'main_Compiler_unchanged':True}),flush=True)
raise SystemExit(0 if len(checks)==3 and all(c['exit']==0 for c in checks) and boundary.returncode==0 else 1)
