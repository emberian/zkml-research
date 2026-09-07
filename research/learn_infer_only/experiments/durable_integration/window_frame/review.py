#!/usr/bin/env python3
from pathlib import Path
import difflib,hashlib,json,os,re,shutil,subprocess,time
R=Path(__file__).resolve().parents[3];E=Path(__file__).parent;F=R/'formal/durable_integration/window_frame';B=F/'build';C=Path('/Users/ember/dev/minidregg')
files=['Assurance/CiphertextWindowFrame.lean','Assurance/CiphertextWindowFrameWitness.lean'];stage=B/'review';stage.mkdir(exist_ok=True)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checks=[]
def run(cmd,cwd,env=None):
 t=time.time();p=subprocess.run([str(x) for x in cmd],cwd=cwd,env=env,capture_output=True,text=True);rec=dict(command=[str(x) for x in cmd],cwd=str(cwd),exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr,elapsed_seconds=time.time()-t);checks.append(rec);print(p.returncode,p.stdout,p.stderr,flush=True)
patch='';inventory={};deps={}
for rel in files:
 p=F/rel;s=p.read_text();rec=json.loads(sorted(E.glob('lean_'+p.stem+'_*.json'))[-1].read_text());assert rec['exit_code']==0 and rec['inputs_unchanged'] and rec['source_sha256']==sha(p) and rec['olean_sha256']==sha(B/Path(rel).with_suffix('.olean'))
 names=re.findall(r'^theorem (\w+)',s,re.M);pins=re.findall(r'^#guard_msgs.*#print axioms (\w+)',s,re.M);assert names==pins
 banned=re.compile(r'\b(?:sorry|sorryAx|axiom|native_decide)\b');clean=re.sub(r'/\-.*?\-/','',s,flags=re.S);clean=re.sub(r'--[^\n]*','',clean);assert not banned.search(clean);assert all(banned.search(x) for x in ['by sorry','axiom bad : False','by native_decide'])
 inventory[rel]=dict(source_sha256=sha(p),pins=len(pins),forbidden_tokens=[])
 for mod in re.findall(r'^import (\S+)',s,re.M):
  suffix=Path(mod.replace('.','/'));sources=[base/suffix.with_suffix('.lean') for base in [F,R/'formal/durable_integration/bfv_window',C]];source=next(x for x in sources if x.exists());olean=next(Path(x)/suffix.with_suffix('.olean') for x in rec['lean_path'].split(':') if (Path(x)/suffix.with_suffix('.olean')).exists());deps[mod]=dict(source_sha256=sha(source),source_path=str(source),olean_path=str(olean.resolve()),olean_sha256=sha(olean))
 patch+=''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/'+rel))
old=(C/'Assurance.lean').read_text();new=old+'\n'+'\n'.join('import '+Path(x).with_suffix('').as_posix().replace('/','.') for x in files)+'\n';(stage/'Assurance.lean').write_text(new)
patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/Assurance.lean',tofile='b/Assurance.lean'))
patchpath=F/'minidregg-window-frame.patch';patchpath.write_text(patch)
run([rec['command'][0],stage/'Assurance.lean'],stage,dict(os.environ,LEAN_PATH=rec['lean_path']))
run(['git','apply','--check',patchpath],C)
full=stage/'full_source';full.mkdir(exist_ok=True)
for ns in ['Theory','Selvage','Assurance']:shutil.copytree(C/ns,full/ns,dirs_exist_ok=True)
for root in ['Theory.lean','Selvage.lean','Assurance.lean']:shutil.copy2(C/root,full/root)
(full/'scripts').mkdir(exist_ok=True);shutil.copy2(C/'scripts/check-import-boundary.sh',full/'scripts/check-import-boundary.sh')
for rel in files:
 if (full/rel).exists():(full/rel).unlink()
run(['git','apply','--unsafe-paths',patchpath],full);assert all((full/x).read_bytes()==(F/x).read_bytes() for x in files)
run(['bash',full/'scripts/check-import-boundary.sh'],full)
frozen={'Theory/CiphertextWindow.lean':'ad2e496b8f8d1fbf7125cf6be9306a97c9933a66c7882066d087a2b04c8605ee','Assurance/CiphertextWindowCell.lean':'7b215707ee631a3d04854f6dd2fd044511dbcfd6d59b21c602380ff1d4c8a77d','Assurance/CiphertextWindowWitness.lean':'8503df829d5f5bcd9aa13bb5febd578b533dd3f8e8a075a687fa4fd30ffe9d92','minidregg-ciphertext-window.patch':'630d2fa6c0ec0c2b049fcc0affeca6c9b22a5a264cf638890780e9e0fe5eb4eb'}
assert all(sha(R/'formal/durable_integration/bfv_window'/p)==h for p,h in frozen.items())
result=dict(inventory=inventory,direct_import_dependencies=deps,checks=checks,patch_sha256=sha(patchpath),frozen_window44_preserved=frozen,prerequisites=['resident-release','durable-integration','ciphertext-window'],scope='Two new Assurance modules; reused dependency oleans; no clean whole-tree build or implementation-refinement claim')
n=len(list(E.glob('review_*.json')))+1;(E/f'review_{n:02}.json').write_text(json.dumps(result,indent=2)+'\n');(E/'review.json').write_text(json.dumps(result,indent=2)+'\n');raise SystemExit(int(any(x['exit_code'] for x in checks)))
