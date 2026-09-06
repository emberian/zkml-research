#!/usr/bin/env python3
"""Package/check the public window patch; all outputs remain in its owned overlay."""
from pathlib import Path
import difflib,hashlib,json,os,re,shutil,subprocess,time
R=Path(__file__).resolve().parents[3];F=R/'formal/durable_integration/bfv_window';E=Path(__file__).parent
P=R/'formal/durable_integration';C=Path('/Users/ember/dev/minidregg');B=F/'build';stage=B/'review';stage.mkdir(exist_ok=True)
files=['Theory/CiphertextWindow.lean','Assurance/CiphertextWindowCell.lean','Assurance/CiphertextWindowWitness.lean']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd,cwd,env=None):
 t=time.time();p=subprocess.run([str(x) for x in cmd],cwd=cwd,env=env,capture_output=True,text=True)
 rec=dict(command=[str(x) for x in cmd],cwd=str(cwd),exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr,elapsed_seconds=time.time()-t)
 print(' '.join(str(x) for x in cmd),p.returncode,p.stdout,p.stderr,flush=True);return rec
inventory={};deps={};patch=''
for rel in files:
 p=F/rel;rec=json.loads(sorted(E.glob('lean_'+p.stem+'_*.json'))[-1].read_text())
 assert rec['exit_code']==0 and rec['source_sha256']==sha(p) and rec['inputs_unchanged']
 assert rec['olean_sha256']==sha(B/Path(rel).with_suffix('.olean'))
 s=p.read_text();names=re.findall(r'^theorem (\w+)',s,re.M);pins=re.findall(r'^#guard_msgs.*#print axioms (\S+)',s,re.M)
 assert names==pins
 banned=re.compile(r'\b(?:sorry|sorryAx|axiom|native_decide)\b')
 clean=re.sub(r'/\-.*?\-/','',s,flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
 assert not banned.search(clean)
 assert all(banned.search(x) for x in ['theorem bad : False := by sorry','axiom bad : False','by native_decide'])
 inventory[rel]=dict(source_sha256=sha(p),theorems=len(names),pins=len(pins),forbidden_tokens=[])
 for mod in re.findall(r'^import (\S+)',s,re.M):
  suffix=Path(mod.replace('.','/'));sources=[F/suffix.with_suffix('.lean'),P/suffix.with_suffix('.lean'),C/suffix.with_suffix('.lean')]
  sources.extend(Path(x)/suffix.with_suffix('.lean') for x in ['/Users/ember/dev/minidregg/.lake/packages/mathlib'])
  source=next((x for x in sources if x.exists()),None)
  oleans=[Path(x)/suffix.with_suffix('.olean') for x in rec['lean_path'].split(':')];olean=next(x for x in oleans if x.exists())
  deps[mod]=dict(source_path=str(source) if source else None,source_sha256=sha(source) if source else None,olean_path=str(olean.resolve()),olean_sha256=sha(olean))
 patch+=''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/'+rel))
checks=[];env=dict(os.environ,LEAN_PATH=rec['lean_path']);lean=rec['command'][0]
for root,newimports in [('Theory.lean',['Theory.CiphertextWindow']),('Assurance.lean',['Assurance.CiphertextWindowCell','Assurance.CiphertextWindowWitness'])]:
 old=(C/root).read_text();new=old+'\n'+'\n'.join('import '+m for m in newimports)+'\n'
 (stage/root).write_text(new)
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+root,tofile='b/'+root))
 checks.append(run([lean,stage/root],stage,env))
patchpath=F/'minidregg-ciphertext-window.patch';patchpath.write_text(patch)
checks.append(run(['git','apply','--check',patchpath],C))
# The real boundary instrument runs on a full copied Theory/Selvage corpus,
# with this actual patch applied there. Nothing is written through symlinks.
full=stage/'full_source';full.mkdir(exist_ok=True)
for ns in ['Theory','Selvage','Assurance']:
 shutil.copytree(C/ns,full/ns,dirs_exist_ok=True,ignore=shutil.ignore_patterns('*.olean','*.ilean'))
for root in ['Theory.lean','Selvage.lean','Assurance.lean']:shutil.copy2(C/root,full/root)
(full/'scripts').mkdir(exist_ok=True);shutil.copy2(C/'scripts/check-import-boundary.sh',full/'scripts/check-import-boundary.sh')
for rel in files:
 target=full/rel
 if target.exists():target.unlink()
checks.append(run(['git','apply','--unsafe-paths',patchpath],full))
assert all((full/x).read_bytes()==(F/x).read_bytes() for x in files)
checks.append(run(['bash',full/'scripts/check-import-boundary.sh'],full))
checks.append(run(['bash',C/'scripts/check-import-boundary.sh'],C))
checks.append(run(['git','rev-parse','HEAD'],C))
frozen={
 'Assurance/ResidentDurableIntegration.lean':'80239c7fbc060c6f0c60a4a085c78b078987b46ffbf7b17017f3f92af57c022a',
 'Assurance/ResidentDurableCollision.lean':'b410206075a03338ef6d569c777c2d2a2420f3ddc8f3280cfcf6d062685a028c',
 'minidregg-durable-integration.patch':'945d70ab4a7504f25bbc598f70951fae8f1a1a5318459a396bfe1fcbf8e57a5a',
 'Compiler/ResidentEmaCertificate.lean':'f6b9c07240bc4f5341a8412b7bc00a5c8c6e19e17743d86c3cecc8b3ea72588d',
 'Assurance/ResidentEmaCell.lean':'68cdb084b839364328bc0717c5b6fa763a8342efbfc4244c02181603af4a9437',
 'Assurance/ResidentEmaRelease.lean':'470a6b5daf54cbd373799fa0b075137d06f5a115395d07ecbabfac130efbc8ee',
 'Assurance/ResidentEmaWitness.lean':'e412cad31eba9eac302a597239fcaee14987b79db6b134c0de884e2ca74f3eeb',
 'minidregg-ema-semantic-bridge.patch':'3f5d9c6895b5a423ce134e586c02141e448052ed559bca0a1aeec707dd99232a'}
assert all(sha(P/x)==h for x,h in frozen.items())
result=dict(source_inventory=inventory,direct_import_dependencies=deps,checks=checks,patch_sha256=sha(patchpath),settled_hashes_preserved=frozen,
 prerequisites=['formal/minidregg-resident-release.patch','formal/durable_integration/minidregg-durable-integration.patch'],
 source_scope='Three new window modules scanned; direct source/olean hashes recorded. Full copied Theory/Selvage plus new patch checked with real boundary script. Prebuilt companion dependencies reused; not rebuilt.')
n=len(list(E.glob('review_*.json')))+1;(E/f'review_{n:02}.json').write_text(json.dumps(result,indent=2)+'\n');(E/'review.json').write_text(json.dumps(result,indent=2)+'\n')
raise SystemExit(int(any(c['exit_code'] for c in checks)))
