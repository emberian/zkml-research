#!/usr/bin/env python3
"""Review the second-tranche patch without changing first settled sources."""
from pathlib import Path
import difflib,hashlib,json,os,re,subprocess,time
R=Path(__file__).resolve().parents[3];F=R/'formal/durable_integration';E=Path(__file__).parent
C=Path('/Users/ember/dev/minidregg');B=F/'build';stage=B/'ema_review';stage.mkdir(exist_ok=True)
files=['Compiler/ResidentEmaCertificate.lean','Assurance/ResidentEmaCell.lean',
       'Assurance/ResidentEmaRelease.lean','Assurance/ResidentEmaWitness.lean']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def run(cmd,cwd,env=None):
 t=time.time();p=subprocess.run([str(x) for x in cmd],cwd=cwd,env=env,capture_output=True,text=True)
 rec=dict(command=[str(x) for x in cmd],cwd=str(cwd),exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr,elapsed_seconds=time.time()-t)
 print(' '.join(str(x) for x in cmd),p.returncode,p.stdout,p.stderr,flush=True);return rec
inventory={};deps={};patch=''
for rel in files:
 p=F/rel;checks=sorted(E.glob('lean_'+p.stem+'_*.json'));rec=json.loads(checks[-1].read_text())
 assert rec['exit_code']==0 and rec['source_sha256']==sha(p) and rec['inputs_unchanged']
 assert rec['olean_sha256']==sha(B/Path(rel).with_suffix('.olean'))
 s=p.read_text();names=re.findall(r'^theorem (\w+)',s,re.M);pins=re.findall(r'^#guard_msgs.*#print axioms (\S+)',s,re.M)
 assert len(names)==len(pins)
 banned=re.compile(r'\b(?:sorry|sorryAx|axiom|native_decide)\b')
 # Strip comments before forbidden declaration/tactic scan. Pin comments may mention axioms.
 clean=re.sub(r'/\-.*?\-/','',s,flags=re.S);clean=re.sub(r'--[^\n]*','',clean)
 assert not banned.search(clean)
 # Red-test scanner itself; absence is only about these four parsed source texts.
 assert all(banned.search(x) for x in ['theorem bad : False := by sorry','axiom bad : False','by native_decide'])
 inventory[rel]=dict(source_sha256=sha(p),theorems=len(names),pins=len(pins),custom_axiom_or_sorry_tokens=[])
 for mod in re.findall(r'^import (\S+)',s,re.M):
  source=(F/Path(mod.replace('.','/')).with_suffix('.lean'))
  if not source.exists():source=C/Path(mod.replace('.','/')).with_suffix('.lean')
  olean=B/Path(mod.replace('.','/')).with_suffix('.olean')
  if not olean.exists():olean=C/'.lake/build/lib/lean'/Path(mod.replace('.','/')).with_suffix('.olean')
  deps[mod]=dict(source_path=str(source),source_sha256=sha(source),olean_path=str(olean.resolve()),olean_sha256=sha(olean))
 patch+=''.join(difflib.unified_diff([],s.splitlines(True),fromfile='/dev/null',tofile='b/'+rel))
checks=[];env=dict(os.environ,LEAN_PATH=rec['lean_path']);lean=rec['command'][0]
for root,newimports in [('Compiler.lean',['Compiler.ResidentEmaCertificate']),('Assurance.lean',['Assurance.ResidentEmaCell','Assurance.ResidentEmaRelease','Assurance.ResidentEmaWitness'])]:
 old=(C/root).read_text();new=old+'\n'+'\n'.join('import '+m for m in newimports)+'\n'
 (stage/root).write_text(new)
 patch+=''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+root,tofile='b/'+root))
 checks.append(run([lean,stage/root],stage,env))
patchpath=F/'minidregg-ema-semantic-bridge.patch';patchpath.write_text(patch)
checks.append(run(['git','apply','--check',patchpath],C))
checks.append(run(['bash',C/'scripts/check-import-boundary.sh'],C))
checks.append(run(['git','rev-parse','HEAD'],C))
first={'Assurance/ResidentDurableIntegration.lean':'80239c7fbc060c6f0c60a4a085c78b078987b46ffbf7b17017f3f92af57c022a',
 'Assurance/ResidentDurableCollision.lean':'b410206075a03338ef6d569c777c2d2a2420f3ddc8f3280cfcf6d062685a028c',
 'minidregg-durable-integration.patch':'945d70ab4a7504f25bbc598f70951fae8f1a1a5318459a396bfe1fcbf8e57a5a'}
assert all(sha(F/x)==h for x,h in first.items())
result=dict(source_inventory=inventory,direct_import_dependencies=deps,checks=checks,patch_sha256=sha(patchpath),first_settled_hashes_preserved=first,
 prerequisites=['formal/minidregg-resident-release.patch','formal/durable_integration/minidregg-durable-integration.patch'],
 source_scope='Only the four new EMA modules are scanned; direct source/olean hashes are recorded, not a claim that prebuilt companion oleans were rebuilt here.')
n=len(list(E.glob('review_*.json')))+1;(E/f'review_{n:02}.json').write_text(json.dumps(result,indent=2)+'\n');(E/'review.json').write_text(json.dumps(result,indent=2)+'\n')
raise SystemExit(int(any(c['exit_code'] for c in checks)))
