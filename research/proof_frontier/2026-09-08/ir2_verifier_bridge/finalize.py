from pathlib import Path
import hashlib,json,re,subprocess,sys,importlib.util,tempfile
from fractions import Fraction
from decimal import Decimal,getcontext
out=Path(__file__).resolve().parent
repo=Path('/tmp/minidregg-ir2-verifier-bridge-20260908')
mods=['Theory/P3BarycentricInterpolation.lean','Selvage/FiniteModuloSampling.lean','Selvage/BabyBearModuloSampling.lean','Selvage/Ir2FriSchedule.lean','Selvage/Ir2FriConsistency.lean','Selvage/P3NativeFoldRows.lean','Selvage/Ir2FriCosetRows.lean','Selvage/Ir2FriModel.lean','Selvage/Ir2FriProjection.lean','Selvage/Ir2FriNativeRows.lean','Selvage/Ir2FriNativeEvent.lean','Selvage/Ir2FriSoundness.lean','Selvage/Ir2FriWitnesses.lean']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
spec=importlib.util.spec_from_file_location('c','/Users/ember/dev/zkml-research/research/learn_infer_only/experiments/integration/check_all_formal.py');c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
files={};patch='';total=0;deps={}
for m in mods:
 p=repo/m;s=p.read_text();ns=c.qualified_declarations(c.stripped_lean(s));pins=re.findall(r'^#print axioms (\S+)',s,re.M)
 assert sorted(pins)==sorted(n['qualified_name']for n in ns),(m,ns,pins)
 assert not re.search(r'\b(?:sorry|native_decide)\b|^\s*axiom\s',c.stripped_lean(s),re.M),m
 total+=len(pins)
 dst=out/'src'/m;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(p.read_bytes())
 files[m]={'sha256':sha(dst),'pins':len(pins),'lines':len(s.splitlines())}
 patch+=f'diff --git a/{m} b/{m}\nnew file mode 100644\n--- /dev/null\n+++ b/{m}\n@@ -0,0 +1,{len(s.splitlines())} @@\n'+''.join('+'+l+'\n'for l in s.splitlines())
 for imp in re.findall(r'^import (\S+)',s,re.M):
  ip=imp.replace('.','/')+'.lean'
  if not imp.startswith('Mathlib') and ip not in mods:deps[ip]={'sha256':sha(repo/ip)}
patchpath=out/'ir2-verifier-bridge.patch';patchpath.write_text(patch)
checks=[json.loads(p.read_text())for p in sorted((out/'checks').glob('final-*.json'))]
assert len(checks)==7,len(checks)
for rec in checks:
 assert rec['exit_code']==0 and rec['source_unchanged']
 assert Path(rec['log']).read_text()==''
 assert rec['source_sha256']==sha(repo/rec['command'][-1])
children={n:json.loads((out/n/'CHECKS.json').read_text())for n in ['query_sampling','schedule','native_rows']}
r=subprocess.run(['bash','scripts/check-import-boundary.sh'],cwd=repo,text=True,capture_output=True)
assert r.returncode==0,(r.stdout,r.stderr)
(out/'checks/import-boundary.log').write_text(r.stdout+r.stderr)
with tempfile.TemporaryDirectory(prefix='ir2-patch-check-') as temp:
 rr=subprocess.run(['git','apply',str(patchpath)],cwd=temp,text=True,capture_output=True)
 assert rr.returncode==0,(rr.stdout,rr.stderr)
 assert all(sha(Path(temp)/m)==v['sha256']for m,v in files.items())
p=2013265921;b=Fraction(131064,p**4)+(Fraction(p-1,p)*Fraction(3,5)+Fraction(1,p))**38
getcontext().prec=50
result={'claim_status':'[EXECUTED]','isolate':str(repo),'base_git_commit':'6937394e1dc2c2aaff986c7d4b3a258aca5d16fd','lean_version':'4.30.0','patch_sha256':sha(patchpath),'module_count':len(mods),'pin_count':total,'source_files':files,'own_final_checks':checks,'retained_child_checks':{n:{'path':n+'/CHECKS.json','sha256':sha(out/n/'CHECKS.json')}for n in children},'direct_predecessor_imports':deps,'import_gate':{'command':['bash','scripts/check-import-boundary.sh'],'exit_code':r.returncode,'log':'checks/import-boundary.log'},'patch_replay':'PASS: additive exact-source reconstruction in empty temporary directory','forbidden_tokens':'PASS: no sorry, axiom declaration, native_decide in stripped source','q38_arithmetic':{'instrument':'Python fractions.Fraction; Decimal at precision50','theta':'2/5','prime':p,'challenge_numerator':131064,'exact_numerator':str(b.numerator),'exact_denominator':str(b.denominator),'decimal':str(Decimal(b.numerator)/Decimal(b.denominator))},'scope':'Individual changed-module checks; no broad rebuild or arbitrary Rust proof refinement claim'}
(out/'CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
prefix='../proof_frontier/2026-09-08/ir2_verifier_bridge'
(out/'integration_entry.json').write_text(json.dumps({'name':'ir2_verifier_bridge','root':prefix,'patch':prefix+'/ir2-verifier-bridge.patch','expected_pins':total,'source_files':{m:prefix+'/src/'+m for m in mods}},indent=2)+'\n')
(out/'STATUS.md').write_text('[EXECUTED] FROZEN: 13 additive Lean modules, '+str(total)+' exact axiom pins; changed-module checks and import gate pass. `Ir2Fri.native_fresh_38` proves the explicit actual-profile native row/query proximity bound. Canonical admission freshly verifies the saved proof. See README.md for the remaining arbitrary-proof packed extraction, PCS and FS boundaries.\n')
(out/'NEXT.md').write_text('[OPEN] Next substantive bridge: arbitrary canonical packed-MMCS/PCS openings must yield a prefix-fixed extracted alpha-reduced word, or a concrete binding/extraction failure, and false opening claims must imply its farness. The scalar-leaf hash reduction is insufficient without a packed-leaf adapter. FS challenge generation remains a separate obligation. No further parameter tuning, rounds, full rebuild or example expansion is needed for this handoff.\n')
print(json.dumps({'patch_sha256':sha(patchpath),'CHECKS_sha256':sha(out/'CHECKS.json'),'modules':len(mods),'pins':total,'source_head_sha256':files['Selvage/Ir2FriSoundness.lean']['sha256']},indent=2))
