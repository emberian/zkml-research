"""Freeze the additive deterministic adapter and verify its exact source evidence."""
from pathlib import Path
import subprocess,json,hashlib,tempfile,importlib.util
out=Path(__file__).resolve().parent
repo=Path('/tmp/minidregg-efficient-root-opening-20260908')
companion=Path('/Users/ember/dev/minidregg')
research=Path('/Users/ember/dev/zkml-research/research')
base='../proof_frontier/2026-09-08/formal/efficient_root_opening'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
checker=research/'learn_infer_only/experiments/integration/check_all_formal.py'
spec=importlib.util.spec_from_file_location('root_integration_census',checker)
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
path='Selvage/EfficientRootOpening.lean';p=repo/path
check=json.loads((out/'logs/final-freeze.json').read_text())
assert check['exit_code']==0 and check['source_unchanged'] and check['source_sha256']==sha(p)
assert not (out/'logs/final-freeze.log').read_text()
census=module.census(p.read_text(),'Selvage.EfficientRootOpening')
assert census['pin_count']==20 and census['theorem_count']==20,census
(out/'integration_census.json').write_text(json.dumps(census,indent=2)+'\n')
dest=out/'src'/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes())
r=subprocess.run(['git','diff','--no-index','--','/dev/null',str(p)],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
assert r.returncode==1,r.stderr
patch=out/'efficient-root-opening.patch'
patch.write_text(r.stdout.replace('a'+str(repo)+'/','a/').replace('b'+str(repo)+'/','b/'))
with tempfile.TemporaryDirectory(prefix='efficient-opening-apply-')as td:
 for cmd in [['git','init','-q'],['git','apply','--check',str(patch)],['git','apply',str(patch)]]:
  r=subprocess.run(cmd,cwd=td,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  assert r.returncode==0,r.stdout
 assert (Path(td)/path).read_bytes()==p.read_bytes()
(out/'logs/patch-apply.log').write_text('PASS: clean git apply --check, git apply, exact byte equality for the owned source.\n')
b=subprocess.run(['bash','scripts/check-import-boundary.sh'],cwd=repo,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(out/'logs/import-boundary.log').write_text(b.stdout);assert b.returncode==0,b.stdout
locs={'Selvage/BinaryMerkle.lean':{'HashSuite':27,'recompute':73,'openingScheme':134,'recompute_cons_some_iff':156,'accepted_different_values_imply_collision':257},'Selvage/OracleLogExtraction.lean':{'OracleLog':78,'OracleLog.answerOf':92},'Selvage/BinaryLookup.lean':{'binaryAddressBits':28},'Selvage/CorrelatedAgreement.lean':{'close':112}}
deps=[]
for dep,locations in locs.items():
 assert sha(repo/dep)==sha(companion/dep),dep
 deps.append({'path':str(companion/dep),'sha256':sha(companion/dep),'locations':locations,'isolated_copy_identical':True})
frozen={}
for rel in ['efficient_root_binding/AUDIT.md','efficient_root_binding/MANIFEST.json','efficient_root_binding_review/REPORT.md']:
 f=research/'proof_frontier/2026-09-08'/rel
 if not f.exists() and f.name=='MANIFEST.json':f=f.with_name('manifest.json')
 frozen[str(f)]=sha(f)
evidence={'claim_label':'SOURCE','dependencies':deps,'frozen_prior_audit_and_review':frozen,'search':{'corpus':'companion Selvage/OracleLog*.lean and BinaryMerkle.lean','instrument':'rg declarations and extraction/log terms; direct source inspection','scope':'Existing challenge-log / explicit word-preimage extraction does not provide this supplied Merkle reverse-path adapter. New reverse lookup is proved equal to existing answerOf on swapped cells.'},'web_queries':0,'scry_sql_queries':0}
(out/'source-evidence.json').write_text(json.dumps(evidence,indent=2)+'\n')
entry={'name':'efficient_root_opening','root':base,'patch':base+'/'+patch.name,'expected_pins':20,'source_files':{path:base+'/src/'+path}}
(out/'integration_entry.json').write_text(json.dumps(entry,indent=2)+'\n')
record={'base_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),'checkout':str(repo),'modules':[{'path':path,'sha256':sha(p),'lines':len(p.read_text().splitlines()),'theorem_count':20,'pin_count':20,'check':check}],'owned_modules':1,'owned_theorems':20,'owned_pins':20,'patch_sha256':sha(patch),'dependencies':deps,'root_census_script_sha256':sha(checker),'exact_guarded_checks_complete':True,'all_pins_standard_only':True,'companion_read_only':True,'source_evidence_sha256':sha(out/'source-evidence.json'),'web_queries':0,'scry_sql_queries':0}
record['files']={str(f.relative_to(out)):sha(f)for f in sorted(out.rglob('*')) if f.is_file() and f.name!='manifest.json'}
(out/'manifest.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'source_sha256':sha(p),'patch_sha256':sha(patch),'manifest_sha256':sha(out/'manifest.json'),'theorems':20},indent=2))
