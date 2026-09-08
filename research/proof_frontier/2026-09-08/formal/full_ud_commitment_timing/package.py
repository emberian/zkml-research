from pathlib import Path
import subprocess,json,hashlib,re,tempfile,importlib.util
out=Path(__file__).resolve().parent
repo=Path('/tmp/minidregg-full-ud-commitment-timing-20260908')
research=Path('/Users/ember/dev/zkml-research/research')
name='full_ud_commitment_timing'
base='../proof_frontier/2026-09-08/formal/'+name
mods=json.loads((out/'declaration-names.json').read_text())
checker=research/'learn_infer_only/experiments/integration/check_all_formal.py'
spec=importlib.util.spec_from_file_location('root_integration_census',checker)
module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=[];censuses={};patches=[];source_files={}
for i,mod in enumerate(mods,1):
 path='Selvage/'+mod+'.lean';p=repo/path
 tag=f'final-guard-{i:02d}' if i==1 else f'freeze-{i:02d}'
 check=json.loads((out/'logs'/f'{tag}.json').read_text())
 assert check['exit_code']==0 and check['source_unchanged'] and check['source_sha256']==sha(p)
 assert not (out/'logs'/f'{tag}.log').read_text(),mod
 s=p.read_text();census=module.census(s,'Selvage.'+mod);censuses[path]=census
 assert census['pin_count']==len(mods[mod])
 dest=out/'src'/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes())
 source_files[path]=base+'/src/'+path
 r=subprocess.run(['git','diff','--no-index','--','/dev/null',str(p)],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 assert r.returncode==1,r.stderr
 patches.append(r.stdout.replace('a'+str(repo)+'/','a/').replace('b'+str(repo)+'/','b/'))
 records.append({'path':path,'sha256':sha(p),'lines':len(s.splitlines()),'theorem_count':census['theorem_count'],'pin_count':census['pin_count'],'check':check})
core=out.parent/'full_ud/manifest.json';core_manifest=json.loads(core.read_text())
deps=[]
for m in core_manifest['modules']:
 assert sha(repo/m['path'])==m['sha256'],m['path']
 deps.append({'path':m['path'],'sha256':m['sha256'],'frozen_source':'full_ud/manifest.json'})
for folder,file in [('full_ud_babybear','BabyBearFullUD.lean'),('full_ud_sampling_budget','FullUDSamplingBudget.lean')]:
 p=out.parent/folder/file
 assert sha(repo/'Selvage'/file)==sha(p),file
 deps.append({'path':'Selvage/'+file,'sha256':sha(p),'frozen_source':folder+'/'+file})
patch=out/'full-ud-commitment-timing.patch';patch.write_text(''.join(patches))
with tempfile.TemporaryDirectory(prefix='full-ud-timing-apply-')as td:
 for cmd in [['git','init','-q'],['git','apply','--check',str(patch)],['git','apply',str(patch)]]:
  r=subprocess.run(cmd,cwd=td,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  assert r.returncode==0,r.stdout
 for path in source_files:assert (Path(td)/path).read_bytes()==(repo/path).read_bytes(),path
(out/'logs/patch-apply.log').write_text('PASS: clean git apply --check, git apply, exact byte equality for all five source files.\n')
b=subprocess.run(['bash','scripts/check-import-boundary.sh'],cwd=repo,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(out/'logs/import-boundary.log').write_text(b.stdout);assert b.returncode==0,b.stdout
entry={'name':name,'root':base,'patch':base+'/'+patch.name,'expected_pins':sum(r['pin_count']for r in records),'source_files':source_files}
(out/'integration_entry.json').write_text(json.dumps(entry,indent=2)+'\n')
(out/'integration_census.json').write_text(json.dumps(censuses,indent=2)+'\n')
record={'base_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),'checkout':str(repo),'modules':records,'owned_modules':len(records),'owned_lines':sum(r['lines']for r in records),'owned_theorems':sum(r['theorem_count']for r in records),'owned_pins':sum(r['pin_count']for r in records),'patch_sha256':sha(patch),'dependencies':deps,'all_16_frozen_dependency_hashes_unchanged':True,'root_census_script_sha256':sha(checker),'exact_guarded_checks_complete':True,'all_pins_standard_only':True,'umbrella_imports_proposed':['Selvage.FriRootResolutionWitnesses','Selvage.BabyBearFriRootResolution'],'source_evidence_sha256':sha(out/'source-evidence.json'),'web_queries':0,'scry_sql_queries':0}
(out/'manifest.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items()if k not in ['modules','dependencies']},indent=2))
