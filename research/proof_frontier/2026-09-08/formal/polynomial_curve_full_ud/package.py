from pathlib import Path
import subprocess,json,hashlib,tempfile,importlib.util
out=Path(__file__).resolve().parent
repo=Path('/tmp/minidregg-polynomial-curve-full-ud-20260908')
research=Path('/Users/ember/dev/zkml-research/research')
name='polynomial_curve_full_ud';base='../proof_frontier/2026-09-08/formal/'+name
mods=json.loads((out/'declaration-names.json').read_text())
checker=research/'learn_infer_only/experiments/integration/check_all_formal.py'
spec=importlib.util.spec_from_file_location('root_census',checker);c=importlib.util.module_from_spec(spec);spec.loader.exec_module(c)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
records=[];censuses={};patches=[];source_files={}
for i,(mod,names) in enumerate(mods.items(),1):
 path=mod.replace('.','/')+'.lean';p=repo/path
 tag=f'freeze-{i:02d}';check=json.loads((out/'checks'/f'{tag}.json').read_text())
 assert check['exit_code']==0 and check['source_unchanged'] and check['source_sha256']==sha(p),mod
 assert not (out/'checks'/f'{tag}.log').read_text(),mod
 s=p.read_text();census=c.census(s,mod);censuses[path]=census
 assert census['pin_count']==len(names)
 dest=out/'src'/path;dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(p.read_bytes())
 source_files[path]=base+'/src/'+path
 r=subprocess.run(['git','diff','--no-index','--','/dev/null',str(p)],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
 assert r.returncode==1,r.stderr
 patches.append(r.stdout.replace('a'+str(repo)+'/','a/').replace('b'+str(repo)+'/','b/'))
 records.append({'path':path,'sha256':sha(p),'lines':len(s.splitlines()),'theorem_count':census['theorem_count'],'pin_count':census['pin_count'],'check':check})
old=json.loads((out.parent/'full_ud/manifest.json').read_text())
predecessors={m['path']:m for m in old['modules']}
old_checks=[]
for path,m in predecessors.items():
 if path=='Theory/PolynomialMatrixKernel.lean':continue
 assert sha(repo/path)==m['sha256'],path
 old_checks.append({'path':path,'sha256':m['sha256']})
ks=out.parent/'polynomial_curve_kernel/PolynomialMatrixKernel.lean'
assert sha(ks)=='f510b6cc0c648a3583e3eefa49e283b2186add24d2e4df71f3afeb9b06a3fa91'
assert sha(repo/'Theory/PolynomialMatrixKernel.lean')==sha(ks)
reachable=set();pending=list(mods)
while pending:
 mod=pending.pop()
 if mod in reachable:continue
 reachable.add(mod)
 p=repo/(mod.replace('.','/')+'.lean')
 if not p.is_file():continue
 pending.extend(x for x in c.imports(p.read_text()) if x.startswith(('Theory.','Selvage.')))
deps=[]
for path,m in predecessors.items():
 mod=path[:-5].replace('/','.')
 if mod not in reachable:continue
 dep={'path':path,'sha256':sha(repo/path)}
 if path=='Theory/PolynomialMatrixKernel.lean':
  dep.update(selected_package='polynomial_curve_kernel',replaces_source_sha256=m['sha256'])
 else:dep['selected_package']='frozen full_ud closure'
 deps.append(dep)
patch=out/'polynomial-curve-full-ud.patch';patch.write_text(''.join(patches))
with tempfile.TemporaryDirectory(prefix='curve-full-ud-apply-')as td:
 for cmd in [['git','init','-q'],['git','apply','--check',str(patch)],['git','apply',str(patch)]]:
  r=subprocess.run(cmd,cwd=td,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  assert r.returncode==0,r.stdout
 for path in source_files:assert (Path(td)/path).read_bytes()==(repo/path).read_bytes(),path
(out/'checks/patch-apply.log').write_text('PASS: clean git apply --check, git apply, exact byte equality for ten new source modules.\n')
b=subprocess.run(['bash','scripts/check-import-boundary.sh'],cwd=repo,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(out/'checks/import-boundary.log').write_text(b.stdout);assert b.returncode==0,b.stdout
entry={'name':name,'root':base,'patch':base+'/'+patch.name,'expected_pins':sum(r['pin_count']for r in records),'source_files':source_files,'requires_selected_lane':'polynomial_curve_kernel','umbrella_imports_proposed':['Selvage.CurveFriChallenge','Selvage.CurveFullUDTeeth']}
(out/'integration_entry.json').write_text(json.dumps(entry,indent=2)+'\n')
(out/'integration_census.json').write_text(json.dumps(censuses,indent=2)+'\n')
note=out.parent.parent/'arity_eight_soundness'
source_evidence={'orientation_note':{'path':str(note/'NOTE.md'),'sha256':sha(note/'NOTE.md')},'orientation_erratum':{'path':str(note/'ERRATUM.md'),'sha256':sha(note/'ERRATUM.md')},'source_pins':{'path':str(note/'SOURCES.json'),'sha256':sha(note/'SOURCES.json')},'selected_kernel':{'path':str(ks),'sha256':sha(ks)},'arklib_commit':'22dbd4e836c15a21f68889afa69b7130da04abbb','license':'Apache-2.0 notices retained; LICENSES/ArkLib-Apache-2.0.txt supplied by selected kernel/core predecessors'}
(out/'source-evidence.json').write_text(json.dumps(source_evidence,indent=2)+'\n')
record={'base_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),'checkout':str(repo),'modules':records,'owned_modules':len(records),'owned_lines':sum(r['lines']for r in records),'owned_theorems':sum(r['theorem_count']for r in records),'owned_pins':sum(r['pin_count']for r in records),'patch_sha256':sha(patch),'dependencies':deps,'frozen_predecessor_byte_checks':old_checks,'selected_kernel_source_sha256':sha(ks),'root_census_script_sha256':sha(checker),'exact_guarded_checks_complete':True,'all_pins_standard_only':True,'umbrella_imports_proposed':entry['umbrella_imports_proposed'],'source_evidence_sha256':sha(out/'source-evidence.json'),'web_queries':0,'scry_sql_queries':0,'combined_umbrella_build':'not run by this lane; root owns integration'}
(out/'manifest.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items()if k not in ['modules','dependencies','frozen_predecessor_byte_checks']},indent=2))
