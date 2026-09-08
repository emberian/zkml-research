from pathlib import Path
import hashlib,json,re,subprocess,tempfile,time,difflib,shutil,importlib.util
out=Path(__file__).resolve().parent
repo=Path('/tmp/minidregg-commitment-failure-successor-20260908')
research=out.parent
main=Path('/Users/ember/dev/minidregg')
base='6937394e1dc2c2aaff986c7d4b3a258aca5d16fd'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def save(p,v):p.write_text(json.dumps(v,indent=2)+'\n')
names=json.loads((out/'declaration-names.json').read_text())
mods=[Path(m.replace('.','/')+'.lean')for m in names]
modules=[]
for i,rel in enumerate(mods,1):
 p=repo/rel;s=p.read_text();n=names[str(rel.with_suffix('')).replace('/','.')]
 c=json.loads((out/'checks'/f'final-{i:02d}.json').read_text())
 assert c['exit_code']==0 and c['source_unchanged'] and c['source_sha256']==sha(p)
 assert Path(c['log']).read_bytes()==b''
 assert len(n)==s.count('#print axioms')==s.count('#guard_msgs')
 assert not re.search(r'\b(sorry|sorryAx|axiom|native_decide)\b',s)
 for message in re.findall(r'/-- info: (.*?) -/',s,re.S):
  assert ('does not depend on any axioms' in message or set(re.search(r'depends on axioms: \[(.*?)\]',message).group(1).split(', ')) <= {'propext','Classical.choice','Quot.sound'})
 dest=out/'src'/rel;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dest)
 loc={m.group(1):s[:m.start()].count('\n')+1 for m in re.finditer(r'^(?:theorem|lemma)\s+(\S+)',s,re.M)}
 modules.append({'path':str(rel),'sha256':sha(p),'lines':len(s.splitlines()),'theorems':len(n),'guards':s.count('#guard_msgs'),'check':c,'locations':loc})
# Stop at base declarations, recurse through selected frozen research imports.
tracked=set(subprocess.check_output(['git','ls-tree','-r','--name-only',base],cwd=repo,text=True).splitlines())
raw=subprocess.check_output(['rg','--files',str(research)],text=True).splitlines()
candidates={}
for t in raw:
 p=Path(t)
 if p.suffix=='.lean' and out not in p.parents:candidates.setdefault(p.name,[]).append(p)
seen=set();deps={}
def visit(rel):
 if str(rel) in seen:return
 seen.add(str(rel));p=repo/rel
 for mod in re.findall(r'^import\s+(\S+)',p.read_text(),re.M):
  if mod.startswith(('Mathlib','Lean','Std','Init')):continue
  child=Path(mod.replace('.','/')+'.lean')
  if child in mods:visit(child);continue
  if str(child) in deps:continue
  cp=repo/child;h=sha(cp)
  if str(child) in tracked:
   mp=main/child;assert mp.exists() and sha(mp)==h
   deps[str(child)]={'kind':'base','sha256':h,'main_source':str(mp),'main_bytes_match':True}
  else:
   matches=[x for x in candidates.get(child.name,[]) if sha(x)==h]
   assert matches,(child,h)
   deps[str(child)]={'kind':'frozen_research_dependency','sha256':h,'matching_source':str(matches[0])}
   visit(child)
for m in mods:visit(m)
save(out/'DEPENDENCIES.json',deps)
# Complete additive patch; no predecessor edits.
patch=out/'commitment-failure.patch';chunks=[]
for rel in sorted(mods):
 s=(out/'src'/rel).read_text()
 chunks.append('diff --git a/'+str(rel)+' b/'+str(rel)+'\nnew file mode 100644\n')
 chunks.extend(difflib.unified_diff([],s.splitlines(keepends=True),fromfile='/dev/null',tofile='b/'+str(rel)))
patch.write_text(''.join(chunks))
replay=Path(tempfile.mkdtemp(prefix='commitment-failure-replay-'))
cmd=['git','apply',str(patch)]
r=subprocess.run(cmd,cwd=replay,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
found=sorted(str(x.relative_to(replay))for x in replay.rglob('*')if x.is_file())
assert r.returncode==0 and found==sorted(map(str,mods)),(r.stdout,found)
matches={str(m):(replay/m).read_bytes()==(out/'src'/m).read_bytes()for m in mods}
assert all(matches.values())
pr={'command':cmd,'cwd':str(replay),'exit_code':r.returncode,'output':r.stdout,'exact_target_files':found,'all_exact_bytes':True,'file_matches':matches}
save(out/'checks'/'patch.json',pr)
cmd=['bash','scripts/check-import-boundary.sh'];start=time.time()
r=subprocess.run(cmd,cwd=repo,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
assert r.returncode==0,r.stdout
ig={'command':cmd,'cwd':str(repo),'exit_code':r.returncode,'elapsed_s':time.time()-start,'output':r.stdout}
save(out/'checks'/'import-boundary.json',ig);(out/'checks'/'import-boundary.log').write_text(r.stdout)
# Pin selected predecessor evidence and verify all one-round inputs stayed frozen.
pred=research/'finite_schedule_successor';pm=json.loads((pred/'MANIFEST.json').read_text())
for source_package in ['constructive_successor','multi_round_successor','finite_schedule_successor']:
 frozen=research/source_package
 frozen_manifest=json.loads((frozen/'MANIFEST.json').read_text())
 for row in frozen_manifest['modules']:
  assert sha(frozen/'src'/row['path'])==row['sha256']==sha(repo/row['path'])
evidence=pm['source_evidence']+[{'path':str(pred/'MANIFEST.json'),'sha256':sha(pred/'MANIFEST.json')},{'path':str(pred/pm['patch']),'sha256':sha(pred/pm['patch'])}]
evidence += [{'path':str(research/'efficient_root_binding/AUDIT.md'),'sha256':sha(research/'efficient_root_binding/AUDIT.md')}]
for row in evidence:assert sha(Path(row['path']))==row['sha256']
entry={'name':'commitment_failure_successor','root':'../proof_frontier/2026-09-08/commitment_failure_successor','patch':'../proof_frontier/2026-09-08/commitment_failure_successor/commitment-failure.patch','expected_pins':sum(x['guards']for x in modules),'source_files':{str(m):'../proof_frontier/2026-09-08/commitment_failure_successor/src/'+str(m)for m in sorted(mods)}}
save(out/'integration_entry.json',entry)
manifest={'scope':'classical adaptive fresh typed-query collision/late-hit reduction; generated scalar supplied-verifier logs; actual five-round BabyBear soundness with priced observed Failure','base_commit':base,'checkout':str(repo),'lean_toolchain':(repo/'lean-toolchain').read_text().strip(),'modules':modules,'module_count':len(modules),'theorem_count':sum(m['theorems']for m in modules),'all_exact_guarded_checks_pass':True,'standard_axioms_only':True,'patch':patch.name,'patch_sha256':sha(patch),'dependencies':deps,'source_evidence':evidence,'import_gate':ig,'patch_replay':pr,'broad_rebuild_performed':False,'independent_review_campaign_performed':False,'new_web_queries':0,'new_scry_sql_queries':0,'predecessors_preserved':True,'artifact_sha256':{str(p.relative_to(out)):sha(p)for p in [out/'README.md',out/'STATUS.md',out/'NEXT.md',out/'DEPENDENCIES.json',out/'declaration-names.json',out/'integration_entry.json',out/'run_lean.py',out/'pin_all.py',out/'finalize.py',out/'final_checks.py',out/'probe.lean',out/'checks/probe.json',out/'checks/probe.log']}}
probe=json.loads((out/'checks/probe.json').read_text());assert probe['exit_code']==0 and probe['source_sha256']==sha(out/'probe.lean')
assert probe['output']=='true\ntrue\n(true, false, 44)\n',probe
manifest['executable_probe']=probe
save(out/'MANIFEST.json',manifest)
print(json.dumps({'patch_sha256':sha(patch),'manifest_sha256':sha(out/'MANIFEST.json'),'module_count':len(modules),'theorems':manifest['theorem_count'],'lines':sum(m['lines']for m in modules),'dependencies':len(deps),'patch_replay':r.returncode},indent=2))
