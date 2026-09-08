from pathlib import Path
import subprocess,json,hashlib,re,tempfile
out=Path(__file__).resolve().parent
repo=Path('/tmp/minidregg-full-ud-babybear-20260908')
name='Selvage/BabyBearFullUD.lean'
p=repo/name
source=p.read_bytes();sha=hashlib.sha256(source).hexdigest()
check=json.loads((out/'logs/bridge-pins-01.json').read_text())
assert check['exit_code']==0 and check['source_unchanged'] and check['source_sha256']==sha
s=source.decode();code=re.sub(r'/\-.*?\-/','',s,flags=re.S)
declarations=re.findall(r'(?m)^theorem\s+([^\s(:]+)',code)
pins=re.findall(r'#print axioms\s+([^\s]+)',code)
assert sorted(declarations)==sorted(x.split('.')[-1]for x in pins)
core=out.parent/'full_ud/manifest.json';core_manifest=json.loads(core.read_text())
for m in core_manifest['modules']:
 assert hashlib.sha256((repo/m['path']).read_bytes()).hexdigest()==m['sha256'],m['path']
(out/'BabyBearFullUD.lean').write_bytes(source)
r=subprocess.run(['git','diff','--no-index','--','/dev/null',str(p)],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
assert r.returncode==1,r.stderr
patch=out/'babybear-full-ud.patch'
patch.write_text(r.stdout.replace('a'+str(repo)+'/','a/').replace('b'+str(repo)+'/','b/'))
with tempfile.TemporaryDirectory(prefix='babybear-full-ud-apply-')as td:
 for cmd in [['git','init','-q'],['git','apply','--check',str(patch)],['git','apply',str(patch)]]:
  r=subprocess.run(cmd,cwd=td,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  assert r.returncode==0,r.stdout
 assert (Path(td)/name).read_bytes()==source
(out/'logs/patch-apply.log').write_text('PASS: clean git apply --check, git apply, exact source byte equality.\n')
b=subprocess.run(['bash','scripts/check-import-boundary.sh'],cwd=repo,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
(out/'logs/import-boundary.log').write_text(b.stdout);assert b.returncode==0,b.stdout
entry={'name':'full_ud_babybear','root':'../proof_frontier/2026-09-08/formal/full_ud_babybear','patch':'../proof_frontier/2026-09-08/formal/full_ud_babybear/babybear-full-ud.patch','expected_pins':len(pins),'source_files':{name:'../proof_frontier/2026-09-08/formal/full_ud_babybear/BabyBearFullUD.lean'}}
(out/'integration_entry.json').write_text(json.dumps(entry,indent=2)+'\n')
record={'base_commit':subprocess.check_output(['git','rev-parse','HEAD'],cwd=repo,text=True).strip(),'checkout':str(repo),'source_file':name,'source_sha256':sha,'lines':len(s.splitlines()),'declarations':declarations,'pins':pins,'expected_pins':len(pins),'patch_sha256':hashlib.sha256(patch.read_bytes()).hexdigest(),'check':check,'field_source_sha256':hashlib.sha256((repo/'Selvage/BabyBearExt4.lean').read_bytes()).hexdigest(),'core_manifest_sha256':hashlib.sha256(core.read_bytes()).hexdigest(),'frozen_core_all_14_hashes_unchanged':True,'external_queries':0}
(out/'provenance.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items()if k not in ['check','declarations','pins']},indent=2))
