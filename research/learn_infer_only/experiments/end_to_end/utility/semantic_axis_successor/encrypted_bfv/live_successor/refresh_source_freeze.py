"""One prelaunch source correction; preserve the same private fixture and initial freeze."""
import ast,hashlib,json,tarfile
from pathlib import Path
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_bytes())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,x):Path(p).write_text(json.dumps(x,sort_keys=True,indent=2)+'\n')
def main():
 assert not (ROOT/'run_started.json').exists() and not (ROOT/'runtime/run').exists()
 assert not list((ROOT/'runtime').rglob('score_started.json'))
 freeze=load(ROOT/'freeze.json');assert 'source_revision' not in freeze
 previous=sha(ROOT/'freeze.json');assert previous==sha(ROOT/'prelaunch_revision_001/freeze.json')
 allowed={str(ROOT/n) for n in ['CONTRACT.md','validate.py','run.py','public_verify.py']}
 changed={p for p,h in freeze['public_source_dependencies'].items() if sha(p)!=h}
 assert changed==allowed,changed
 for p in sorted(ROOT.glob('*.py')):ast.parse(p.read_text())
 for p in changed:
  assert sha(ROOT/'prelaunch_revision_001'/Path(p).name)==freeze['public_source_dependencies'][p]
  freeze['public_source_dependencies'][p]=sha(p)
 freeze['public_source_dependencies'][str(Path(__file__).resolve())]=sha(__file__)
 for p,h in freeze['snapshot_source_pins'].items():assert sha(ROOT/'runtime/e2e'/p)==h
 for p,h in freeze['query_vector_pins'].items():assert sha(ROOT/'runtime/public_query_inputs'/p)==h
 prepared=ROOT/'runtime/.private/prepared';pf=load(prepared/'freeze.json')
 assert pf==load(prepared/'freeze_v001.json')
 assert sha(ROOT/'runtime/.private/input.json')==pf['private_input_sha256']
 assert sha(prepared/'issuer_inputs.json')==pf['source_sha256'][str(prepared/'issuer_inputs.json')]
 pf['source_sha256'].update(freeze['public_source_dependencies'])
 freeze.update({'source_revision':2,'previous_freeze_sha256':previous,'same_private_input_and_prompts':True,
                'prelaunch_changes':['query dictionary omission-scope correction','descendant process-group cleanup','model posthash before private gate']})
 dump(prepared/'freeze.json',pf);dump(ROOT/'freeze.json',freeze)
 reports=ROOT/'reports/run001';dump(reports/'frontend_dependencies.json',freeze['public_source_dependencies'])
 with tarfile.open(reports/'source_snapshot.tar.gz','w:gz') as archive:
  for name in sorted(freeze['snapshot_source_pins']):
   if name!='resident-crypto':archive.add(ROOT/'runtime/e2e'/name,arcname=name)
  for name in ['issue_semantic_text.py','encoder/common.py','encoder/score.py','encoder_inventory.json','CONTRACT.md']:
   archive.add(ROOT/name,arcname='semantic_frontend/'+name)
  archive.add(ROOT.parents[2]/'semantic_axis_selection/prompts.json',arcname='semantic_frontend/public_framing_definitions.json')
 result={'ok':True,'source_revision':2,'previous_freeze_sha256':previous,'freeze_sha256':sha(ROOT/'freeze.json'),
         'same_private_input_and_prompts':True,'model_forwards':0,'crypto_calls':0,
         'changed_sources':sorted(changed),'public_source_dependencies':len(freeze['public_source_dependencies'])}
 dump(ROOT/'source_revision.json',result);print(json.dumps(result,indent=2))
if __name__=='__main__':main()
