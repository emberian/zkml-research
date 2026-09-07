"""Pin the authorized correction without changing any first-run bytes."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent;PRIOR=ROOT.parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_text())
def main():
 assert not (ROOT/'freeze.json').exists(),'Preserve correction freeze'
 manifest=load(PRIOR/'manifest.json')
 for name,row in manifest['files'].items():assert sha(PRIOR/name)==row['sha256'],name
 prior=load(PRIOR/'freeze.json')
 inputs=load(PRIOR/'issuer_inputs.json');assert [r['record_id'] for r in inputs]==[0,16,32,48,64,80,96,112]
 source=[ROOT/n for n in ['CONTRACT.md','prepare.py','run.py','launch.py']]
 source +=[PRIOR/n for n in ['manifest.json','freeze.json','preflight.py','PROMPT.txt','issuer_inputs.json','teacher_oracle.json','config_diagnostic.json','results.json','raw_outputs.json']]
 diagnostic=load(PRIOR/'config_diagnostic.json');source.append(Path(diagnostic['installed_source_path']))
 assert sha(diagnostic['installed_source_path'])==diagnostic['installed_source_sha256']
 out={'correction':'Disable model-default merging and explicitly select greedy; assert/log actual merged configuration',
  'prior_manifest_sha256':sha(PRIOR/'manifest.json'),'prior_frozen_file_count_verified':len(manifest['files']),
  'model':prior['model'],'model_revision':prior['revision'],'teacher_ids':[r['record_id'] for r in inputs],
  'source_sha256':{str(p):sha(p) for p in source},'new_semantic_prompt_candidates':0,'additional_heldout_inputs':0,
  'corrected_model_attempts_authorized':1,'all_prior_bytes_preserved':True}
 (ROOT/'freeze.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps({'prepared':True,'freeze_sha256':sha(ROOT/'freeze.json'),'prior_files_unchanged':len(manifest['files'])}))
if __name__=='__main__':main()
