"""Freeze the corrected-attempt census and costs without another model run."""
import ast,hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent;PRIOR=ROOT.parent
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
save=lambda p,x:Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def main():
 r=load(ROOT/'results.json');a=load(ROOT/'audit.json');prior=load(PRIOR/'manifest.json')
 assert a['audit_passed'] and r['corrected_decoding_contract_verified'] and r['valid_json_count']==0
 for name,row in prior['files'].items():assert sha(PRIOR/name)==row['sha256'],name
 save(ROOT/'costs.json',{'label':'EXECUTED; observed one corrected teacher-only run',
   'model_parameter_count':r['model_parameter_count'],'input_tokens':a['input_tokens'],'generated_tokens':a['generated_tokens'],
   'full_process_wall_seconds':load(ROOT/'run.command.json')['wall_seconds'],
   'cpu_load_wall_seconds':r['cpu_load_wall_seconds'],'transfer_to_mps_wall_seconds':r['transfer_to_mps_wall_seconds'],
   'generation_wall_seconds':r['generation_wall_seconds'],'generation_process_cpu_seconds':r['generation_process_cpu_seconds'],
   'memory_at_end':r['memory_at_end'],'semantic_prompt_tokens_unchanged':load(PRIOR/'freeze.json')['public_instruction_token_count'],
   'attempts_in_this_child':1,'physical_attempts_including_prior':2,'physical_teacher_requests_including_prior':16,
   'unique_teacher_inputs':8,'heldout_inputs':0,'utility_history_runs':0,
   'caveats':['Timings are nested inside total process wall time.','Shared machine; not a controlled speed comparison.',
      'MPS and RSS views overlap and must not be summed.','Strict encoder accepted zero outputs.','No encrypted-source privacy measurement.']})
 files={}
 for p in sorted(ROOT.iterdir()):
  if p.is_file() and p.name!='manifest.json':
   if p.suffix=='.py':ast.parse(p.read_text())
   if p.suffix in ['.py','.md','.json']:assert b'\r\n' not in p.read_bytes()
   files[p.name]={'bytes':p.stat().st_size,'sha256':sha(p)}
 save(ROOT/'manifest.json',{'completed':True,'corrected_actual_mode_verified_greedy':True,'strict_interface_success':False,
   'corrected_attempts':1,'total_teacher_attempts_including_prior':2,'all_prior26_files_unchanged':True,
   'prior_manifest_sha256':sha(PRIOR/'manifest.json'),'heldout_inputs':0,'utility_history_runs':0,
   'command_exit_codes':{s:load(ROOT/f'{s}.command.json')['returncode'] for s in ['prepare','run']},'files':files})
 print(json.dumps({'completed':True,'files':len(files),'manifest_sha256':sha(ROOT/'manifest.json'),
   'report_sha256':sha(ROOT/'REPORT.md'),'prior_manifest_unchanged':True}))
if __name__=='__main__':main()
