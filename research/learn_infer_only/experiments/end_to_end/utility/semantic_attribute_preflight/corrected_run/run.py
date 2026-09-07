"""Exactly one corrected greedy teacher preflight, with actual config telemetry."""
import hashlib,json,os,sys,time
from pathlib import Path
sys.dont_write_bytecode=True
for k in ['HF_HUB_OFFLINE','TRANSFORMERS_OFFLINE']:os.environ[k]='1'
os.environ['TOKENIZERS_PARALLELISM']='false'
START=time.perf_counter();CPUSTART=time.process_time()
ROOT=Path(__file__).resolve().parent;PRIOR=ROOT.parent
sys.path.insert(0,str(PRIOR))
import preflight as first
import torch
from transformers import AutoTokenizer,AutoModelForCausalLM,GenerationConfig
load=first.load;save=first.save;sha=first.sha
def main():
 assert not (ROOT/'results.json').exists(),'No corrected retries'
 freeze=load(ROOT/'freeze.json');prior=load(PRIOR/'freeze.json')
 for p,h in freeze['source_sha256'].items():assert sha(p)==h,p
 manifest=load(PRIOR/'manifest.json')
 for name,row in manifest['files'].items():assert sha(PRIOR/name)==row['sha256'],name
 modelpath=Path(prior['model_path'])
 for name,row in prior['model_files'].items():assert sha(modelpath/name)==row['sha256'],name
 assert torch.backends.mps.is_available(),'No backend fallback'
 torch.set_num_threads(2);torch.set_num_interop_threads(1);torch.manual_seed(7901)
 tok=AutoTokenizer.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False)
 before=first.memory();t=time.perf_counter();cpu=time.process_time()
 model=AutoModelForCausalLM.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False,
  dtype=torch.float16,attn_implementation='eager').eval().requires_grad_(False)
 cpu_loaded=time.perf_counter();cpu_loadcpu=time.process_time()-cpu
 model.to('mps');torch.mps.synchronize();loaded=time.perf_counter();after_load=first.memory()
 generation=GenerationConfig(max_new_tokens=32,do_sample=False,num_beams=1,use_cache=True,
  bos_token_id=model.config.bos_token_id,eos_token_id=model.config.eos_token_id,pad_token_id=tok.pad_token_id)
 effective=[];prepare_bound=model._prepare_generation_config
 def checked_prepare(configuration,use_model_defaults=None,**kwargs):
  actual,model_kwargs=prepare_bound(configuration,use_model_defaults=use_model_defaults,**kwargs)
  mode=actual.get_generation_mode().value
  row={'call_index':len(effective),'explicit_use_model_defaults':use_model_defaults,
    'explicit_do_sample_kwarg':kwargs.get('do_sample'),'effective_generation_mode':mode,
    'effective_configuration':actual.to_dict()}
  effective.append(row);save(ROOT/'effective_configurations.json',effective)
  assert use_model_defaults is False and kwargs.get('do_sample') is False
  assert actual.do_sample is False and mode=='greedy_search'
  assert actual.max_new_tokens==32 and actual.num_beams==1 and actual.use_cache is True
  assert actual.temperature==1.0 and actual.top_p==1.0
  return actual,model_kwargs
 model._prepare_generation_config=checked_prepare
 inputs=load(PRIOR/'issuer_inputs.json');outputs=[]
 with torch.inference_mode():
  for item in inputs:
   tokens=tok([item['rendered_prompt']],add_special_tokens=False,return_tensors='pt')
   assert tokens['input_ids'][0].tolist()==item['token_ids'];tokens=tokens.to('mps');torch.mps.synchronize()
   old_calls=len(effective);t0=time.perf_counter();c0=time.process_time()
   result=model.generate(**tokens,generation_config=generation,use_model_defaults=False,
     do_sample=False,temperature=1.0,top_p=1.0)
   torch.mps.synchronize();finished=time.perf_counter();assert len(effective)==old_calls+1
   ids=result[0,tokens['input_ids'].shape[1]:].cpu().tolist();text=tok.decode(ids,skip_special_tokens=True)
   parsed,error=first.strict_parse(text)
   row={'record_id':item['record_id'],'input_tokens':item['token_count'],'generated_tokens':len(ids),
    'generated_token_ids':ids,'raw_output':text,'parsed':parsed,'parse_error':error,
    'effective_config_call_index':old_calls,'generation_wall_seconds':finished-t0,
    'generation_process_cpu_seconds':time.process_time()-c0,'memory_after_generation':first.memory()}
   outputs.append(row);save(ROOT/'raw_outputs.json',outputs);print(json.dumps(row),flush=True)
 oracle={r['record_id']:r for r in load(PRIOR/'teacher_oracle.json')};valid=0;bits=0;pairs=0
 for row in outputs:
  want=oracle[row['record_id']];got=row['parsed'];correct=[got is not None and got[k]==want[k] for k in ['a','b']]
  valid+=int(got is not None);bits+=sum(correct);pairs+=int(all(correct))
  row['oracle']={'a':want['a'],'b':want['b']};row['attribute_correct']=correct
 assert len(effective)==8
 for name,row in manifest['files'].items():assert sha(PRIOR/name)==row['sha256'],name
 out={'execution_completed':True,'corrected_decoding_contract_verified':True,'model_attempt_in_this_child':1,
  'total_teacher_model_attempts_including_deviating_parent':2,'teacher_inputs_this_run':8,'teacher_attribute_denominator':16,
  'valid_json_count':valid,'correct_attribute_count':bits,'correct_pair_count':pairs,'heldout_inputs':0,'utility_history_runs':0,
  'model_parameter_count':sum(p.numel() for p in model.parameters()),'runtime':first.runtime(),
  'settings':{'device':'mps','dtype':'float16','source_weight_dtype':'bfloat16','attention':'eager','enable_thinking':False,
    'do_sample':False,'use_model_defaults':False,'effective_mode_asserted_in_actual_merge':True,'max_new_tokens':32,
    'requests_sequential':True,'kv_cache':'per request only','threads':2,'interop_threads':1,'seed':7901,
    'semantic_prompt_changed':False,'parser_changed':False,'teacher_inputs_changed':False},
  'cpu_load_wall_seconds':cpu_loaded-t,'cpu_load_process_cpu_seconds':cpu_loadcpu,
  'transfer_to_mps_wall_seconds':loaded-cpu_loaded,'load_and_transfer_wall_seconds':loaded-t,
  'generation_wall_seconds':sum(r['generation_wall_seconds'] for r in outputs),
  'generation_process_cpu_seconds':sum(r['generation_process_cpu_seconds'] for r in outputs),
  'total_wall_seconds_including_imports':time.perf_counter()-START,'total_process_cpu_seconds_including_imports':time.process_time()-CPUSTART,
  'memory_before_load':before,'memory_after_load':after_load,'memory_at_end':first.memory(),'rows':outputs,
  'freeze_sha256':sha(ROOT/'freeze.json'),'prior_manifest_sha256':sha(PRIOR/'manifest.json'),
  'prior_issuer_inputs_sha256':sha(PRIOR/'issuer_inputs.json'),'raw_outputs_sha256':sha(ROOT/'raw_outputs.json'),
  'effective_configurations_sha256':sha(ROOT/'effective_configurations.json'),'all_prior_bytes_preserved':True}
 save(ROOT/'results.json',out);print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2),flush=True)
if __name__=='__main__':main()
