"""One frozen semantic prompt, eight public teacher inputs, no held-out utility."""
import argparse,hashlib,json,os,platform,resource,sys,time
from pathlib import Path
sys.dont_write_bytecode=True
for k in ['HF_HUB_OFFLINE','TRANSFORMERS_OFFLINE']:os.environ[k]='1'
os.environ['TOKENIZERS_PARALLELISM']='false'
START=time.perf_counter();CPUSTART=time.process_time()
import torch,transformers
from transformers import AutoTokenizer,AutoModelForCausalLM,GenerationConfig
ROOT=Path(__file__).resolve().parent;UTILITY=ROOT.parent;BASE=UTILITY.parents[1]/'adaptation_utility'
IDS=[0,16,32,48,64,80,96,112]
load=lambda p:json.loads(Path(p).read_text())
save=lambda p,x:Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  while data:=f.read(1024*1024):h.update(data)
 return h.hexdigest()
def runtime():return {'python':sys.version,'executable':sys.executable,'torch':torch.__version__,
 'transformers':transformers.__version__,'platform':platform.platform(),'mps_built':torch.backends.mps.is_built(),
 'mps_available':torch.backends.mps.is_available(),'cuda_available':torch.cuda.is_available()}
def prepare():
 assert not (ROOT/'freeze.json').exists(),'Preserve frozen evidence'
 inv=load(UTILITY/'encoder_feasibility/candidates.json')['HuggingFaceTB/SmolLM3-3B'];modelpath=Path(inv['path'])
 files={str(p.relative_to(modelpath)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(modelpath.rglob('*')) if p.is_file()}
 tok=AutoTokenizer.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False)
 instructions=(ROOT/'PROMPT.txt').read_text();records=load(BASE/'representation_records.json');inputs=[];oracle=[]
 for rid in IDS:
  record=records[rid];assert record['pool']=='teach';task=['plant','letter'][record['skill']]
  messages=[{'role':'system','content':instructions},{'role':'user','content':f'Task: {task}\nText: {record["text"]}'}]
  prompt=tok.apply_chat_template(messages,tokenize=False,add_generation_prompt=True,enable_thinking=False)
  tokens=tok([prompt],add_special_tokens=False)['input_ids'][0]
  inputs.append({'record_id':rid,'task':task,'text':record['text'],'messages':messages,'rendered_prompt':prompt,
    'token_ids':tokens,'token_count':len(tokens),'rendered_prompt_sha256':hashlib.sha256(prompt.encode()).hexdigest()})
  oracle.append({'record_id':rid,'a':record['a'],'b':record['b']})
 save(ROOT/'issuer_inputs.json',inputs);save(ROOT/'teacher_oracle.json',oracle)
 source=[ROOT/n for n in ['CONTRACT.md','PROMPT.txt','preflight.py','issuer_inputs.json','teacher_oracle.json']]
 source +=[BASE/'representation_records.json',UTILITY/'encoder_feasibility/candidates.json']
 record={'model':'HuggingFaceTB/SmolLM3-3B','revision':inv['revision'],'model_path':str(modelpath),'model_files':files,
  'source_sha256':{str(p):sha(p) for p in source},'teacher_ids':IDS,'heldout_inputs':0,'prompts_tried':1,
  'runtime':runtime(),'public_instruction_utf8_bytes':len(instructions.encode()),
  'public_instruction_token_count':len(tok(instructions,add_special_tokens=False)['input_ids']),
  'generated_tokens_limit_per_input':32,'weights_not_loaded_in_prepare':True,
  'wall_seconds_including_imports':time.perf_counter()-START}
 assert record['runtime']['mps_available'],'Chosen backend unavailable; no implicit fallback'
 save(ROOT/'freeze.json',record);print(json.dumps({'prepared':True,'freeze_sha256':sha(ROOT/'freeze.json'),
  'teacher_ids':IDS,'input_tokens':[r['token_count'] for r in inputs],'runtime':runtime(),
  'instruction_token_count':record['public_instruction_token_count'],'full_weight_bytes':sum(v['bytes'] for k,v in files.items() if k.endswith('.safetensors'))},indent=2))
def memory():return {'mps_current_allocated_bytes':torch.mps.current_allocated_memory(),
 'mps_driver_allocated_bytes':torch.mps.driver_allocated_memory(),
 'mps_recommended_max_bytes':torch.mps.recommended_max_memory(),
 'process_high_water_rss_bytes_macos':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
def strict_parse(text):
 def pairs(pairs):
  out={}
  for k,v in pairs:
   if k in out:raise ValueError('duplicate key')
   out[k]=v
  return out
 try:
  obj=json.loads(text.strip(),object_pairs_hook=pairs)
  if not isinstance(obj,dict) or set(obj)!= {'a','b'}:raise ValueError('wrong keys/type')
  if not all(v is None or type(v) is int and v in [0,1] for v in obj.values()):raise ValueError('not binary/null')
  return obj,None
 except (ValueError,TypeError) as e:return None,str(e)
def run():
 assert not (ROOT/'results.json').exists(),'Preserve preflight outputs'
 freeze=load(ROOT/'freeze.json');modelpath=Path(freeze['model_path'])
 for p,h in freeze['source_sha256'].items():assert sha(p)==h,p
 for n,row in freeze['model_files'].items():assert sha(modelpath/n)==row['sha256'],n
 assert torch.backends.mps.is_available(),'No implicit CPU fallback'
 torch.set_num_threads(2);torch.set_num_interop_threads(1);torch.manual_seed(7901)
 tok=AutoTokenizer.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False)
 before=memory();t=time.perf_counter();cpu=time.process_time()
 model=AutoModelForCausalLM.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False,
  dtype=torch.float16,attn_implementation='eager').eval().requires_grad_(False)
 cpu_loaded=time.perf_counter();cpu_loadcpu=time.process_time()-cpu
 model.to('mps');torch.mps.synchronize();loaded=time.perf_counter();after_load=memory()
 generation=GenerationConfig(max_new_tokens=32,do_sample=False,num_beams=1,use_cache=True,
  bos_token_id=model.config.bos_token_id,eos_token_id=model.config.eos_token_id,pad_token_id=tok.pad_token_id)
 save(ROOT/'generation_config.json',generation.to_dict());inputs=load(ROOT/'issuer_inputs.json');outputs=[]
 with torch.inference_mode():
  for item in inputs:
   tokens=tok([item['rendered_prompt']],add_special_tokens=False,return_tensors='pt')
   assert tokens['input_ids'][0].tolist()==item['token_ids'];tokens=tokens.to('mps');torch.mps.synchronize()
   t0=time.perf_counter();c0=time.process_time();result=model.generate(**tokens,generation_config=generation)
   torch.mps.synchronize();finished=time.perf_counter();output=result[0,tokens['input_ids'].shape[1]:].cpu().tolist()
   text=tok.decode(output,skip_special_tokens=True);parsed,error=strict_parse(text)
   row={'record_id':item['record_id'],'input_tokens':item['token_count'],'generated_tokens':len(output),
    'generated_token_ids':output,'raw_output':text,'parsed':parsed,'parse_error':error,
    'generation_wall_seconds':finished-t0,'generation_process_cpu_seconds':time.process_time()-c0,'memory_after_generation':memory()}
   outputs.append(row);save(ROOT/'raw_outputs.json',outputs);print(json.dumps(row),flush=True)
 # Oracle is first read after all model outputs; never enters input encoding.
 oracle={r['record_id']:r for r in load(ROOT/'teacher_oracle.json')};correct_bits=0;correct_pairs=0;valid=0
 for row in outputs:
  want=oracle[row['record_id']];got=row['parsed'];bits=[got is not None and got[k]==want[k] for k in ['a','b']]
  correct_bits+=sum(bits);correct_pairs+=int(all(bits));valid+=int(got is not None)
  row['oracle']={'a':want['a'],'b':want['b']};row['attribute_correct']=bits
 out={'execution_completed':True,'teacher_inputs':8,'teacher_attribute_denominator':16,'valid_json_count':valid,
  'correct_attribute_count':correct_bits,'correct_pair_count':correct_pairs,'heldout_inputs':0,'utility_history_runs':0,
  'model_parameter_count':sum(p.numel() for p in model.parameters()),'runtime':runtime(),
  'settings':{'device':'mps','dtype':'float16','source_weight_dtype':'bfloat16','attention':'eager','enable_thinking':False,
   'do_sample':False,'max_new_tokens':32,'requests_sequential':True,'kv_cache':'per request only, discarded between calls',
   'threads':2,'interop_threads':1,'seed':7901,'backbone_updates':0,'prompt_candidates':1},
  'cpu_load_wall_seconds':cpu_loaded-t,'cpu_load_process_cpu_seconds':cpu_loadcpu,
  'transfer_to_mps_wall_seconds':loaded-cpu_loaded,'load_and_transfer_wall_seconds':loaded-t,
  'generation_wall_seconds':sum(r['generation_wall_seconds'] for r in outputs),
  'generation_process_cpu_seconds':sum(r['generation_process_cpu_seconds'] for r in outputs),
  'total_wall_seconds_including_imports':time.perf_counter()-START,'total_process_cpu_seconds_including_imports':time.process_time()-CPUSTART,
  'memory_before_load':before,'memory_after_load':after_load,'memory_at_end':memory(),'rows':outputs,
  'freeze_sha256':sha(ROOT/'freeze.json'),'generation_config_sha256':sha(ROOT/'generation_config.json'),
  'issuer_inputs_sha256':sha(ROOT/'issuer_inputs.json'),'raw_outputs_sha256':sha(ROOT/'raw_outputs.json')}
 save(ROOT/'results.json',out);print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2),flush=True)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('stage',choices=['prepare','run']);globals()[p.parse_args().stage]()
