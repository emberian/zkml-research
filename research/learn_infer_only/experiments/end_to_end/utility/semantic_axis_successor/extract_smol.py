"""The frozen 135M baseline on new source texts only; no semantic oracle."""
import sys,time
sys.dont_write_bytecode=True
START=time.perf_counter();CPUSTART=time.process_time()
from common import *
import numpy as np
import torch,transformers
from transformers import AutoTokenizer,AutoModelForCausalLM
def main():
 verify();assert not (ROOT/'smol_test.started.json').exists(),'One baseline extraction only'
 save(ROOT/'smol_test.started.json',{'freeze_sha256':sha(ROOT/'freeze.json'),'attempt':1})
 # Only issuer source strings, never the records/oracle file, enter this process.
 source=load(ROOT/'issuer_inputs.json');records=[r for r in source if r['axis']=='a']
 assert [r['record_id'] for r in records]==list(range(256,384))
 inv=load(UTILITY/'encoder_feasibility.json');modelpath=Path(inv['model_path'])
 for name,row in inv['model_files'].items():assert sha(modelpath/name)==row['sha256'],name
 torch.set_num_threads(2);torch.set_num_interop_threads(1);torch.manual_seed(7901)
 t=time.perf_counter();c=time.process_time()
 tok=AutoTokenizer.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False)
 tok.padding_side='right';tok.pad_token=tok.eos_token
 model=AutoModelForCausalLM.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False,
  dtype=torch.float32,attn_implementation='eager').eval().requires_grad_(False)
 loadwall=time.perf_counter()-t;loadcpu=time.process_time()-c;captured={}
 def hook(module,inputs,output):captured['block9']=output
 handle=model.model.layers[9].register_forward_hook(hook)
 batches=[];arrays=[];lengths=[]
 with torch.inference_mode():
  for i in range(0,128,16):
   texts=[r['text'] for r in records[i:i+16]]
   batch=tok(texts,padding=True,truncation=False,return_tensors='pt');n=batch['attention_mask'].sum(1)
   t=time.perf_counter();c=time.process_time()
   model.model(**batch,use_cache=False,return_dict=True);h=captured['block9']
   pooled=(h*batch['attention_mask'][:,:,None]).sum(1)/n[:,None]
   assert pooled.shape==(len(n),576)
   arrays.append(pooled.numpy());lengths.extend(n.tolist())
   row={'first_record_id':records[i]['record_id'],'records':len(n),'padded_tokens_per_record':batch['input_ids'].shape[1],
    'wall_seconds':time.perf_counter()-t,'cpu_seconds':time.process_time()-c};batches.append(row);print(json.dumps(row),flush=True)
 handle.remove();np.savez(ROOT/'smol_test.npz',features=np.concatenate(arrays),token_lengths=np.array(lengths))
 result={'executed':True,'model':'HuggingFaceTB/SmolLM2-135M','revision':inv['revision'],'model_path':str(modelpath),
  'model_files':inv['model_files'],'records':128,'record_ids':list(range(256,384)),
  'parameter_count':sum(p.numel() for p in model.parameters()),'teacher_reencodings':0,'oracle_parsed':False,
  'runtime':runtime(),'numpy':np.__version__,
  'settings':{'device':'cpu','dtype':'float32','attention':'eager','batch_size':16,'padding_side':'right',
   'use_cache':False,'threads':2,'interop_threads':1,'seed':7901,'pooling':'masked mean direct block9 output',
   'blocks_actually_executed':30,'local_files_only':True,'trust_remote_code':False},
  'freeze_sha256':sha(ROOT/'freeze.json'),'script_sha256':sha(__file__),'features_sha256':sha(ROOT/'smol_test.npz'),
  'load_wall_seconds':loadwall,'load_cpu_seconds':loadcpu,'batches':batches,
  'forward_wall_seconds':sum(x['wall_seconds'] for x in batches),'forward_cpu_seconds':sum(x['cpu_seconds'] for x in batches),
  'unpadded_tokens':sum(lengths),'padded_tokens':sum(x['records']*x['padded_tokens_per_record'] for x in batches),
  'total_wall_seconds_including_imports':time.perf_counter()-START,'total_cpu_seconds_including_imports':time.process_time()-CPUSTART,
  'process_high_water_rss_bytes_macos':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
 save(ROOT/'smol_test.extraction.json',result);print(json.dumps({k:v for k,v in result.items() if k not in ['model_files','batches','record_ids']},indent=2))
if __name__=='__main__':main()
