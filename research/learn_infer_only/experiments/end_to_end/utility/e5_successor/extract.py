"""Pinned local E5 or frozen SmolLM2 features; stage order prevents test peeking."""
import argparse,hashlib,json,os,resource,sys,time
from pathlib import Path
sys.dont_write_bytecode=True
for k in ['HF_HUB_OFFLINE','TRANSFORMERS_OFFLINE']:os.environ[k]='1'
os.environ['TOKENIZERS_PARALLELISM']='false'
started=time.perf_counter();cpustart=time.process_time()
import numpy as np
import torch,transformers
from transformers import AutoTokenizer,AutoModel,AutoModelForCausalLM
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_text())
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  while x:=f.read(1024*1024):h.update(x)
 return h.hexdigest()
def main():
 parser=argparse.ArgumentParser();parser.add_argument('kind',choices=['e5_train','e5_test','smol_test']);kind=parser.parse_args().kind
 assert not (ROOT/f'{kind}.extraction.json').exists(),'Preserve earlier extraction'
 for path,digest in load(ROOT/'freeze.json')['source_sha256'].items():assert sha(path)==digest,path
 records=load(ROOT/'records.json');is_e5=kind.startswith('e5');train=kind=='e5_train'
 if train:records=records[:256];selection_sha=None;assert not (ROOT/'selection.json').exists()
 else:records=records[256:];selection_sha=sha(ROOT/'selection.json')
 if is_e5:
  inv=load(ROOT.parent/'encoder_feasibility/candidates.json')['intfloat/e5-base-v2'];modelpath=Path(inv['path']);modelname='intfloat/e5-base-v2';revision=inv['revision'];files=inv['files']
 else:
  inv=load(ROOT.parent/'encoder_feasibility.json');modelpath=Path(inv['model_path']);modelname='HuggingFaceTB/SmolLM2-135M';revision=inv['revision'];files=inv['model_files']
 for name,row in files.items():assert sha(modelpath/name)==row['sha256'],name
 torch.set_num_threads(2);torch.set_num_interop_threads(1);torch.manual_seed(7901)
 t=time.perf_counter();tcpu=time.process_time();tok=AutoTokenizer.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False)
 tok.padding_side='right'
 if not is_e5:tok.pad_token=tok.eos_token
 cls=AutoModel if is_e5 else AutoModelForCausalLM
 model=cls.from_pretrained(modelpath,local_files_only=True,trust_remote_code=False,dtype=torch.float32,attn_implementation='eager').eval().requires_grad_(False)
 loadwall=time.perf_counter()-t;loadcpu=time.process_time()-tcpu;captured={};handle=None
 if not is_e5:
  def hook(module,inputs,output):captured['block9']=output
  handle=model.model.layers[9].register_forward_hook(hook)
 batches=[];arrays=[];lengths=[]
 with torch.inference_mode():
  for i in range(0,len(records),16):
   texts=[('query: ' if is_e5 else '')+r['text'] for r in records[i:i+16]]
   batch=tok(texts,padding=True,truncation=False,return_tensors='pt');n=batch['attention_mask'].sum(1)
   if is_e5:assert int(n.max())<=512,'No silent truncation'
   t=time.perf_counter();tcpu=time.process_time()
   if is_e5:h=model(**batch,use_cache=False,return_dict=True).last_hidden_state
   else:model.model(**batch,use_cache=False,return_dict=True);h=captured['block9']
   pooled=(h*batch['attention_mask'][:,:,None]).sum(1)/n[:,None]
   if is_e5:pooled=torch.nn.functional.normalize(pooled,p=2,dim=1)
   assert pooled.shape==(len(n),768 if is_e5 else 576)
   arrays.append(pooled.numpy());lengths.extend(n.tolist())
   row={'first_record_id':records[i]['id'],'records':len(n),'padded_tokens':batch['input_ids'].shape[1],
    'wall_seconds':time.perf_counter()-t,'cpu_seconds':time.process_time()-tcpu};batches.append(row);print(json.dumps(row),flush=True)
 if handle:handle.remove()
 np.savez(ROOT/f'{kind}.npz',features=np.concatenate(arrays),token_lengths=np.array(lengths))
 out={'executed':True,'kind':kind,'model':modelname,'revision':revision,'model_path':str(modelpath),'model_files':files,
  'records':len(records),'record_ids':[r['id'] for r in records],'parameter_count':sum(p.numel() for p in model.parameters()),
  'trainable_backbone_parameters':sum(p.numel() for p in model.parameters() if p.requires_grad),
  'python':sys.version,'executable':sys.executable,'numpy':np.__version__,'torch':torch.__version__,'transformers':transformers.__version__,
  'settings':{'device':'cpu','dtype':'float32','attention':'eager','batch_size':16,'padding_side':'right','use_cache':False,
   'threads':2,'interop_threads':1,'seed':7901,'prefix':'query: ' if is_e5 else '',
   'pooling':'masked mean final hidden states then L2' if is_e5 else 'masked mean direct block9 output',
   'blocks_actually_executed':12 if is_e5 else 30,'local_files_only':True,'trust_remote_code':False},
  'selection_sha256':selection_sha,'freeze_sha256':sha(ROOT/'freeze.json'),'records_sha256':sha(ROOT/'records.json'),
  'script_sha256':sha(__file__),'features_sha256':sha(ROOT/f'{kind}.npz'),
  'load_wall_seconds':loadwall,'load_cpu_seconds':loadcpu,'batches':batches,
  'forward_wall_seconds':sum(r['wall_seconds'] for r in batches),'forward_cpu_seconds':sum(r['cpu_seconds'] for r in batches),
  'unpadded_tokens':sum(lengths),'padded_tokens':sum(r['records']*r['padded_tokens'] for r in batches),
  'total_wall_seconds_including_imports':time.perf_counter()-started,'total_cpu_seconds_including_imports':time.process_time()-cpustart,
  'process_high_water_rss_bytes_macos':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
 if not train:assert selection_sha==sha(ROOT/'selection.json')
 (ROOT/f'{kind}.extraction.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
 print(json.dumps({k:v for k,v in out.items() if k not in ['model_files','batches','record_ids']},indent=2),flush=True)
if __name__=='__main__':main()
