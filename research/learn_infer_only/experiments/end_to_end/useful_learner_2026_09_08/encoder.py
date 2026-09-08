"""Plaintext E5 issuer. Labels and learner state are never encoder inputs."""
import hashlib,json,time
from pathlib import Path
import numpy as np
HERE=Path(__file__).resolve().parent
CFG=json.loads((HERE/'config.json').read_text())
class Encoder:
 def __init__(self,cache=None):
  self.cache=Path(cache or HERE/'feature_cache');self.cache.mkdir(parents=True,exist_ok=True)
  self.model=None;self.stats={'model_load_seconds':0.,'forward_seconds':0.,'forward_batches':0,'encoded_texts':0,'cached_texts':0,'clipped_coordinates':0}
  self.projection=(np.random.Generator(np.random.PCG64(CFG['projection_seed'])).integers(0,2,(768,576),dtype=np.int8)*2-1).astype(np.float32)/np.sqrt(np.float32(576))
 def key(self,text):
  return hashlib.sha256((json.dumps(CFG,sort_keys=True)+'\0'+text).encode()).hexdigest()
 def load(self):
  if self.model is not None:return
  import torch,transformers
  from transformers import AutoTokenizer,AutoModel
  t=time.perf_counter();torch.set_num_threads(2);torch.set_num_interop_threads(1)
  self.torch=torch
  self.tokenizer=AutoTokenizer.from_pretrained(CFG['model_path'],local_files_only=True,trust_remote_code=False)
  self.model=AutoModel.from_pretrained(CFG['model_path'],local_files_only=True,trust_remote_code=False,dtype=torch.float32,attn_implementation='eager').eval().requires_grad_(False)
  self.stats.update(model_load_seconds=time.perf_counter()-t,torch=torch.__version__,transformers=transformers.__version__,numpy=np.__version__)
 def encode(self,texts):
  if any(not isinstance(t,str) or not t.strip() for t in texts):raise ValueError('Text must be nonempty')
  result={};missing=[]
  for text in dict.fromkeys(texts):
   p=self.cache/(self.key(text)+'.json')
   if p.exists():result[text]=json.loads(p.read_text())['vector'];self.stats['cached_texts']+=1
   else:missing.append(text)
  if missing:self.load()
  for first in range(0,len(missing),16):
   chunk=missing[first:first+16];t=time.perf_counter()
   batch=self.tokenizer(['query: '+s for s in chunk],padding=True,truncation=True,max_length=512,return_tensors='pt')
   with self.torch.inference_mode():
    h=self.model(**batch).last_hidden_state
    mask=batch['attention_mask'][:,:,None]
    mean=(h*mask).sum(1)/mask.sum(1)
    raw=self.torch.nn.functional.normalize(mean,p=2,dim=1).numpy()
   projected=raw@self.projection
   projected/=np.linalg.norm(projected,axis=1,keepdims=True)
   unbounded=np.rint(CFG['scale']*projected)
   vectors=np.clip(unbounded,-127,127).astype(np.int64)
   self.stats['clipped_coordinates']+=int(np.count_nonzero(abs(unbounded)>127))
   for text,vec in zip(chunk,vectors):
    vector=vec.tolist()+[0];result[text]=vector
    (self.cache/(self.key(text)+'.json')).write_text(json.dumps({'text_sha256':hashlib.sha256(text.encode()).hexdigest(),'vector':vector},separators=(',',':'))+'\n')
   elapsed=time.perf_counter()-t;self.stats['forward_seconds']+=elapsed;self.stats['forward_batches']+=1;self.stats['encoded_texts']+=len(chunk)
   print(json.dumps({'encoder_batch':first//16,'texts':len(chunk),'seconds':elapsed}),flush=True)
  return np.array([result[t] for t in texts],dtype=np.int64)
