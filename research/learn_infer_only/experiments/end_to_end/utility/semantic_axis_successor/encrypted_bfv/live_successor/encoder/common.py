"""Private output/provenance helpers for the unchanged factual forward loop."""
import hashlib,json,os,platform,resource,sys
from pathlib import Path
sys.dont_write_bytecode=True
for key in ['HF_HUB_OFFLINE','TRANSFORMERS_OFFLINE']:os.environ[key]='1'
os.environ['TOKENIZERS_PARALLELISM']='false'
ROOT=Path(os.environ['SEMANTIC_LIVE_WORKDIR']).resolve()
load=lambda p:json.loads(Path(p).read_bytes())
def save(p,x):
 fd=os.open(p,os.O_CREAT|os.O_TRUNC|os.O_WRONLY,0o600)
 with os.fdopen(fd,'w') as f:json.dump(x,f,sort_keys=True,indent=2);f.write('\n')
 os.chmod(p,0o600)
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  while data:=f.read(1024*1024):h.update(data)
 return h.hexdigest()
def verify_priors():
 counts={}
 for directory in load(ROOT/'freeze.json')['parent_manifests']:
  directory=Path(directory);m=load(directory/'manifest.json')
  for name,r in m['files'].items():assert sha(directory/name)==r['sha256'],(directory,name)
  counts[str(directory)]=len(m['files'])
 return counts
def runtime():
 import torch,transformers
 return {'python':sys.version,'executable':sys.executable,'torch':torch.__version__,'transformers':transformers.__version__,
  'platform':platform.platform(),'mps_built':torch.backends.mps.is_built(),'mps_available':torch.backends.mps.is_available(),
  'cuda_available':torch.cuda.is_available()}
def memory():
 import torch
 return {'mps_current_allocated_bytes':torch.mps.current_allocated_memory(),
  'mps_driver_allocated_bytes':torch.mps.driver_allocated_memory(),'mps_recommended_max_bytes':torch.mps.recommended_max_memory(),
  'process_high_water_rss_bytes_macos':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
