"""No inference at import; shared provenance and exact utility definitions."""
import hashlib,json,os,platform,resource,sys
from pathlib import Path
sys.dont_write_bytecode=True
for key in ['HF_HUB_OFFLINE','TRANSFORMERS_OFFLINE']:os.environ[key]='1'
os.environ['TOKENIZERS_PARALLELISM']='false'
ROOT=Path(__file__).resolve().parent;UTILITY=ROOT.parent
BASE=UTILITY.parents[1]/'adaptation_utility';SELECTED=UTILITY/'semantic_axis_selection'
load=lambda p:json.loads(Path(p).read_text())
save=lambda p,x:Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  while data:=f.read(1024*1024):h.update(data)
 return h.hexdigest()
def verify_priors():
 manifest=load(SELECTED/'manifest.json')
 for name,row in manifest['files'].items():assert sha(SELECTED/name)==row['sha256'],name
 return {'selected_teacher_manifest_entries':len(manifest['files'])}
def verify():
 for p,h in load(ROOT/'freeze.json')['source_sha256'].items():assert sha(p)==h,p
 verify_priors()
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
