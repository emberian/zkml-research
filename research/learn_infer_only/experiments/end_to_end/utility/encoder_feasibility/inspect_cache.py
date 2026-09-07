"""Read-only public-model cache/header inventory; never loads model tensors."""
import hashlib,json,math,struct,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
CACHE=Path('/Users/ember/.cache/huggingface/hub')
CANDIDATES={'intfloat/e5-base-v2':'f52bf8ec8c7124536f0efb74aca902b2995e5bcd',
 'microsoft/harrier-oss-v1-0.6b':'f9b9dc8d367d443f2479d27aa5d8d2850c0774ee',
 'HuggingFaceTB/SmolLM3-3B':'a07cc9a04f16550a088caea529712d1d335b0ac1',
 'Qwen/Qwen2.5-0.5B-Instruct':'7ae557604adf67be50417f59c2c2f167def9a775'}
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  while chunk:=f.read(1024*1024):h.update(chunk)
 return h.hexdigest()
def save(p,x):Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def main():
 t=time.perf_counter();inventory=[]
 for directory in sorted(CACHE.glob('models--*')):
  snapshots=[]
  for s in sorted((directory/'snapshots').glob('*')):
   files=[{'name':str(p.relative_to(s)),'bytes':p.stat().st_size} for p in sorted(s.rglob('*')) if p.is_file()]
   snapshots.append({'revision':s.name,'files':files,'logical_bytes':sum(f['bytes'] for f in files)})
  inventory.append({'cache':directory.name,'snapshots':snapshots})
 save(ROOT/'cache_inventory.json',{'corpus':str(CACHE),'instrument':str(Path(__file__).resolve()),
   'scope':'Immediate models--*/snapshots trees; logical files/sizes only; no unrelated file contents',
   'entries':inventory})
 candidates={}
 for name,rev in CANDIDATES.items():
  p=CACHE/('models--'+name.replace('/','--'))/'snapshots'/rev;counts={};weights=[]
  files={}
  for f in sorted(p.rglob('*')):
   if not f.is_file():continue
   rel=str(f.relative_to(p));row={'bytes':f.stat().st_size}
   # Fully pin the recommended E5; for other large weights pin header only.
   if name=='intfloat/e5-base-v2' or f.suffix!='.safetensors':row['sha256']=sha(f)
   files[rel]=row
  for f in sorted(p.glob('*.safetensors')):
   with f.open('rb') as stream:
    n=struct.unpack('<Q',stream.read(8))[0];raw=stream.read(n);header=json.loads(raw)
   for key,tensor in header.items():
    if key=='__metadata__':continue
    counts[tensor['dtype']]=counts.get(tensor['dtype'],0)+math.prod(tensor['shape'])
   weights.append({'name':f.name,'bytes':f.stat().st_size,'header_bytes':n,
     'header_sha256':hashlib.sha256(raw).hexdigest()})
  cfg=json.loads((p/'config.json').read_text())
  candidates[name]={'path':str(p),'revision':rev,'config':cfg,'files':files,
    'weight_headers':weights,'tensor_scalars_by_dtype':counts,
    'floating_tensor_scalars':sum(v for k,v in counts.items() if k in ['F16','BF16','F32','F64']),
    'weight_file_bytes':sum(f['bytes'] for f in weights),'snapshot_logical_bytes':sum(f['bytes'] for f in files.values()),
    'full_e5_weight_hash_verified_here':name=='intfloat/e5-base-v2'}
 save(ROOT/'candidates.json',candidates)
 save(ROOT/'inspection.json',{'passed':True,'executed_model_forwards':0,'loaded_model_tensors':False,
   'physical_memory_bytes':int(subprocess.check_output(['/usr/sbin/sysctl','-n','hw.memsize'],text=True)),
   'cache_model_directories':len(inventory),'wall_seconds':time.perf_counter()-t,
   'script_sha256':sha(__file__),'candidates_sha256':sha(ROOT/'candidates.json'),
   'cache_inventory_sha256':sha(ROOT/'cache_inventory.json')})
 print(json.dumps({'passed':True,'model_directories':len(inventory),'selected_e5':candidates['intfloat/e5-base-v2'],
   'wall_seconds':time.perf_counter()-t},indent=2))
if __name__=='__main__':main()
