#!/usr/bin/env python3
"""Read/hash public cached model files and public selection provenance; no model import."""
from pathlib import Path
import hashlib,json,time
HERE=Path(__file__).resolve().parent
EXPERIMENTS=HERE.parents[1]
SEM=EXPERIMENTS/'end_to_end/utility/semantic_axis_successor'
SELECT=SEM.parent/'semantic_axis_selection'
def sha(path):
 h=hashlib.sha256()
 with Path(path).open('rb') as source:
  while raw:=source.read(1024*1024):h.update(raw)
 return h.hexdigest()
def main():
 start=time.perf_counter_ns();freeze=json.loads((SEM/'freeze.json').read_bytes());root=Path(freeze['model_path']);checked={}
 for name,entry in freeze['model_files'].items():
  p=root/name;observed=sha(p);assert observed==entry['sha256'] and p.stat().st_size==entry['bytes']
  checked[name]={'sha256':observed,'bytes':p.stat().st_size}
 sources=[SEM/'score.py',SEM/'CONTRACT.md',SELECT/'prompts.json',SELECT/'REPORT.md',SELECT/'results.json']
 model_source=next(Path(n) for n in freeze['source_sha256'] if n.endswith('modeling_smollm3.py'))
 assert sha(model_source)==freeze['source_sha256'][str(model_source)];sources.append(model_source)
 out={'schema':'live-semantic-independent-model-provenance-v1','ok':True,'model':freeze['model'],'revision':freeze['revision'],'model_path':str(root),'model_files':checked,'file_count':len(checked),'total_model_file_bytes':sum(x['bytes'] for x in checked.values()),'public_source_read_sha256':{str(p):sha(p) for p in sources},'elapsed_hash_check_ns':time.perf_counter_ns()-start,'model_or_crypto_imports':0,'model_forwards':0,'private_file_reads':0,'source_sha256':sha(Path(__file__))}
 (HERE/'model_preflight.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n');print(json.dumps(out,sort_keys=True))
if __name__=='__main__':main()
