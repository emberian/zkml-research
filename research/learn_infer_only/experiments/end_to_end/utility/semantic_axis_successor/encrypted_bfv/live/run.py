"""Execute the single frozen live demonstration; never retry a scored input."""
import hashlib,json,resource,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_bytes())
def sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  while raw:=f.read(1024*1024):h.update(raw)
 return h.hexdigest()
def dump(p,x):Path(p).write_text(json.dumps(x,sort_keys=True,indent=2)+'\n')
def main():
 assert not (ROOT/'run_started.json').exists(),'Preserve the only attempted live demonstration'
 freeze=load(ROOT/'freeze.json');runtime=Path(freeze['runtime']);reports=Path(freeze['reports']);snap=runtime/'e2e'
 for p,h in freeze['public_source_dependencies'].items():assert sha(p)==h,p
 for p,h in freeze['snapshot_source_pins'].items():assert sha(snap/p)==h,p
 for p,h in freeze['query_vector_pins'].items():assert sha(runtime/'public_query_inputs'/p)==h,p
 privatefreeze=load(runtime/'.private/prepared/freeze.json')
 assert sha(runtime/'.private/input.json')==privatefreeze['private_input_sha256']
 command=[sys.executable,'-B',str(snap/'verified_reader/live_driver.py'),'--worker','--input',str(runtime/'.private/input.json'),
  '--runtime',str(runtime),'--reports',str(reports),'--binary',str(snap/'resident-crypto')]
 dump(ROOT/'run_started.json',{'freeze_sha256':sha(ROOT/'freeze.json'),'attempt':1})
 dump(reports/'command.json',{'argv':command,'input_is_generic_ignored_private_path':True})
 start=time.perf_counter_ns()
 with (reports/'execution.log').open('wb') as log:result=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,timeout=600)
 elapsed=time.perf_counter_ns()-start
 deps={p:sha(p) for p in freeze['public_source_dependencies']};snapshot={p:sha(snap/p) for p in freeze['snapshot_source_pins']}
 model={p:sha(Path(freeze['model_path'])/p) for p in freeze['model_files']}
 unchanged=deps==freeze['public_source_dependencies'] and snapshot==freeze['snapshot_source_pins'] and all(model[n]==r['sha256'] for n,r in freeze['model_files'].items())
 dump(reports/'source_dependencies_after.json',deps);dump(reports/'snapshot_pins_after.json',snapshot);dump(reports/'model_pins_after.json',model)
 cost=resource.getrusage(resource.RUSAGE_CHILDREN)
 out={'command':command,'returncode':result.returncode,'launcher_subprocess_wall_ns':elapsed,'source_snapshot_and_model_bytes_unchanged':unchanged,
  'children_user_cpu_seconds':cost.ru_utime,'children_system_cpu_seconds':cost.ru_stime,'maximum_child_rss_bytes_macos':cost.ru_maxrss,
  'scope':'One subprocess interval including model and BFV normal path; pre/post hash verification and staging are outside this interval.'}
 dump(ROOT/'run.command.json',out);print(json.dumps(out,indent=2),flush=True)
 assert unchanged;raise SystemExit(result.returncode)
if __name__=='__main__':main()
