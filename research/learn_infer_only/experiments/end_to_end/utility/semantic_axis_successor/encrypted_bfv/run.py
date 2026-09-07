"""Execute the frozen normal semantic BFV join once, with pre/post source checks."""
import hashlib,json,resource,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
load=lambda p:json.loads(Path(p).read_bytes())
def dump(p,x):Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def main():
 assert not (ROOT/'run_started.json').exists(),'Preserve the first actual run'
 freeze=load(ROOT/'freeze.json');runtime=Path(freeze['runtime']);reports=Path(freeze['reports']);snap=runtime/'e2e'
 for p,digest in freeze['source_dependencies'].items():assert sha(p)==digest,p
 for p,digest in freeze['snapshot_source_pins'].items():assert sha(snap/p)==digest,p
 args=[sys.executable,'-B',str(snap/'verified_reader/fast_utility_driver.py'),'--worker',
  '--runtime',str(runtime),'--reports',str(reports),'--binary',str(snap/'resident-crypto')]
 dump(ROOT/'run_started.json',{'freeze_sha256':sha(ROOT/'freeze.json'),'command':args})
 dump(reports/'command.json',{'argv':args});start=time.perf_counter_ns()
 with (reports/'execution.log').open('wb') as log:
  proc=subprocess.run(args,stdout=log,stderr=subprocess.STDOUT,timeout=1800)
 elapsed=time.perf_counter_ns()-start
 post={p:sha(p) for p in freeze['source_dependencies']};snapshot={p:sha(snap/p) for p in freeze['snapshot_source_pins']}
 dump(reports/'dependency_pins_after.json',post);dump(reports/'snapshot_pins_after.json',snapshot)
 unchanged=post==freeze['source_dependencies'] and snapshot==freeze['snapshot_source_pins']
 cost=resource.getrusage(resource.RUSAGE_CHILDREN)
 out={'returncode':proc.returncode,'launcher_wall_ns':elapsed,'dependency_and_snapshot_bytes_unchanged':unchanged,
  'children_user_cpu_seconds':cost.ru_utime,'children_system_cpu_seconds':cost.ru_stime,
  'max_child_rss_bytes_macos':cost.ru_maxrss,'command':args,'freeze_sha256':sha(ROOT/'freeze.json')}
 dump(ROOT/'run.command.json',out);print(json.dumps(out,indent=2),flush=True)
 assert unchanged,'Pinned dependencies changed during execution'
 raise SystemExit(proc.returncode)
if __name__=='__main__':main()
