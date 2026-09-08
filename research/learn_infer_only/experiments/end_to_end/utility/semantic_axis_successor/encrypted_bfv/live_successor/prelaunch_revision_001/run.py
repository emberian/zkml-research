"""One reviewed model/BFV attempt; public success gates the separate private drain."""
import argparse,hashlib,json,resource,subprocess,sys,time
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
 parser=argparse.ArgumentParser();parser.add_argument('--review',required=True);args=parser.parse_args()
 assert not (ROOT/'run_started.json').exists(),'Preserve the only model/BFV attempt'
 freeze=load(ROOT/'freeze.json');review=load(args.review)
 assert review['accepted'] is True and review['freeze_sha256']==sha(ROOT/'freeze.json')
 runtime=Path(freeze['runtime']);reports=Path(freeze['reports']);snap=runtime/'e2e'
 def check():
  for p,h in freeze['public_source_dependencies'].items():assert sha(p)==h,p
  for p,h in freeze['snapshot_source_pins'].items():assert sha(snap/p)==h,p
  for p,h in freeze['query_vector_pins'].items():assert sha(runtime/'public_query_inputs'/p)==h,p
 check();pf=load(runtime/'.private/prepared/freeze.json')
 assert sha(runtime/'.private/input.json')==pf['private_input_sha256']
 dump(ROOT/'run_started.json',{'freeze_sha256':sha(ROOT/'freeze.json'),'review_sha256':sha(args.review),'attempt':1,
                             'started_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())})
 commands=[('public_phase',[sys.executable,'-B',str(snap/'verified_reader/live_driver.py'),'--worker',
            '--input',str(runtime/'.private/input.json'),'--runtime',str(runtime),'--reports',str(reports),
            '--binary',str(snap/'resident-crypto')]),
           ('public_verify',[sys.executable,'-B',str(ROOT/'public_verify.py')]),
           ('private_drain',[sys.executable,'-B',str(ROOT/'drain.py')]),
           ('validate',[sys.executable,'-B',str(ROOT/'validate.py')])]
 records=[];begin=time.perf_counter_ns();returncode=1
 try:
  for name,command in commands:
   check();started=time.perf_counter_ns()
   with (reports/(name+'.log')).open('wb') as log:
    result=subprocess.run(command,stdout=log,stderr=subprocess.STDOUT,timeout=600 if name=='public_phase' else 120)
   row={'phase':name,'command':command,'returncode':result.returncode,'wall_ns':time.perf_counter_ns()-started}
   records.append(row);dump(reports/'phase_commands.json',records);print(json.dumps(row),flush=True)
   check();assert result.returncode==0,'Stopped at failed phase; no downstream drain or retry'
  returncode=0
 finally:
  model={p:sha(Path(freeze['model_path'])/p) for p in freeze['model_files']}
  unchanged=all(model[n]==r['sha256'] for n,r in freeze['model_files'].items());check()
  dump(reports/'model_pins_after.json',model)
  cost=resource.getrusage(resource.RUSAGE_CHILDREN)
  dump(ROOT/'run.command.json',{'returncode':returncode,'phases':records,'wall_ns':time.perf_counter_ns()-begin,
       'source_snapshot_and_model_bytes_unchanged':unchanged,'children_user_cpu_seconds':cost.ru_utime,
       'children_system_cpu_seconds':cost.ru_stime,'maximum_child_rss_bytes_macos':cost.ru_maxrss,
       'scope':'Sequential one-attempt pipeline; source hashing overlaps outer wall time. No retry after model scoring.'})
  assert unchanged
if __name__=='__main__':main()
