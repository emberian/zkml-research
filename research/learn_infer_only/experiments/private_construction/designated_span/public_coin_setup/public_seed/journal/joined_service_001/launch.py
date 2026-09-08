"""Authorized normal join; process-group deadline and public-before-private gate."""
from pathlib import Path
import datetime,json,os,signal,subprocess,sys,time
from driver import check_pins,file_sha
from common import read_json,require,write_json
HERE=Path(__file__).resolve().parent
REPORTS=HERE/'reports/normal_001'
ROOT=HERE/'runtime/normal_001'

def group_exists(pgid):
 try:os.killpg(pgid,0);return True
 except ProcessLookupError:return False

def cleanup(proc):
 required=group_exists(proc.pid);term=False;kill=False
 if required:
  os.killpg(proc.pid,signal.SIGTERM);term=True
  until=time.monotonic()+5
  while group_exists(proc.pid) and time.monotonic()<until:
   proc.poll();time.sleep(.05)
  if group_exists(proc.pid):os.killpg(proc.pid,signal.SIGKILL);kill=True
 proc.wait(timeout=5)
 until=time.monotonic()+5
 while group_exists(proc.pid) and time.monotonic()<until:time.sleep(.05)
 return {'cleanup_needed':required,'sent_SIGTERM':term,'sent_SIGKILL':kill,'group_absent':not group_exists(proc.pid)}

def main():
 require(len(sys.argv)==1,'noAlternateLaunchArguments');check_pins(REPORTS)
 now=datetime.datetime.now(datetime.timezone.utc)
 require(not ROOT.exists() and not (REPORTS/'LAUNCH.json').exists(),'singleFreshAttemptOnly')
 started=time.monotonic();deadline=started+2700
 write_json(REPORTS/'LAUNCH.json',{'schema':'public-seed-journal-authorized-launch-v1','utc':now.isoformat(),'overall_cap_seconds':2700,'authorization_basis':'Renewed root/user instruction: finish prepared public-seed journal join and run normal33Learn/4Infer/1expiry with reopen/retry; no additional independent-review gate.','execution_pins_sha256':file_sha(REPORTS/'execution_pins.json')})
 def phase(name,argv,private=False):
  check_pins(REPORTS);remaining=deadline-time.monotonic();require(remaining>0,'overallDeadline')
  directory=ROOT/'.private/postprotocol' if private else REPORTS
  directory.mkdir(parents=True,exist_ok=True,mode=0o700 if private else 0o755)
  outpath=directory/(name+'.stdout');errpath=directory/(name+'.stderr')
  with outpath.open('xb') as out,errpath.open('xb') as err:
   if private:os.chmod(outpath,0o600);os.chmod(errpath,0o600)
   proc=subprocess.Popen(argv,stdout=out,stderr=err,start_new_session=True)
   stamp=time.monotonic();timeout=False
   try:
    proc.wait(timeout=max(.001,deadline-time.monotonic()))
   except subprocess.TimeoutExpired:timeout=True
   finally:closed=cleanup(proc)
  record={'phase':name,'argv':argv,'pid':proc.pid,'exit_code':proc.returncode,'timed_out':timeout,'elapsed_ns':round((time.monotonic()-stamp)*1_000_000_000),**closed}
  write_json(directory/(name+'.json'),record,private)
  require(not timeout and proc.returncode==0 and closed['group_absent'] and not closed['cleanup_needed'],'phaseMustCloseWithoutCleanup:'+name)
  require(time.monotonic()<=deadline,'overallDeadlineAfterPhase')
  return record
 try:
  print(json.dumps({'phase':'public_start','cap_seconds':2700}),flush=True)
  public=phase('public_worker',[sys.executable,'-B',str(HERE/'driver.py'),'public','--root',str(ROOT),'--reports',str(REPORTS)])
  verification=phase('public_verification_worker',[sys.executable,'-B',str(HERE/'public_close.py'),'--root',str(ROOT),'--reports',str(REPORTS)])
  require(public['group_absent'] and verification['group_absent'],'allPublicGroupsClosed');check_pins(REPORTS)
  require(read_json(REPORTS/'public_verification.json')['ok'],'publicVerifierPassed')
  inventory={p.name:{'bytes':p.stat().st_size,'sha256':file_sha(p)} for p in sorted(REPORTS.iterdir()) if p.is_file()}
  write_json(REPORTS/'PUBLIC_SEAL.json',{'schema':'public-seed-journal-public-seal-v1','files':inventory,'all_public_process_groups_absent':True,'private_decryptions_so_far':0,'elapsed_ns':round((time.monotonic()-started)*1_000_000_000)})
  write_json(REPORTS/'PUBLIC_GATE.json',{'ok':True,'all_public_process_groups_absent':True,'public_seal_sha256':file_sha(REPORTS/'PUBLIC_SEAL.json'),'public_verification_sha256':file_sha(REPORTS/'public_verification.json'),'execution_pins_sha256':file_sha(REPORTS/'execution_pins.json')})
  print(json.dumps({'phase':'public_closed','elapsed_seconds':time.monotonic()-started}),flush=True)
  phase('private_worker',[sys.executable,'-B',str(HERE/'driver.py'),'private','--root',str(ROOT),'--reports',str(REPORTS)],True)
  print(json.dumps({'ok':True,'report':str(REPORTS/'report.json')}),flush=True)
 except BaseException as error:
  # Never open a private result or continue a failed public phase.
  private=(REPORTS/'PUBLIC_GATE.json').exists()
  target=ROOT/'.private/postprotocol' if private else REPORTS
  target.mkdir(parents=True,exist_ok=True,mode=0o700)
  write_json(target/'LAUNCH_STOPPED.json',{'ok':False,'reason':type(error).__name__,'no_retry':True},private)
  raise

if __name__=='__main__':main()
