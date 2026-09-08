"""Run public phase, public verification, then deferred private drain."""
import datetime
import os
import subprocess
import sys
import time
from common import ROOT,REPORTS,save,sha,verify_freeze

verify_freeze()
assert not (ROOT/'launch_started.json').exists()
started=time.perf_counter()
save(ROOT/'launch_started.json',{'started_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
     'pid':os.getpid(),'freeze_sha256':sha(ROOT/'freeze.json'),'script_stages':['run','verify_public','drain']})
for stage in ['run','verify_public','drain']:
    command=[sys.executable,'-B',str(ROOT/(stage+'.py'))]
    t=time.perf_counter()
    with (ROOT/(stage+'.stdout')).open('x') as stdout,(ROOT/(stage+'.stderr')).open('x') as stderr:
        run=subprocess.run(command,stdout=stdout,stderr=stderr,cwd=ROOT)
    save(ROOT/(stage+'.command.json'),{'command':command,'exit_code':run.returncode,'wall_seconds':time.perf_counter()-t})
    print({'completed_stage':stage,'exit_code':run.returncode},flush=True)
    if run.returncode:sys.exit(run.returncode)
save(REPORTS/'launch_completed.json',{'completed':True,'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
     'whole_launch_wall_seconds':time.perf_counter()-started})
