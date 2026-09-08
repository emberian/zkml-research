"""Retain the exact subprocess command, stdout, stderr and exit status."""
import datetime
import subprocess
import sys
import time
from common import ROOT, save

stage=sys.argv[1]
assert stage in ['freeze','evaluate','audit']
command=[sys.executable,'-B',str(ROOT/(stage+'.py'))]
assert not (ROOT/(stage+'.command.json')).exists(), 'Preserve prior attempts'
start=time.perf_counter()
started=datetime.datetime.now(datetime.timezone.utc).isoformat()
with (ROOT/(stage+'.stdout')).open('w') as out, (ROOT/(stage+'.stderr')).open('w') as err:
    completed=subprocess.run(command,stdout=out,stderr=err,cwd=ROOT)
save(ROOT/(stage+'.command.json'),{'command':command,'cwd':str(ROOT),'started_utc':started,
                                  'exit_code':completed.returncode,'wall_seconds':time.perf_counter()-start})
print({'stage':stage,'exit_code':completed.returncode,'stdout':str(ROOT/(stage+'.stdout'))})
sys.exit(completed.returncode)
