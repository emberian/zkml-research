"""One launch, sequential stages; any failed stage prevents every later stage."""
import datetime
import os
import subprocess
import sys
from common import ROOT,save,verify_freeze


def main():
    os.umask(0o077);verify_freeze();records=[]
    assert not (ROOT/'pipeline.json').exists()
    for stage in ['run_public','verify_public','drain','seal']:
        argv=[sys.executable,str(ROOT/f'{stage}.py')]
        started=datetime.datetime.now(datetime.timezone.utc).isoformat()
        with (ROOT/f'{stage}.stdout').open('xb') as out,(ROOT/f'{stage}.stderr').open('xb') as err:
            process=subprocess.run(argv,cwd=ROOT,stdout=out,stderr=err)
        row={'stage':stage,'argv':argv,'started_utc':started,'ended_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'returncode':process.returncode}
        records.append(row);save(ROOT/'pipeline.json',{'claim':'EXECUTED','stages':records,'completed':stage=='seal' and process.returncode==0})
        print(__import__('json').dumps(row),flush=True)
        if process.returncode:raise SystemExit(process.returncode)


if __name__=='__main__':main()
