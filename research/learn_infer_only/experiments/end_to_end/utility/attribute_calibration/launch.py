"""Retain command, elapsed wall time, stdout and stderr for one protocol stage."""
import argparse,json,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
BASE=ROOT.parents[2]/'adaptation_utility'
def main():
    p=argparse.ArgumentParser();p.add_argument('stage',choices=['select','extract','evaluate','audit']);a=p.parse_args()
    assert not (ROOT/f'{a.stage}.command.json').exists(),'Preserve prior process evidence'
    python=BASE/'.venv/bin/python';command=[str(python),str(ROOT/'run.py'),a.stage] if a.stage in ['select','evaluate'] else [str(python),str(ROOT/f'{a.stage}.py')]
    t=time.perf_counter()
    with (ROOT/f'{a.stage}.stdout').open('w') as out,(ROOT/f'{a.stage}.stderr').open('w') as err:
        result=subprocess.run(command,stdout=out,stderr=err,check=False)
    record={'command':command,'cwd':str(Path.cwd()),'returncode':result.returncode,'wall_seconds':time.perf_counter()-t}
    (ROOT/f'{a.stage}.command.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record));print((ROOT/f'{a.stage}.stdout').read_text());print((ROOT/f'{a.stage}.stderr').read_text(),file=sys.stderr)
    raise SystemExit(result.returncode)
if __name__=='__main__':main()
