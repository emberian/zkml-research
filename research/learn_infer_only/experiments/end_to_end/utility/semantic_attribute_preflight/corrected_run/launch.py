"""One logged preparation/corrected run, no implicit retries."""
import argparse,json,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent;BASE=ROOT.parents[3]/'adaptation_utility'
def main():
 p=argparse.ArgumentParser();p.add_argument('stage',choices=['prepare','run']);stage=p.parse_args().stage
 assert not (ROOT/f'{stage}.command.json').exists(),'Preserve one-attempt evidence'
 command=[str(BASE/'.venv/bin/python'),str(ROOT/f'{stage}.py')];t=time.perf_counter()
 with (ROOT/f'{stage}.stdout').open('w') as out,(ROOT/f'{stage}.stderr').open('w') as err:
  try:r=subprocess.run(command,stdout=out,stderr=err,timeout=1200);code=r.returncode
  except subprocess.TimeoutExpired:code=124
 row={'command':command,'returncode':code,'wall_seconds':time.perf_counter()-t,'timeout_seconds':1200}
 (ROOT/f'{stage}.command.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row))
 print((ROOT/f'{stage}.stdout').read_text());print((ROOT/f'{stage}.stderr').read_text());raise SystemExit(code)
if __name__=='__main__':main()
