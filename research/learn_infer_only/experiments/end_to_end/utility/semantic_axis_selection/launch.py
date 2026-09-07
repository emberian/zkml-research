"""Recorded one-attempt stage invocation, existing environment only."""
import argparse,json,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent;BASE=ROOT.parents[2]/'adaptation_utility'
def main():
 p=argparse.ArgumentParser();p.add_argument('stage',choices=['prepare','score','evaluate','audit']);stage=p.parse_args().stage
 assert not (ROOT/f'{stage}.command.json').exists(),'Preserve stage evidence'
 command=[str(BASE/'.venv/bin/python'),'-B',str(ROOT/f'{stage}.py')];t=time.perf_counter()
 with (ROOT/f'{stage}.stdout').open('w') as out,(ROOT/f'{stage}.stderr').open('w') as err:
  try:r=subprocess.run(command,stdout=out,stderr=err,timeout=1800);code=r.returncode
  except subprocess.TimeoutExpired:code=124
 row={'command':command,'returncode':code,'wall_seconds':time.perf_counter()-t,'timeout_seconds':1800}
 (ROOT/f'{stage}.command.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row),flush=True)
 print((ROOT/f'{stage}.stdout').read_text()[-14000:]);print((ROOT/f'{stage}.stderr').read_text()[-3000:]);raise SystemExit(code)
if __name__=='__main__':main()
