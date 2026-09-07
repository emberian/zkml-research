"""Retain the exact one-attempt teacher-preflight commands and outputs."""
import argparse,json,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent;BASE=ROOT.parents[2]/'adaptation_utility'
def main():
 p=argparse.ArgumentParser();p.add_argument('stage',choices=['prepare','run']);s=p.parse_args().stage
 assert not (ROOT/f'{s}.command.json').exists(),'No implicit retries'
 command=[str(BASE/'.venv/bin/python'),str(ROOT/'preflight.py'),s];t=time.perf_counter()
 with (ROOT/f'{s}.stdout').open('w') as out,(ROOT/f'{s}.stderr').open('w') as err:
  try:r=subprocess.run(command,stdout=out,stderr=err,timeout=1200);code=r.returncode
  except subprocess.TimeoutExpired:code=124
 result={'command':command,'returncode':code,'wall_seconds':time.perf_counter()-t,'timeout_seconds':1200}
 (ROOT/f'{s}.command.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
 print((ROOT/f'{s}.stdout').read_text());print((ROOT/f'{s}.stderr').read_text());raise SystemExit(code)
if __name__=='__main__':main()
