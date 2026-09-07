"""Recorded deterministic fixture stages; no model/crypto executable dispatch."""
import argparse,json,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent;BASE=ROOT.parents[3]/'adaptation_utility'
def main():
 p=argparse.ArgumentParser();p.add_argument('stage',choices=['prepare','build','audit']);stage=p.parse_args().stage
 assert not (ROOT/f'{stage}.command.json').exists(),'Preserve stage evidence'
 command=[str(BASE/'.venv/bin/python'),'-B',str(ROOT/f'{stage}.py')];t=time.perf_counter()
 with (ROOT/f'{stage}.stdout').open('w') as out,(ROOT/f'{stage}.stderr').open('w') as err:
  r=subprocess.run(command,stdout=out,stderr=err,timeout=300)
 row={'command':command,'returncode':r.returncode,'wall_seconds':time.perf_counter()-t,'timeout_seconds':300}
 (ROOT/f'{stage}.command.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row))
 print((ROOT/f'{stage}.stdout').read_text()[-8000:]);print((ROOT/f'{stage}.stderr').read_text()[-3000:]);raise SystemExit(r.returncode)
if __name__=='__main__':main()
