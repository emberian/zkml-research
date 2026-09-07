"""One logged stage; no implicit retries or overwriting completed evidence."""
import argparse,json,subprocess,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent;BASE=ROOT.parents[2]/'adaptation_utility'
def main():
 p=argparse.ArgumentParser();p.add_argument('stage',choices=['prepare','e5_train','fit_select','e5_test','smol_test','evaluate','audit']);stage=p.parse_args().stage
 assert not (ROOT/f'{stage}.command.json').exists(),'Preserve process evidence'
 python=BASE/'.venv/bin/python'
 if stage in ['prepare','fit_select','evaluate']:command=[str(python),str(ROOT/'run.py'),stage]
 elif stage=='audit':command=[str(python),str(ROOT/'audit.py')]
 else:command=[str(python),str(ROOT/'extract.py'),stage]
 t=time.perf_counter()
 with (ROOT/f'{stage}.stdout').open('w') as out,(ROOT/f'{stage}.stderr').open('w') as err:r=subprocess.run(command,stdout=out,stderr=err)
 row={'command':command,'cwd':str(Path.cwd()),'returncode':r.returncode,'wall_seconds':time.perf_counter()-t}
 (ROOT/f'{stage}.command.json').write_text(json.dumps(row,indent=2)+'\n');print(json.dumps(row))
 print((ROOT/f'{stage}.stdout').read_text());print((ROOT/f'{stage}.stderr').read_text());raise SystemExit(r.returncode)
if __name__=='__main__':main()
