#!/usr/bin/env python3
"""Check only this three-module bridge in a supplied prepared minidregg isolate."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess,time
MODULES=['Compiler/Ir2NearbyColumns.lean','Compiler/Ir2SelectedAirPcs.lean','Compiler/Ir2NearbyWitnesses.lean']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 p=argparse.ArgumentParser();p.add_argument('isolate',type=Path);a=p.parse_args();root=Path(__file__).resolve().parent
 records=[];dependencies={}
 for mod in MODULES:
  src=a.isolate/mod;before=sha(src)
  for dep in re.findall(r'^import ([\w.]+)',src.read_text(),re.M):
   path=dep.replace('.','/')+'.lean';dp=a.isolate/path;op=a.isolate/'.lake/build/lib/lean'/Path(path).with_suffix('.olean')
   dependencies[path]={'source_sha256':sha(dp),'olean_sha256':sha(op)}
  out=a.isolate/'.lake/build/lib/lean'/Path(mod).with_suffix('.olean')
  cmd=['lake','env','lean','-o',str(out),mod];start=time.monotonic();r=subprocess.run(cmd,cwd=a.isolate,text=True,capture_output=True)
  log='checks/'+Path(mod).stem+'.log';(root/log).write_text(r.stdout+r.stderr)
  record={'path':mod,'command':cmd,'cwd':str(a.isolate),'exit_code':r.returncode,'elapsed_s':time.monotonic()-start,'source_sha256':before,'source_stable':before==sha(src),'olean_sha256':sha(out) if out.exists() else None,'axiom_guards':src.read_text().count('#guard_msgs'),'log':log}
  records.append(record);print(json.dumps(record),flush=True)
  if r.returncode or not record['source_stable']:raise SystemExit(1)
 r=subprocess.run(['bash','scripts/check-import-boundary.sh'],cwd=a.isolate,text=True,capture_output=True)
 (root/'checks/import-boundary.log').write_text(r.stdout+r.stderr)
 checks={'classification':'EXECUTED','modules':records,'direct_dependencies_at_import':dependencies,'import_boundary':{'command':['bash','scripts/check-import-boundary.sh'],'exit_code':r.returncode,'log':'checks/import-boundary.log'},'scope':'Changed modules only; exact guard-pinned kernel checks. No broad rebuild, native execution, or implementation refinement claimed.'}
 (root/'CHECKS.json').write_text(json.dumps(checks,indent=2)+'\n')
 raise SystemExit(r.returncode)
if __name__=='__main__':main()
