#!/usr/bin/env python3
"""One sequential complete matched public emission pair; no cryptography."""
from pathlib import Path
import subprocess,time,hashlib,json,filecmp
P=Path(__file__).resolve().parent
FROZEN=P.parent/'query_arithmetic'
INPUT=P.parent/'query_runtime/results/case001/public_rows.json'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
pins=json.loads((FROZEN/'source_pins.json').read_text())
for name,digest in pins['sources'].items():assert sha(FROZEN/name)==digest
report={'input':str(INPUT),'input_sha256':sha(INPUT),'order':['baseline','fast'],'observations':[]}
for name,root,source in [('baseline',FROZEN,'EmitBfvQuery.lean'),('fast',P,'EmitBfvQueryFast.lean')]:
 out=P/'results'/(name+'001')
 assert not out.exists(),str(out)
 cmd=['/usr/bin/time','-l','lake','env','bash','-c','LEAN_PATH="$1/build:$LEAN_PATH" lean --root="$1" --run "$1/$2" "$3" "$4"','emit',str(root),source,str(out),str(INPUT)]
 (P/'results'/(name+'.command.json')).write_text(json.dumps(cmd,indent=2)+'\n')
 start=time.perf_counter()
 with (P/'results'/(name+'.stdout')).open('w') as stdout,(P/'results'/(name+'.stderr')).open('w') as stderr:
  run=subprocess.run(cmd,cwd='/Users/ember/dev/minidregg',stdout=stdout,stderr=stderr)
 seconds=time.perf_counter()-start
 report['observations'].append({'name':name,'seconds':seconds,'exit_code':run.returncode,'output_dir':str(out)})
 (P/'RESULTS.json').write_text(json.dumps(report,indent=2)+'\n')
 if run.returncode:raise SystemExit(run.returncode)
 print(name,seconds,'seconds',flush=True)
for name in ['template_ir2.json','trace.leu32','sample0.leu32']:
 a=P/'results/baseline001'/name;b=P/'results/fast001'/name;f=FROZEN/'artifacts'/name
 assert filecmp.cmp(a,b,shallow=False),name
 assert filecmp.cmp(a,f,shallow=False),'frozen '+name
 report[name]={'byte_identical':True,'bytes':a.stat().st_size,'sha256':sha(a),'matches_frozen':True}
report['speedup']=report['observations'][0]['seconds']/report['observations'][1]['seconds']
for name,digest in pins['sources'].items():assert sha(FROZEN/name)==digest
(P/'RESULTS.json').write_text(json.dumps(report,indent=2)+'\n')
print('Complete equality PASS; speedup',report['speedup'],flush=True)
