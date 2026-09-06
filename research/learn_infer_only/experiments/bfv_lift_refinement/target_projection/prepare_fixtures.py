#!/usr/bin/env python3
"""Extract actual retained Rust coefficient rows and pin the unchanged source witness."""
import gzip,hashlib,json,sys,time
from pathlib import Path
from math import prod
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent))
from fhe_scaler_model import ScalerModel
start=time.monotonic();engine=ROOT.parent/'engine_probe/full-coefficients.jsonl.gz';source=ROOT.parent/'source_certificate/retained-inputs.json.gz'
source_fixture=json.loads(gzip.decompress(source.read_bytes()));initial=source_fixture['cases'][0]['initial_variables']
(ROOT/'captured-source-variables.json').write_text(json.dumps(initial)+'\n')
cases=[];count=0;limb_checks=0
for line in gzip.open(engine,'rt'):
 try:r=json.loads(line)
 except json.JSONDecodeError:continue
 if r.get('kind')!='full_unrelinearized_tensor':continue
 base=r['base'];q=prod(base);model=ScalerModel(r['extended_base'],base,r['t'],q)
 for c,poly in enumerate(r['product_extended']):
  for k in range(r['N']):
   residues=[row[k] for row in poly['rows']];actual=[row[k] for row in r['output'][c]['rows']]
   expected,details=model.scale(residues);y=details['integer']%q
   assert expected==actual and all(0<=a<p and y%p==a for a,p in zip(actual,base))
   count+=1;limb_checks+=len(base)
   if r['N']==4096 and c==0 and k==0 and ('rounding_boundary' in r['label'] or 'negative' in r['label']):
    cases.append(dict(label=r['label'],coefficient=[c,k],source_residues=residues,source_integer=str(details['integer']),canonical_output=y,actual_target_limbs=actual,target_primes=base))
assert count>80000 and cases
cap=next(c for c in cases if c['label']=='N4096_structured_rounding_boundary_0')
assert cap['source_residues']==list(map(int,source_fixture['source_residues']))
assert cap['actual_target_limbs']==[172481]*3 and cap['canonical_output']==source_fixture['pinned_output']
result=dict(label='EXECUTED retained actual Rust target limbs versus deterministic integer source projection',command=[sys.executable,str(Path(__file__).resolve())],engine_fixture_sha256=hashlib.sha256(engine.read_bytes()).hexdigest(),frozen_source_fixture_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),source_assignment_sha256=hashlib.sha256(json.dumps(initial).encode()).hexdigest(),coefficient_rows=count,target_limb_checks=limb_checks,cases=cases,elapsed_seconds=time.monotonic()-start)
(ROOT/'actual-coefficients.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k!='cases'},indent=2))
