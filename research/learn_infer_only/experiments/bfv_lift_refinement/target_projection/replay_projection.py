#!/usr/bin/env python3
"""Replay actual existing descriptors and explicit two-assignment boundary pins."""
import gzip,hashlib,json,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent/'source_certificate'))
from replay_descriptor import run

def read(root,name):
 p=root/name
 if not p.exists():p=p.with_suffix(p.suffix+'.gz')
 raw=gzip.decompress(p.read_bytes()) if p.suffix=='.gz' else p.read_bytes()
 return json.loads(raw),hashlib.sha256(raw).hexdigest()
def decoded(a,j):return sum(a[19*j+k]*64**k for k in range(19))
def main():
 start=time.monotonic();d,dh=read(ROOT,'optimized-descriptor.json');cases,fh=read(ROOT,'retained-inputs.json');layout,_=read(ROOT,'layout.json')
 src=ROOT.parent/'source_certificate';sd,sdh=read(src,'optimized-descriptor.json');sc,sfh=read(src,'retained-inputs.json');sa=sc['cases'][0]['initial_variables'];source_ok=run(sd,sa)
 source_groups=[sum(sa[22*j+k]*64**k for k in range(22)) for j in range(21)]
 assert source_ok and source_groups[:6]==list(map(int,sc['source_residues'])) and source_groups[18]==172481
 results=[]
 for case in cases['cases']:
  a=case['initial_variables'];accepted=run(d,a);assert accepted==case['expected']
  x=[decoded(a,j) for j in range(10)];violated=[j for j,row in enumerate(layout['rows']) if row['left_constant']+sum(v*c for v,c in zip(x,row['left']))!=row['right_constant']+sum(v*c for v,c in zip(x,row['right']))]
  if case['label']=='coherent_wrong_limb':assert violated==[0]
  if case['label']=='coherent_noncanonical_limb':assert violated==[1]
  if case['label']=='disconnected_valid_projection':assert accepted and x[0]!=172481
  composite=source_ok and x[0]==172481 and [x[1],x[4],x[7]]==[172481]*3 and accepted
  assert composite==(case['label']=='captured_projection')
  results.append(dict(label=case['label'],projection_accepts=accepted,unchanged_source_accepts=source_ok,composite_captured_claim_accepts=composite,violated_projection_rows=violated))
 report=dict(label='EXECUTED independent replay of existing target/source descriptors and concrete boundary pins',command=[sys.executable,str(Path(__file__).resolve())],source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),projection_descriptor_uncompressed_sha256=dh,projection_inputs_uncompressed_sha256=fh,frozen_source_descriptor_uncompressed_sha256=sdh,frozen_source_inputs_uncompressed_sha256=sfh,cases=results,elapsed_seconds=time.monotonic()-start)
 (ROOT/'replay-results.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
