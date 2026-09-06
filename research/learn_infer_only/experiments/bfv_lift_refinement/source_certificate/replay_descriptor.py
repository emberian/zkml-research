#!/usr/bin/env python3
"""Replay the existing compiler's serialized gate descriptor; no alternate AIR."""
import gzip,hashlib,json,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def read(name):
 p=ROOT/name
 if not p.exists():p=p.with_suffix(p.suffix+'.gz')
 payload=gzip.decompress(p.read_bytes()) if p.suffix=='.gz' else p.read_bytes()
 return json.loads(payload),hashlib.sha256(payload).hexdigest()
def run(d,initial):
 p=d['p'];assert len(initial)==d['nVars'];assert all(0<=x<p for x in initial)
 values=list(initial)+[0]*(d['nWires']-d['nVars']);known=set(range(d['nVars']))
 def get(w):
  assert len(w)==1
  if 'c' in w:assert 0<=w['c']<p;return w['c']
  assert w['w'] in known
  return values[w['w']]
 for g in d['gates']:
  out=g['out'];assert d['nVars']<=out<d['nWires'] and out not in known
  a,b=get(g['a']),get(g['b']);assert g['op'] in ('add','mul')
  values[out]=(a+b if g['op']=='add' else a*b)%p;known.add(out)
 return all(get(z)==0 for z in d['zeros'])
def group(initial,j):return sum(initial[22*j+k]*64**k for k in range(22))
def main():
 start=time.monotonic();d,dh=read('optimized-descriptor.json');fixture,fh=read('retained-inputs.json');layout,_=read('layout.json');result=[]
 for case in fixture['cases']:
  inputs=case['initial_variables'];ok=run(d,inputs);assert ok==case['expected'],case['label']
  x=[group(inputs,j) for j in range(21)]
  pins=x[:6]==list(map(int,fixture['source_residues'])) and x[18]==fixture['pinned_output']
  violated=[i for i,row in enumerate(layout['rows']) if row['left_constant']+sum(a*b for a,b in zip(row['left'],x))!=row['right_constant']+sum(a*b for a,b in zip(row['right'],x))]
  if case['label']=='correction_range_attack':assert violated==[9]
  result.append(dict(label=case['label'],descriptor_accepts=ok,pinned_source_claim_accepts=ok and pins,violated_integer_balance_rows=violated))
 report=dict(label='EXECUTED independent replay of existing optimized descriptor and retained public synthetic fixtures',command=[sys.executable,str(Path(__file__).resolve())],source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),descriptor_uncompressed_sha256=dh,inputs_uncompressed_sha256=fh,gates=len(d['gates']),zero_checks=len(d['zeros']),cases=result,elapsed_seconds=time.monotonic()-start)
 (ROOT/'replay-results.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
if __name__=='__main__':main()
