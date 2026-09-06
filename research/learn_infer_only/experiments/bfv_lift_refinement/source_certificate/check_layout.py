#!/usr/bin/env python3
"""Independent integer balance audit and exact baseline layout bill; not a new AIR."""
import hashlib,json,random,sys,time
from pathlib import Path
from math import prod
ROOT=Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT.parent))
from fhe_scaler_model import ScalerModel
base=[68719403009,68719230977,137438822401];ext=base+[4611686018427322369,4611686018427289601,4611686018427215873];q=prod(base);s=ScalerModel(ext,base,1032193,q);BG=1<<126;BF=1<<127;WO=1<<65;UO=1<<120
layout=json.loads((ROOT/'layout.json').read_text())
def cert(r):
 _,d=s.scale(r);v=d['v'];w=d['w'];y=d['integer']%q;u=d['integer']//q
 rg=(2*sum(a*b for a,b in zip(r,s.tgarner))+BG)%(2*BG)
 rf=(2*sum(a*b for a,b in zip(r,s.tomega))+BF)%(2*BF)
 return r+[p-1-a for a,p in zip(r,ext)]+[v,rg,2*BG-1-rg,w+WO,rf,2*BF-1-rf,y,q-1-y,u+UO]
def accepts(x):
 return len(x)==21 and all(0<=a<64**22 for a in x) and all(row['left_constant']+sum(a*b for a,b in zip(row['left'],x))==row['right_constant']+sum(a*b for a,b in zip(row['right'],x)) for row in layout['rows'])
start=time.monotonic();rng=random.Random(20260906);vectors=[[0]*6,[p-1 for p in ext]]+[[rng.randrange(p) for p in ext] for _ in range(1000)]
captured=json.loads((ROOT.parent/'captured-rounding-witness.json').read_text())['rests'];vectors.append(captured)
wrong=0
for r in vectors:
 x=cert(r);assert accepts(x)
 bad=x.copy();bad[18]=(bad[18]+1)%q;bad[19]=q-1-bad[18];assert not accepts(bad);wrong+=1
x=cert(captured);assert x[18]==172481
near=x.copy();near[18]=172480;near[19]=q-1-172480;assert not accepts(near)
assert 63+462*63*63+(2**15-1)<2013265921
assert 63+64*(2**15-1)<2013265921
# Direct existing-gadget formula:6+1 scalar assertions; each weighted gadget has
# 57*(6+1)+58*(15+1)+2+57 assertions. Shared result ranges are repeated by the baseline.
zero_checks=462*7+24*(57*7+58*16+2+57)
result=dict(label='EXECUTED integer balance specification and DERIVED conservative compiler layout bill',command=[sys.executable,str(Path(__file__).resolve())],source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),layout_sha256=hashlib.sha256((ROOT/'layout.json').read_bytes()).hexdigest(),canonical_cases=len(vectors),wrong_outputs_refused=wrong,captured_source_output=172481,wrong_nearest172480_refused=True,groups=21,scalar_digits=462,scalar_bit_wires=2772,balance_rows=12,weighted_accumulators=24,columns=57,carry_bits=15,variables=30294,unoptimized_zero_assertions_formula=zero_checks,left_column_no_wrap_bound=63+462*63*63+(2**15-1),right_column_no_wrap_bound=63+64*(2**15-1),naive_full_tensor_variable_repetitions=30294*3*4096,elapsed_seconds=time.monotonic()-start,
 scope='No committed-ciphertext provenance, integer convolution/NTT, Shoup, proof protocol, relin/noise, secrecy or latency result. Uniform132-bit groups are a conservative first emitted layout, not a lower bound.')
(ROOT/'layout-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
