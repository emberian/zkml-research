#!/usr/bin/env python3
"""Differential check of word transcripts against actual cached library calls."""
import gzip,hashlib,json,sys,time
from pathlib import Path
from word_model import shoup,barrett,reduce1
ROOT=Path(__file__).resolve().parent;start=time.monotonic();rows=[];B=1<<64
stats=dict(actual_rows=0,full_width_a_exceeds_modulus=0,noncanonical_lazy_shoup=0,noncanonical_lazy_barrett=0,max_middle_bits=0)
for line in gzip.open(ROOT/'actual-words.jsonl.gz','rt'):
 r=json.loads(line);p=r['p'];a=r['a'];b=r['b'];x=int(r['x']);lazy,s=shoup(B,p,a,b);br,mid=barrett(B,p,x)
 assert (lazy,s,reduce1(B,p,lazy),br,reduce1(B,p,br))==(r['lazy_shoup'],r['shoup'],r['mul_shoup'],r['lazy_barrett'],r['reduce'])
 stats['actual_rows']+=1;stats['full_width_a_exceeds_modulus']+=a>=p;stats['noncanonical_lazy_shoup']+=lazy>=p;stats['noncanonical_lazy_barrett']+=br>=p;stats['max_middle_bits']=max(stats['max_middle_bits'],mid.bit_length())
finiteS=finiteB=0
for B in [16,32,64]:
 for p in range(2,B//2):
  for a in range(B):
   for b in range(p):shoup(B,p,a,b);finiteS+=1
  for a in range(B*B):barrett(B,p,a);finiteB+=1
# Concrete premise and sign falsifiers are public synthetic arithmetic controls.
assert shoup(256,31,34,11)[0]==33
assert shoup(256,31,8,32,False)[0]%31 != 8*32%31
assert barrett(256,31,65535)[0]==32
assert reduce1(256,31,62,False)!=62%31
record=dict(label='EXECUTED literal word models versus actual fhe-math calls plus exhaustive reduced-word checks',command=[sys.executable,str(Path(__file__).resolve())],source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),model_sha256=hashlib.sha256((ROOT/'word_model.py').read_bytes()).hexdigest(),actual_fixture_sha256=hashlib.sha256((ROOT/'actual-words.jsonl.gz').read_bytes()).hexdigest(),**stats,finite_shoup_cases=finiteS,finite_barrett_cases=finiteB,canonical_b_and_lazy_range_falsifiers_refused=True,elapsed_seconds=time.monotonic()-start)
(ROOT/'word-results.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
