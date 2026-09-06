#!/usr/bin/env python3
"""Close the word-level target path against the integer model and retained Rust rows."""
import hashlib,json,random,sys,time
from math import prod
from pathlib import Path
from word_model import shoup,barrett,reduce1
ROOT=Path(__file__).resolve().parent;sys.path.insert(0,str(ROOT.parent))
from fhe_scaler_model import ScalerModel
B=1<<64;M=B*B;U=1<<256;base=[68719403009,68719230977,137438822401];extended=base+[4611686018427322369,4611686018427289601,4611686018427215873];q=prod(base);model=ScalerModel(extended,base,1032193,q)
def source_words(r):
 assert len(r)==6 and all(0<=a<p for a,p in zip(r,extended))
 tg=sum(a*b for a,b in zip(r,model.tgarner));v=(((tg%U)>>(model.shift-1))%M+1)//2
 T=sum(a*b for a,b in zip(r,model.tomega));wrapped=T%U;negative=(wrapped>>191)>0
 pre=(((U-1-wrapped)>>126)%M) if negative else ((wrapped>>126)%M)
 assert pre+1<M;mag=(pre+1)//2
 assert 0<=v<M and 0<=mag<M and model.tgamma==0
 result=[];accs=[]
 for p in base:
  vred=reduce1(B,p,barrett(B,p,v)[0]);lg=shoup(B,p,vred,model.gamma%p)[0]
  lw=barrett(B,p,mag)[0];acc=2*p-lg+(2*p-lw if negative else lw)
  for a,om in zip(r,model.omega):acc+=shoup(B,p,a,om%p)[0]
  assert 0<=acc<=16*p and acc<M
  result.append(reduce1(B,p,barrett(B,p,acc%M)[0]));accs.append(acc)
 return result,dict(negative=negative,magnitude=mag,v=v,max_accumulator=max(accs))
start=time.monotonic();rng=random.Random(2026090603);rows=[[0]*6,[p-1 for p in extended]]+[[rng.randrange(p) for p in extended] for _ in range(1000)];neg=pos=0;maxacc=0
for r in rows:
 got,d=source_words(r);expected,_=model.scale(r);assert got==expected
 neg+=d['negative'];pos+=not d['negative'];maxacc=max(maxacc,d['max_accumulator'])
actual=json.loads((ROOT.parent/'target_projection/actual-coefficients.json').read_text());captured=[]
for item in actual['cases']:
 got,d=source_words(item['source_residues']);assert got==item['actual_target_limbs']
 captured.append(dict(label=item['label'],source_integer=item['source_integer'],actual_target_limbs=got,**d))
files=[Path(__file__),ROOT/'word_model.py',ROOT.parent/'fhe_scaler_model.py'];result=dict(label='EXECUTED complete handwritten source-word path versus integer model and retained actual Rust target arrays',command=[sys.executable,str(Path(__file__).resolve())],sources=[dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in files],random_and_endpoint_rows=len(rows),negative_sign_rows=neg,positive_sign_rows=pos,target_checks=3*(len(rows)+len(captured)),max_observed_u128_accumulator=str(maxacc),actual_retained_rows=captured,source_arithmetic_calls_per_three_target_row=dict(lazy_shoup=21,lazy_barrett=9,reduce_one=6),extra_emitted_constraints=0,elapsed_seconds=time.monotonic()-start)
(ROOT/'source-word-results.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['sources','actual_retained_rows']},indent=2))
