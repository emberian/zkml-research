#!/usr/bin/env python3
"""Cross-check full-byte EMA against the existing HE bit-circuit source.
Public arithmetic experiment; no encryption/receipt/storage is implemented here.
"""
from pathlib import Path
import hashlib,importlib.util,json,time
R=Path(__file__).resolve().parents[3]
src=R/'experiments/he_closure_costs/ema_bits.py'
spec=importlib.util.spec_from_file_location('he_ema',src)
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)
start=time.time();pairs=0;changed=0;negative_remainder=0;bad_neighbor=0
for c in range(-128,128):
 for u in range(-128,128):
  out=m.ema_word(c,u,m.Counter())
  want=(7*c+u)//8
  assert out==want and -128<=out<=127
  C,U,N=c+128,u+128,out+128
  r=7*C+U-8*N
  assert 0<=r<8 and 7*C+U==8*N+r
  # Neighbor remains byte-ranged but cannot have an in-range remainder.
  forged=N+1 if N<255 else N-1
  assert not 0<=7*C+U-8*forged<8
  pairs+=1;changed+=out!=c;negative_remainder+=(7*c+u)<0 and r!=0;bad_neighbor+=1
histories=[]
for inputs in ([120,-120],[-120,120]):
 c=0;states=[c]
 for u in inputs:c=m.ema_word(c,u,m.Counter());states.append(c)
 histories.append(dict(inputs=inputs,states=states))
assert histories[0]['states']==[0,15,-2] and histories[1]['states']==[0,-15,1]
rec=dict(claim='EXECUTED full signed-byte public bit-circuit/QR cross-check',
 source=str(src),source_sha256=hashlib.sha256(src.read_bytes()).hexdigest(),pairs=pairs,
 changed_state_pairs=changed,negative_nonzero_remainder_pairs=negative_remainder,
 wrong_neighbor_posts_refused=bad_neighbor,histories=histories,
 minimum_boundary=[m.ema_word(-128,-128,m.Counter()),m.ema_word(-128,127,m.Counter())],
 seconds=time.time()-start,limitations=['No ciphertext operation, FS receipt, or physical storage is checked here.',
 'Extends earlier HE Python range [-127,127] to [-128,127]; TFHE encrypted execution remains the separately recorded4updates.'])
Path(__file__).with_name('audit.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps(rec,indent=2))
