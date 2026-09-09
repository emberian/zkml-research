"""Read only the saved public evaluation-key protobuf and public Infer metadata."""
from pathlib import Path
import hashlib,json
P=Path(__file__).resolve().parent
ORIGIN=P.parents[1]/'learn_infer_only/experiments/end_to_end/nonlinear_successor_2026_09_08'
M=ORIGIN/'models/basic'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def fields(data):
 out={};i=0
 def varint():
  nonlocal i
  x=0
  for shift in range(0,70,7):
   b=data[i];i+=1;x|=(b&127)<<shift
   if b<128:return x
  raise ValueError('oversized varint')
 while i<len(data):
  tag=varint();field=tag>>3;wire=tag&7
  if wire==0:v=varint()
  elif wire==2:
   n=varint();v=data[i:i+n];assert len(v)==n;i+=n
  else:raise ValueError(('unexpected wire',wire))
  out.setdefault(field,[]).append(v)
 return out
def number(d,k):
 v=d.get(k,[0]);assert len(v)==1 and isinstance(v[0],int);return v[0]
key=fields((M/'evaluation.key').read_bytes());rows=[]
for raw in key.get(2,[]):
 g=fields(raw);assert len(g[1])==1;k=fields(g[1][0]);row=dict(exponent=number(g,2),ciphertext_level=number(k,4),ksk_level=number(k,5),log_base=number(k,6),c0_polynomials=len(k.get(1,[])),c1_serialized_polynomials=len(k.get(2,[])),seed_bytes=[len(x) for x in k.get(3,[])])
 assert row['ciphertext_level']==row['ksk_level']==row['log_base']==0
 assert row['c0_polynomials']==4 and row['c1_serialized_polynomials']==0 and row['seed_bytes']==[32]
 rows.append(row)
assert len(rows)==10
exponents=[pow(3,i,16384) for i in [8,16,32,64,128,256,512,1024,2048]]+[16383]
assert sorted(r['exponent'] for r in rows)==sorted(exponents)
state=json.loads((M/'model.json').read_text());ops=[json.loads(x) for x in (M/'operations.jsonl').read_text().splitlines()];infer=[r for r in ops if r['command']=='infer'];assert len(infer)==1 and state['revision']==9
paths=[M/'evaluation.key',M/'model.json',M/'queries/basic.json',Path(state['classes']['card_arrival']['acc']),M/'operations.jsonl',ORIGIN/'basic_crypto.py',ORIGIN/'model.py',ORIGIN/'config.json',ORIGIN/'crypto/src/main.rs',ORIGIN/'public_trace/basic.dot.ct',ORIGIN/'public_trace/basic-000.ct']
v=dict(scope='Read-only public protobuf metadata and saved model/query provenance. No secret-key path, crypto operation or private answer was read.',evaluation_key_ciphertext_level=number(key,3),evaluation_key_level=number(key,4),galois_keys=sorted(rows,key=lambda x:x['exponent']),rotation_order=exponents,branch='multi-prime RNS residue-row lift, four-term paired NTT MAC; no log-base bit decomposition, no context-downswitch at level0',revision=9,classes={'card_arrival':8},commitment_scope='saved model manifest hash; old basic run had no historical journal commit',infer=infer[0],files=[dict(path=str(f),bytes=f.stat().st_size,sha256=sha(f)) for f in paths])
(P/'PUBLIC_PROVENANCE.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps({k:v[k] for k in ['branch','rotation_order','revision']},indent=2));print('PUBLIC_PROVENANCE',sha(P/'PUBLIC_PROVENANCE.json'))
