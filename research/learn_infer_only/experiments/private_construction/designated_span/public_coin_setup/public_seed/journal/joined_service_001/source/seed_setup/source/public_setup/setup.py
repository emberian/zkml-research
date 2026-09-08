#!/usr/bin/env python3
"""Honest public-field-coin setup; no scalar master or projection dealer path.

The retained transcript is accepted values only. OS RNG state is not published.
Legacy dealer commands in the frozen arithmetic module are never called here.
"""
from pathlib import Path
import argparse,base64,hashlib,json,os,secrets,subprocess,sys,time
HERE=Path(__file__).resolve().parent
CORE=HERE/'source/crypto'
sys.path.insert(0,str(CORE))
import crypto as c
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PrivateKey,Ed25519PublicKey

DOMAIN='public-coin-fixed-slot-announcement-v1'


def sample_interval(lower,upper):
 """Literal unbiased rejection from independent ideal bit words [lower,upper).
 secrets.randbits is the concrete OS-backed implementation; its seed/state is
 outside the accepted-public-value transcript. Zero tau and U=+/-1 are valid.
 """
 bits=(upper-1).bit_length()
 while True:
  candidate=secrets.randbits(bits)
  if lower<=candidate<upper:return candidate


def freeze():
 return {name:c.sha((CORE/name).read_bytes()) for name in ['crypto.py','group.py','native_pow.py','rows.json']}


def native_pin():
 from native_pow import LIBRARY
 return {'path':str(LIBRARY),'sha256':c.sha(LIBRARY.read_bytes())}


def saved(path,obj,private=False):c.save(path,c.canonical(obj),private)


def determinant(matrix):
 a=[row[:] for row in matrix];n=len(a);previous=1;sign=1
 for k in range(n-1):
  pivot=next(i for i in range(k,n) if a[i][k])
  if pivot!=k:a[k],a[pivot]=a[pivot],a[k];sign=-sign
  current=a[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):
    numerator=a[i][j]*current-a[i][k]*a[k][j]
    c.require(numerator%previous==0,'exact determinant division');a[i][j]=numerator//previous
   a[i][k]=0
  previous=current
 return sign*a[-1][-1]


def matrices():
 n=c.K;yp=[row[:n] for row in c.ROWS]
 det=determinant(yp);c.require(det==-812032080 and det%c.Q!=0,'fixed first16 determinant')
 aug=[[x%c.Q for x in row]+[int(i==j) for j in range(n)] for i,row in enumerate(yp)]
 for col in range(n):
  pivot=next(i for i in range(col,n) if aug[i][col])
  aug[col],aug[pivot]=aug[pivot],aug[col]
  multiplier=pow(aug[col][col],-1,c.Q);aug[col]=[x*multiplier%c.Q for x in aug[col]]
  for i in range(n):
   if i!=col:
    multiplier=aug[i][col];aug[i]=[(x-multiplier*y)%c.Q for x,y in zip(aug[i],aug[col],strict=True)]
 inverse=[row[n:] for row in aug]
 c.require(all(sum(yp[i][k]*inverse[k][j] for k in range(n))%c.Q==int(i==j) for i in range(n) for j in range(n)),'matrix inverse over Fq')
 completion=[[-sum(inverse[i][k]*c.ROWS[k][j] for k in range(n))%c.Q for j in range(n,c.D)] for i in range(n)]
 c.require(all((sum(yp[i][k]*completion[k][j-n] for k in range(n))+c.ROWS[i][j])%c.Q==0 for i in range(n) for j in range(n,c.D)),'YpL plus Yf zero')
 return inverse,completion,det


def complete(public_A,tau,field_U):
 inverse,completion,det=matrices()
 for value in public_A:c.subgroup(value)
 c.require(len(tau)==c.K and all(0<=t<c.Q for t in tau),'tau field')
 c.require(len(field_U)==c.D-c.K and all(1<=u<c.P for u in field_U),'nonzero field U')
 free=[u*u%c.P for u in field_U]
 targets=[A*c.exp(c.G,t)%c.P for A,t in zip(public_A,tau,strict=True)]
 pivots=[]
 for i in range(c.K):
  value=1
  for base,exponent in zip(targets,inverse[i],strict=True):
   if exponent:value=value*c.exp(base,exponent)%c.P
  for base,exponent in zip(free,completion[i],strict=True):
   if exponent:value=value*c.exp(base,exponent)%c.P
  pivots.append(value)
 return pivots+free,det


def registry(path,expected=None):
 raw=c.read(path,100000);body=c.parse(raw)
 c.require(raw==c.canonical(body) and (expected is None or c.sha(raw)==expected),'registry canonical/pin')
 c.exact(body,['schema','params_id','slots'])
 c.require(body['schema']=='public-coin-fixed-slot-registry-v1' and body['params_id']==c.PARAMS_ID and len(body['slots'])==c.K,'fixed registry')
 for i,slot in enumerate(body['slots']):
  c.exact(slot,['row_id','row_sha256','verification_key'])
  c.require(slot['row_id']==i and slot['row_sha256']==c.ROW_HASHES[i] and len(bytes.fromhex(slot['verification_key']))==32,'fixed slot')
 return body,c.sha(raw)


def check_announcements(reg,announcements):
 c.require(len(announcements)==c.K,'all announcements precede public sampling')
 values=[]
 for i,announcement in enumerate(announcements):
  c.exact(announcement,['domain','payload','signature']);payload=announcement['payload']
  c.exact(payload,['schema','params_id','row_id','row_sha256','A'])
  c.require(announcement['domain']==DOMAIN and payload['schema']=='public-coin-recipient-announcement-v1' and payload['params_id']==c.PARAMS_ID and payload['row_id']==i and payload['row_sha256']==c.ROW_HASHES[i],'announcement slot')
  message=c.canonical({'domain':DOMAIN,'payload':payload})
  Ed25519PublicKey.from_public_bytes(bytes.fromhex(reg['slots'][i]['verification_key'])).verify(base64.b64decode(announcement['signature'],validate=True),message)
  values.append(c.unhex(payload['A']))
 return values


def context_body(h,public_A,tau):
 hex_h=[c.hx(x) for x in h];setup_id=c.digest(c.bootstrap_body(hex_h))
 return {'schema':'resident-designated-context-v1','params_id':c.PARAMS_ID,'setup_id':setup_id,'rows':c.ROWS,'h':hex_h,
         'recipients':[c.registration(setup_id,i,A,t) for i,(A,t) in enumerate(zip(public_A,tau,strict=True))]}


def execute(a):
 if a.command=='auth-init':
  directory=Path(a.private);directory.mkdir(parents=True,mode=0o700);slots=[]
  for i in range(c.K):
   key=Ed25519PrivateKey.generate();c.save(directory/f'r{i:02d}.sigkey',key.private_bytes_raw(),True)
   slots.append({'row_id':i,'row_sha256':c.ROW_HASHES[i],'verification_key':key.public_key().public_bytes_raw().hex()})
  obj={'schema':'public-coin-fixed-slot-registry-v1','params_id':c.PARAMS_ID,'slots':slots};saved(a.out,obj)
  return {'registration_slots':c.K,'registry_sha256':c.digest(obj),'authentication_independent_of_crypto_coins':True}
 if a.command=='recipient-init':
  reg,_=registry(a.registry,a.registry_sha256);i=a.row;c.require(0<=i<c.K,'row')
  key=Ed25519PrivateKey.from_private_bytes(c.read(a.auth_key,32))
  c.require(key.public_key().public_bytes_raw().hex()==reg['slots'][i]['verification_key'],'pinned recipient auth key')
  scalar=sample_interval(0,c.Q);A=c.exp(c.G,scalar)
  c.save(a.pending,scalar.to_bytes(c.WIDTH,'big'),True)
  payload={'schema':'public-coin-recipient-announcement-v1','params_id':c.PARAMS_ID,'row_id':i,'row_sha256':c.ROW_HASHES[i],'A':c.hx(A)}
  announcement={'domain':DOMAIN,'payload':payload,'signature':base64.b64encode(key.sign(c.canonical({'domain':DOMAIN,'payload':payload}))).decode()}
  saved(a.out,announcement)
  return {'row_id':i,'public_announcement_sha256':c.digest(announcement),'recipient_owned_scalar_count':1}
 if a.command=='public-build':
  reg,reg_sha=registry(a.registry,a.registry_sha256)
  announcements=[c.read_json(Path(a.announcements)/f'r{i:02d}.json',exact=True) for i in range(c.K)]
  public_A=check_announcements(reg,announcements)
  # Matrix selection and verified rank precede all public sampling.
  matrices()
  tau=[sample_interval(0,c.Q) for _ in range(c.K)]
  field_U=[sample_interval(1,c.P) for _ in range(c.D-c.K)]
  h,det=complete(public_A,tau,field_U);body=context_body(h,public_A,tau);saved(a.context,body)
  ctx={'body':body,'id':c.digest(body),'h':h};c.save(a.zero,c.pack(ctx,c.STATE,[1]*(c.D+1)))
  transcript={'schema':'designated-public-field-coins-v1','params_id':c.PARAMS_ID,'context_id':ctx['id'],
   'dimension':c.D,'row_count':c.K,'rows_sha256':c.digest(c.ROWS),'pivot_columns':list(range(c.K)),
   'free_columns':list(range(c.K,c.D)),'integer_pivot_determinant':det,'registry_sha256':reg_sha,
   'announcements':announcements,'tau':[c.hx(t) for t in tau],'U':[c.hx(u) for u in field_U],
   'sampling':'direct unbiased bit-word rejection: tau in [0,q), U in [1,p); U is not g to a sampled scalar',
   'transcript_scope':'accepted values only; no RNG seed/state/rejected tape; physical timing excluded',
   'setup_source_sha256':c.sha(Path(__file__).read_bytes()),'crypto_sources':freeze(),'native_dependency':native_pin()}
  saved(a.transcript,transcript)
  return {'context_id':ctx['id'],'context_bytes':len(c.canonical(body)),'transcript_sha256':c.digest(transcript),'transcript_bytes':len(c.canonical(transcript)),
   'pivot_rank':c.K,'integer_pivot_determinant':det,'public_field_samples':c.D-c.K,'public_tau_samples':c.K,
   'scalar_master_computed_in_this_path':False,'scalar_projection_delivery_computed_in_this_path':False}
 if a.command=='verify-public':
  transcript=c.read_json(a.transcript,exact=True);reg,reg_sha=registry(a.registry,a.registry_sha256)
  c.require(transcript['registry_sha256']==reg_sha and transcript['setup_source_sha256']==c.sha(Path(__file__).read_bytes()) and transcript['crypto_sources']==freeze() and transcript['native_dependency']==native_pin(),'transcript source/registry pins')
  c.require(transcript['params_id']==c.PARAMS_ID and transcript['rows_sha256']==c.digest(c.ROWS) and transcript['pivot_columns']==list(range(c.K)) and transcript['free_columns']==list(range(c.K,c.D)),'transcript fixed coordinates')
  public_A=check_announcements(reg,transcript['announcements'])
  tau=[c.unhex(t,scalar=True) for t in transcript['tau']];field_U=[c.unhex(u) for u in transcript['U']]
  h,det=complete(public_A,tau,field_U);expected=context_body(h,public_A,tau)
  raw=c.read(a.context,1_000_000)
  c.require(raw==c.canonical(expected) and c.sha(raw)==transcript['context_id'] and det==transcript['integer_pivot_determinant'],'complete public transcript recomputation')
  return {'ok':True,'complete_context_byte_match':True,'context_id':c.sha(raw),'transcript_sha256':c.digest(transcript),'pivot_inverse_and_completion_equations_checked':True,'no_private_file_read_by_public_verifier':True}
 raise ValueError('command')


def main():
 parser=argparse.ArgumentParser();subs=parser.add_subparsers(dest='command',required=True)
 specs={'auth-init':['private','out'],'recipient-init':['registry','registry-sha256','row','auth-key','pending','out'],
        'public-build':['registry','registry-sha256','announcements','context','transcript','zero'],
        'verify-public':['registry','registry-sha256','context','transcript']}
 for command,flags in specs.items():
  sub=subs.add_parser(command)
  for flag in flags:sub.add_argument('--'+flag,required=True,type=int if flag=='row' else str)
 a=parser.parse_args();started=time.perf_counter_ns();c.ENGINE=c.NativePow(c.P)
 try:
  result=execute(a);result.update(process_work_ns=time.perf_counter_ns()-started,counts=dict(c.COUNTS));print(json.dumps(result))
 finally:c.ENGINE.close()
if __name__=='__main__':main()
