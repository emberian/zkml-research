#!/usr/bin/env python3
"""Trusted issuer/oracle fixture. No public seed, vectors, scores or score hashes."""
import argparse,json,os,secrets,sqlite3,sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parent/'journal'))
from common import read_json,write_json,require

def prepare(root,rows):
 private=Path(root)/'.private/oracle';private.mkdir(mode=0o700)
 ys=read_json(rows);queue=[];expected={}
 for n in range(1,41):
  x=[secrets.randbelow(255)-127 for _ in range(577)]
  write_json(private/f'input-{n:02d}.json',x,True)
  queue.append(x)
  if len(queue)>32:queue.pop(0)
  if n%10==0:
   row=n//10-1
   accumulator=[sum(v[j] for v in queue) for j in range(577)]
   expected[f'infer-{n:02d}']=sum(a*b for a,b in zip(accumulator,ys[row],strict=True))
 write_json(private/'expected.json',expected,True)
 return {'ok':True,'fresh_private_vectors':40,'dimension':577,'expected_private_scores':4,'public_seed':False}

def compare(root):
 private=Path(root)/'.private/oracle';expected=read_json(private/'expected.json')
 with sqlite3.connect(Path(root)/'.private/reader/answers.sqlite3') as db:
  got={r[0]:json.loads(r[1])['signed_score'] for r in db.execute('SELECT request_id,answer FROM private_decodes')}
 checks=[{'request_id':k,'expected':v,'actual':got.get(k),'matches':got.get(k)==v} for k,v in expected.items()]
 write_json(private/'private_comparisons.json',checks,True)
 require(expected==got,'privateIntegerOracle')
 return {'ok':True,'private_integer_comparisons':len(checks),'all_match':True}

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('mode',choices=['prepare','compare']);p.add_argument('--root',required=True);p.add_argument('--rows');a=p.parse_args()
 print(json.dumps(prepare(a.root,a.rows) if a.mode=='prepare' else compare(a.root)))
