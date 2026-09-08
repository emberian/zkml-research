#!/usr/bin/env python3
"""Known fixture and direct integer oracle; imports no cryptographic implementation."""
from pathlib import Path
import argparse,json,os,sqlite3
HERE=Path(__file__).resolve().parent

def write(path,obj):
 path=Path(path);path.write_text(json.dumps(obj,sort_keys=True,separators=(',',':'))+'\n');os.chmod(path,0o600)
def prepare(root):
 private=root/'.private/oracle';private.mkdir(mode=0o700)
 for n in range(1,41):write(private/f'input-{n:02d}.json',[((n+3)*(j+5)%17)-8 for j in range(577)])
 return {'ok':True,'known_fixture_vectors':40,'dimension':577}
def compare(root):
 rows=json.loads((HERE/'source/crypto/rows.json').read_bytes());queue=[];expected={}
 for n in range(1,41):
  x=json.loads((root/f'.private/oracle/input-{n:02d}.json').read_bytes());assert x==[((n+3)*(j+5)%17)-8 for j in range(577)]
  queue.append(x)
  if len(queue)>32:queue.pop(0)
  if n%10==0:expected[f'infer-{n:02d}']=sum(sum(v[j] for v in queue)*rows[n//10-1][j] for j in range(577))
 with sqlite3.connect(root/'.private/reader/answers.sqlite3') as db:
  got={r[0]:json.loads(r[1])['signed_score'] for r in db.execute('SELECT request_id,answer FROM private_decodes')}
  assert db.execute('SELECT count(*),sum(decode_count) FROM private_decodes').fetchone()==(4,4)
 checks=[{'request_id':k,'expected':v,'actual':got.get(k),'matches':got.get(k)==v} for k,v in expected.items()]
 write(root/'.private/oracle/comparisons.json',checks);assert expected==got
 return {'ok':True,'private_integer_comparisons':4,'all_match':True,'private_persisted_decode_count':4}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('mode',choices=['prepare','compare']);p.add_argument('--root',type=Path,required=True);a=p.parse_args()
 print(json.dumps(prepare(a.root) if a.mode=='prepare' else compare(a.root)))
