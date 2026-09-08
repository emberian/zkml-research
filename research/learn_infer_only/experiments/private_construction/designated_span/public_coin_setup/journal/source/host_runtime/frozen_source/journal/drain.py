#!/usr/bin/env python3
"""Recipient-private scalar recovery after public verified ciphertext acceptance.

No network/RPC endpoint invokes this entry point. This role has all 16 dedicated
recipient keys and therefore has the full fixed-span coalition's authority.
Private persistence/dedup is software behavior, not a limit on that coalition.
"""
import argparse
from model import *
from authority import connect


def drain(config):
 cfg=read_json(config);g=load_genesis(cfg)
 require(cfg['role']=='recipient_private_drain','privateDrainRole')
 crypto=Crypto(cfg,'recipient_private_drain')
 cas=CAS(cfg['cas'],g,crypto)
 private=Path(cfg['private_db']);private.touch(mode=0o600,exist_ok=True);os.chmod(private,0o600)
 decoded=0;already=0
 with connect(private) as db:
  db.execute('PRAGMA journal_mode=WAL')
  db.execute('CREATE TABLE IF NOT EXISTS identity (genesis TEXT PRIMARY KEY)')
  prior=db.execute('SELECT genesis FROM identity').fetchall()
  if prior:require(len(prior)==1 and prior[0]['genesis']==digest(g),'privateDrainGenesis')
  else:db.execute('INSERT INTO identity VALUES(?)',(digest(g),))
  db.execute('CREATE TABLE IF NOT EXISTS private_decodes (nonce TEXT PRIMARY KEY, request_id TEXT UNIQUE NOT NULL,envelope_sha256 TEXT NOT NULL,output_ct TEXT NOT NULL,row_id INTEGER NOT NULL,recipient_id TEXT NOT NULL,answer TEXT NOT NULL,decode_count INTEGER NOT NULL CHECK(decode_count=1))')
  with connect(cfg['db']) as accepted:
   accepted.execute('BEGIN')
   rows=accepted.execute('SELECT * FROM received ORDER BY rowid').fetchall()
   for row in rows:
    envelope=read_json_bytes(row['envelope']);payload=verify(envelope,g['authority_vk'],'resident-authority-finalization-v1')
    req=payload['request'];a=req['action'];check_request(req,g,cas)
    require(a['kind']=='Infer' and digest(envelope)==row['envelope_sha256'] and payload['output_ct']==row['output_ct'],'privateAcceptedIdentity')
    require(a['nonce']==row['nonce'] and a['request_id']==row['request_id'],'privateAcceptedRequest')
    verified=accepted.execute('SELECT kind,envelope FROM verified_journal WHERE envelope_sha256=?',(row['envelope_sha256'],)).fetchone()
    require(verified is not None and verified['kind']=='Infer' and verified['envelope']==row['envelope'],'privateVerifiedMembership')
    ticket=accepted.execute('SELECT authorization FROM expected WHERE nonce=?',(a['nonce'],)).fetchone()
    require(ticket is not None and ticket['authorization']==canonical(req['authorization']).decode(),'privateSelectedTicket')
    db.execute('BEGIN IMMEDIATE')
    old=db.execute('SELECT * FROM private_decodes WHERE nonce=?',(a['nonce'],)).fetchone()
    if old:
     require(old['envelope_sha256']==row['envelope_sha256'] and old['output_ct']==row['output_ct'],'privateDedupIdentity');already+=1
    else:
     key=Path(cfg['recipient_key_dir'])/f"r{a['row_id']:02d}.key"
     started=time.perf_counter_ns()
     answer=crypto.run('reader-decrypt',private_output=True,sk=key,ct=cas.get(row['output_ct']))
     elapsed=time.perf_counter_ns()-started
     require(answer['key_id']==g['key_id'] and answer['ciphertext_sha256']==row['output_ct'] and answer['row_id']==a['row_id'] and answer['recipient_id']==a['recipient'],'privateOutputBinding')
     db.execute('INSERT INTO private_decodes VALUES(?,?,?,?,?,?,?,1)',(a['nonce'],a['request_id'],row['envelope_sha256'],row['output_ct'],a['row_id'],a['recipient'],canonical(answer).decode()))
     cost={'request_id':a['request_id'],'row_id':a['row_id'],'decode_elapsed_ns':elapsed,'metrics':answer.get('metrics')}
     path=Path(cfg['private_cost_log'])
     with path.open('ab') as sink:sink.write(canonical(cost)+b'\n');sink.flush();os.fsync(sink.fileno())
     os.chmod(path,0o600);decoded+=1
    db.execute('COMMIT')
   accepted.execute('COMMIT')
  count=db.execute('SELECT count(*) FROM private_decodes').fetchone()[0]
 return {'ok':True,'new_private_decodes':decoded,'already_private_decoded':already,'private_decodes_total':count}


def read_json_bytes(raw):return parse_json(raw)

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--config',required=True);a=p.parse_args()
 # Stdout is deliberately aggregate-only; coordinator saves it privately.
 print(json.dumps(drain(a.config)))
