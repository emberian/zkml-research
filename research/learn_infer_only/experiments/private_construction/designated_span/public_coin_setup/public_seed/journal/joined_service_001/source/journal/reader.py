"""Public recipient acceptance. Independently verified ciphertexts are durable
before ACK; no recipient scalar or decoding runs in this service. Use drain.py
privately after public handling. The service is not an OS isolation boundary.
"""
import argparse
from authority import connect,serve
from model import *

class Reader:
 def __init__(self,config):
  self.cfg=config;self.g=load_genesis(config)
  self.cas=CAS(config['cas'],self.g,Crypto(config,'reader',config['command_log']))
  Path(config['db']).touch(mode=0o600,exist_ok=True);os.chmod(config['db'],0o600)
  with connect(config['db']) as db:
   db.execute('PRAGMA journal_mode=WAL')
   db.execute('CREATE TABLE IF NOT EXISTS identity (genesis TEXT PRIMARY KEY)')
   rows=db.execute('SELECT genesis FROM identity').fetchall()
   if rows:require(len(rows)==1 and rows[0]['genesis']==digest(self.g),'readerGenesis')
   else:db.execute('INSERT INTO identity VALUES(?)',(digest(self.g),))
   db.execute('CREATE TABLE IF NOT EXISTS expected (nonce TEXT PRIMARY KEY,authorization TEXT NOT NULL)')
   db.execute('CREATE TABLE IF NOT EXISTS received (nonce TEXT PRIMARY KEY,request_id TEXT UNIQUE NOT NULL,envelope_sha256 TEXT NOT NULL,output_ct TEXT NOT NULL,envelope TEXT NOT NULL)')
 def register(self,auth,raw):
  a=auth['payload'];require(a.get('kind')=='Infer','readerOnlyInfer')
  self.cas.put(raw,'query',a['query_ct']);validate_action(a,auth,self.g,self.cas)
  encoded=canonical(auth).decode()
  with connect(self.cfg['db']) as db:
   db.execute('BEGIN IMMEDIATE');row=db.execute('SELECT authorization FROM expected WHERE nonce=?',(a['nonce'],)).fetchone()
   if row:require(row['authorization']==encoded,'expectedNonceConflict')
   else:db.execute('INSERT INTO expected VALUES(?,?)',(a['nonce'],encoded))
   db.execute('COMMIT')
  return {'ok':True,'status':'registered','nonce':a['nonce']}
 def receive(self,envelope,raw):
  p=verify(envelope,self.g['authority_vk'],'resident-authority-finalization-v1')
  exact_keys(p,['schema','request','request_sha256','revision','parent_state','next_state','delta','output_ct'],'finalizationFields')
  require(p['schema']=='resident-finalized-v1','finalizationSchema');req=p['request'];a=req['action']
  require(a.get('kind')=='Infer','readerOnlyInfer')
  check_request(req,self.g,self.cas)
  require(p['request_sha256']==digest(req),'finalizedRequestDigest')
  require(integer(p['revision']) and p['revision']==a['parent_revision']+1,'finalizedRevision')
  require(p['parent_state']==a['parent_state'] and p['next_state']==a['parent_state']==req['proposal']['next_state'],'inferStateFrame')
  require(req['proposal']['expired_ct'] is None,'inferExpiry')
  require(p['output_ct']==req['proposal']['result_ct'],'finalizedOutput')
  require(canonical(p['delta'])==canonical({'kind':'Infer','route':a['route'],'query_ct':a['query_ct'],'output_ct':p['output_ct']}),'finalizedDelta')
  self.cas.put(raw,'ct',p['output_ct']);meta=self.cas.inspected[p['output_ct']]
  require(meta['object_type']=='recipient_output' and meta['row_id']==a['row_id'] and meta['recipient_id']==a['recipient'] and meta['row_sha256']==a['row_sha256'] and meta['token_sha256']==a['token_sha256'],'acceptedDesignatedOutputBinding')
  envelope_hash=digest(envelope)
  db=connect(self.cfg['db'])
  try:
   db.execute('BEGIN IMMEDIATE');expected=db.execute('SELECT authorization FROM expected WHERE nonce=?',(a['nonce'],)).fetchone()
   require(expected is not None and expected['authorization']==canonical(req['authorization']).decode(),'unselectedQueryTicket')
   prior=db.execute('SELECT * FROM received WHERE nonce=?',(a['nonce'],)).fetchone()
   if prior:
    require(prior['envelope_sha256']==envelope_hash and prior['output_ct']==p['output_ct'],'readerNonceConflict');status='replayed'
   else:
    require(db.execute('SELECT 1 FROM received WHERE request_id=?',(a['request_id'],)).fetchone() is None,'readerRequestConflict')
    db.execute('INSERT INTO received VALUES(?,?,?,?,?)',(a['nonce'],a['request_id'],envelope_hash,p['output_ct'],canonical(envelope).decode()));status='ciphertextAccepted'
   db.execute('COMMIT')
  finally:
   if db.in_transaction:db.execute('ROLLBACK')
   db.close()
  return {'ok':True,'status':status,'nonce':a['nonce'],'envelope_sha256':envelope_hash}
 def handle(self,msg):
  require(isinstance(msg,dict),'messageObject')
  if msg.get('op')=='register':
   exact_keys(msg,['op','authorization','query']);return self.register(msg['authorization'],base64.b64decode(msg['query'],validate=True))
  if msg.get('op')=='receive':
   exact_keys(msg,['op','envelope','ciphertext']);return self.receive(msg['envelope'],base64.b64decode(msg['ciphertext'],validate=True))
  if msg.get('op')=='status':
   exact_keys(msg,['op'])
   with connect(self.cfg['db']) as db:
    return {'ok':True,'selected':db.execute('SELECT count(*) FROM expected').fetchone()[0],'received':db.execute('SELECT count(*) FROM received').fetchone()[0]}
  raise Refusal('operation')
def main():
 p=argparse.ArgumentParser();p.add_argument('--config',required=True);a=p.parse_args();cfg=read_json(a.config);serve(Reader(cfg),cfg['socket'])
if __name__=='__main__':main()
