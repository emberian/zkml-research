"""Keyless SQLite authority: recompute, commit exact delta/outbox, then publish."""
import argparse,signal,sqlite3,socketserver,threading
from model import *

def connect(path):
 db=sqlite3.connect(path,timeout=90,isolation_level=None);db.row_factory=sqlite3.Row
 db.execute('PRAGMA busy_timeout=90000');db.execute('PRAGMA synchronous=FULL');return db

def crash(point,selected,marker):
 if point==selected:
  if marker:atomic_write(marker,point.encode())
  os.kill(os.getpid(),signal.SIGKILL)

class Authority:
 def __init__(self,config,fault=None,marker=None):
  self.cfg=config;self.g=load_genesis(config);self.fault=fault;self.marker=marker
  self.cas=CAS(config['cas'],self.g,Crypto(config,'authority',config['command_log']))
  with connect(config['db']) as db:
   db.execute('PRAGMA journal_mode=WAL')
   db.execute('CREATE TABLE IF NOT EXISTS meta (singleton INTEGER PRIMARY KEY CHECK(singleton=1),genesis TEXT NOT NULL,revision INTEGER NOT NULL,state TEXT NOT NULL,state_digest TEXT NOT NULL)')
   db.execute('CREATE TABLE IF NOT EXISTS journal (revision INTEGER PRIMARY KEY,request_id TEXT UNIQUE NOT NULL,nonce TEXT UNIQUE NOT NULL,record_id TEXT UNIQUE,request TEXT NOT NULL,envelope TEXT NOT NULL,published INTEGER NOT NULL DEFAULT 0)')
   row=db.execute('SELECT * FROM meta').fetchone()
   if row:require(row['genesis']==digest(self.g),'authorityGenesis')
   else:
    state=initial_state(self.g);db.execute('INSERT INTO meta VALUES(1,?,?,?,?)',(digest(self.g),0,canonical(state).decode(),digest(state)))
 def head(self):
  with connect(self.cfg['db']) as db:row=db.execute('SELECT * FROM meta').fetchone()
  state=json.loads(row['state']);require(validate_state(state,self.g,self.cas)==row['state_digest'],'installedStateDigest')
  return {'ok':True,'revision':row['revision'],'state_digest':row['state_digest'],'state':state}
 def publish(self,envelope):
  p=envelope['payload'];a=p['request']['action']
  if a['kind']=='Learn':return {'status':'not_a_release'}
  ct=self.cas.get(p['output_ct']).read_bytes()
  try:
   ack=rpc(self.cfg['reader_socket'],{'op':'receive','envelope':envelope,'ciphertext':base64.b64encode(ct).decode()})
   if ack.get('ok'):
    with connect(self.cfg['db']) as db:db.execute('UPDATE journal SET published=1 WHERE revision=?',(p['revision'],))
    return {'status':'acknowledged','reader':ack}
   return {'status':'pending','reader':ack}
  except (OSError,EOFError,Refusal) as e:return {'status':'pending','reason':type(e).__name__}
 def submit(self,req):
  # Lookup precedes currentness and blob checks so later heads do not invalidate exact retry.
  exact_keys(req,['schema','action','authorization','proposal'],'requestFields')
  require(isinstance(req['action'],dict) and isinstance(req['action'].get('request_id'),str),'requestIdentifier')
  encoded=canonical(req).decode();crash('before_reservation',self.fault,self.marker)
  db=connect(self.cfg['db'])
  try:
   db.execute('BEGIN IMMEDIATE');row=db.execute('SELECT request,envelope FROM journal WHERE request_id=?',(req['action']['request_id'],)).fetchone()
   if row:
    require(row['request']==encoded,'requestIdConflict');envelope=json.loads(row['envelope']);status='replayed';db.execute('COMMIT')
   else:
    check_request(req,self.g,self.cas);a=req['action'];meta=db.execute('SELECT * FROM meta').fetchone()
    require(a['parent_revision']==meta['revision'] and a['parent_state']==meta['state_digest'],'staleParent')
    require(db.execute('SELECT 1 FROM journal WHERE nonce=?',(a['nonce'],)).fetchone() is None,'alreadyConsumed')
    if a['kind']=='Learn':require(db.execute('SELECT 1 FROM journal WHERE record_id=?',(a['record_id'],)).fetchone() is None,'inputAlreadyAdmitted')
    state=json.loads(meta['state']);require(validate_state(state,self.g,self.cas)==meta['state_digest'],'installedStateDigest')
    new,delta,expected=transition(state,a,self.g,self.cas)
    require(req['proposal']==expected,'recomputedProposalMismatch')
    revision=meta['revision']+1
    payload={'schema':'resident-finalized-v1','request':req,'request_sha256':digest(req),'revision':revision,'parent_state':meta['state_digest'],'next_state':digest(new),'delta':delta,'output_ct':expected['result_ct'] if a['kind']=='Infer' else None}
    envelope=sign(payload,self.cfg['signing_key'],'resident-authority-finalization-v1')
    db.execute('INSERT INTO journal(revision,request_id,nonce,record_id,request,envelope) VALUES(?,?,?,?,?,?)',(revision,a['request_id'],a['nonce'],a.get('record_id'),encoded,canonical(envelope).decode()))
    db.execute('UPDATE meta SET revision=?,state=?,state_digest=? WHERE singleton=1',(revision,canonical(new).decode(),digest(new)))
    db.execute('COMMIT');status='accepted'
  finally:
   if db.in_transaction:db.execute('ROLLBACK')
   db.close()
  crash('after_commit',self.fault,self.marker)
  delivery=self.publish(envelope)
  crash('after_publication',self.fault,self.marker)
  return {'ok':True,'status':status,'envelope':envelope,'delivery':delivery}
 def handle(self,msg):
  require(isinstance(msg,dict),'messageObject');op=msg.get('op')
  if op=='head':exact_keys(msg,['op']);return self.head()
  if op=='put':
   exact_keys(msg,['op','kind','sha256','data']);raw=base64.b64decode(msg['data'],validate=True)
   return {'ok':True,'sha256':self.cas.put(raw,msg['kind'],msg['sha256'])}
  if op=='get':
   exact_keys(msg,['op','kind','sha256']);raw=self.cas.get(msg['sha256'],msg['kind']).read_bytes()
   return {'ok':True,'sha256':msg['sha256'],'data':base64.b64encode(raw).decode()}
  if op=='submit':exact_keys(msg,['op','request']);return self.submit(msg['request'])
  if op=='export':
   exact_keys(msg,['op'])
   with connect(self.cfg['db']) as db:rows=db.execute('SELECT envelope,published FROM journal ORDER BY revision').fetchall()
   return {'ok':True,'head':self.head(),'journal':[{'envelope':json.loads(x['envelope']),'published':bool(x['published'])} for x in rows]}
  raise Refusal('operation')

class Server(socketserver.ThreadingUnixStreamServer):
 daemon_threads=True
class Handler(socketserver.StreamRequestHandler):
 def handle(self):
  try:
   line=self.rfile.readline(2_000_001);require(len(line)<=2_000_000,'requestSize');response=self.server.role.handle(json.loads(line))
  except Refusal as e:response={'ok':False,'reason':str(e)}
  except Exception as e:response={'ok':False,'reason':'malformed:'+type(e).__name__}
  self.wfile.write(canonical(response)+b'\n')
def serve(role,address):
 address=Path(address)
 if address.exists():address.unlink()
 with Server(str(address),Handler) as server:
  server.role=role;os.chmod(address,0o600);server.serve_forever(poll_interval=0.1)
def main():
 p=argparse.ArgumentParser();p.add_argument('--config',required=True);p.add_argument('--socket');p.add_argument('--fault',choices=['before_reservation','after_commit','after_publication']);p.add_argument('--marker');a=p.parse_args()
 cfg=read_json(a.config);serve(Authority(cfg,a.fault,a.marker),a.socket or cfg['socket'])
if __name__=='__main__':main()
