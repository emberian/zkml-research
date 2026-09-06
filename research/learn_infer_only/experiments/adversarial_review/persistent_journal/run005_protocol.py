#!/usr/bin/env python3
"""Local role-separated continuity fixture. No cryptographic verifier or isolation claim."""
from __future__ import annotations
import argparse,hashlib,json,os,signal,socket,socketserver,sqlite3,sys,time
from pathlib import Path

def canonical(value):return json.dumps(value,sort_keys=True,separators=(',',':'))
def digest(value):return hashlib.sha256(canonical(value).encode()).hexdigest()
def write_json(path,value):
 path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
 temporary=path.with_suffix(path.suffix+'.tmp');temporary.write_text(json.dumps(value,indent=2)+'\n');temporary.replace(path)
def connect(path):
 db=sqlite3.connect(path,timeout=10,isolation_level=None)
 db.row_factory=sqlite3.Row
 db.execute('PRAGMA journal_mode=WAL');db.execute('PRAGMA synchronous=FULL');db.execute('PRAGMA busy_timeout=10000')
 return db

def initialize_authority(path,fixture):
 Path(path).parent.mkdir(parents=True,exist_ok=True)
 with connect(path) as db:
  db.executescript('''CREATE TABLE meta(id INTEGER PRIMARY KEY CHECK(id=1),head INTEGER NOT NULL,state_root INTEGER NOT NULL,state_bytes TEXT NOT NULL,budget TEXT NOT NULL,fixture_sha TEXT NOT NULL);
CREATE TABLE journal(seq INTEGER PRIMARY KEY AUTOINCREMENT,txid INTEGER NOT NULL UNIQUE,nonce TEXT NOT NULL UNIQUE,request TEXT NOT NULL,packet TEXT NOT NULL,installed_state TEXT NOT NULL,published INTEGER NOT NULL DEFAULT 0 CHECK(published IN (0,1)));
CREATE TABLE authority_events(id INTEGER PRIMARY KEY AUTOINCREMENT,kind TEXT NOT NULL,detail TEXT NOT NULL);''')
  initial=fixture['initial'];db.execute('INSERT INTO meta VALUES(1,0,?,?,?,?)',(initial['state_root'],canonical(initial['state_bytes']),canonical(initial['budget']),digest(fixture)))

def initialize_recipient(path):
 Path(path).parent.mkdir(parents=True,exist_ok=True)
 with connect(path) as db:db.executescript('''CREATE TABLE deliveries(nonce TEXT PRIMARY KEY,txid INTEGER NOT NULL,packet TEXT NOT NULL);
CREATE TABLE attempts(id INTEGER PRIMARY KEY AUTOINCREMENT,nonce TEXT NOT NULL,txid INTEGER NOT NULL,packet TEXT NOT NULL,outcome TEXT NOT NULL);''')

def rpc(address,payload,timeout=15):
 with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as s:
  s.settimeout(timeout);s.connect(str(address));s.sendall((canonical(payload)+'\n').encode())
  with s.makefile('rb') as stream:
   line=stream.readline(1_000_001)
  if not line:raise EOFError('peer died before response')
  return json.loads(line)

def crash_at(message,stage):
 if message.get('failpoint')!=stage:return
 path=Path(message['crash_marker']);path.parent.mkdir(parents=True,exist_ok=True)
 with path.open('w') as f:
  json.dump({'stage':stage,'pid':os.getpid(),'signal':'SIGKILL','time_ns':time.time_ns()},f);f.flush();os.fsync(f.fileno())
 os.kill(os.getpid(),signal.SIGKILL)

def receipt_from_row(row,kind,publication):
 # The packet is obtained solely from the persisted journal row, never relabelled
 # by the caller's request object. There is no regenerated randomness/output.
 return dict(status=kind,transaction_id=row['txid'],sequence=row['seq'],nonce=json.loads(row['nonce']),
             packet=json.loads(row['packet']),installed_state=json.loads(row['installed_state']),publication=publication)

def preflight(fixture,request,meta,db):
 # The allowlist is an EXPLICIT computational-validity premise for two public
 # already-materialized fixture candidates. It is not a receipt verifier.
 txid=request.get('intent',{}).get('transaction_id')
 allow={x['intent']['transaction_id']:x for x in [fixture['primary'],fixture['racing']]}
 if txid not in allow or canonical(request)!=canonical(allow[txid]):return 'fixtureGateRefused'
 c=request['context'];o=request['openings'];i=request['intent'];s=fixture['selected']
 if o['genesis_id']!=s['genesis_id'] or o['state_id']!=s['state_id'] or o['genesis_bytes']!=s['genesis_bytes']:return 'wrongSelection'
 if c['genesis']!=s['genesis_id'] or c['authorization']!=s['authorization'] or c['recipient']!=s['recipient']:return 'wrongContextPolicy'
 if len(o['prior'])!=meta['head']:return 'stalePrefix'
 if o['pre_bytes']!=json.loads(meta['state_bytes']) or c['parent']!=meta['state_root']:return 'stalePreState'
 nonce=canonical(i['nullifiers'][0])
 if db.execute('SELECT 1 FROM journal WHERE nonce=?',(nonce,)).fetchone():return 'alreadyConsumed'
 # This is the exported singleton Bool cell, not a generic materializer.
 if len(i['writes'])!=1 or len(i['read_guards'])!=1 or len(i['nullifiers'])!=1:return 'fixtureShape'
 w=i['writes'][0];g=i['read_guards'][0]
 if w['cell_id']!=s['state_id'] or w['expected_pre']!=meta['state_root']:return 'stalePreRoot'
 if w['canonical_post_bytes']!=[w['exact_post']] or c['next']!=w['exact_post']:return 'wrongPostOpening'
 if g!={'cell_id':s['genesis_id'],'expected_root':s['genesis_bytes'][0]}:return 'readGuardConflict'
 if i['event']['event_id']!=txid:return 'eventIdConflict'
 available=json.loads(meta['budget'])
 if any(charge>available.get(lane,-1) or charge<0 for lane,charge in i['exact_charge'].items()):return 'insufficientBudget'
 return None

class FixtureServer(socketserver.ThreadingUnixStreamServer):
 daemon_threads=True;allow_reuse_address=True

class RecipientHandler(socketserver.StreamRequestHandler):
 def handle(self):
  msg=json.loads(self.rfile.readline(1_000_001));nonce=canonical(msg['nonce']);packet=canonical(msg['packet']);txid=msg['transaction_id']
  db=connect(self.server.database)
  try:
   db.execute('BEGIN IMMEDIATE')
   previous=db.execute('SELECT * FROM deliveries WHERE nonce=?',(nonce,)).fetchone()
   if previous is None:
    db.execute('INSERT INTO deliveries VALUES(?,?,?)',(nonce,txid,packet));outcome='stored'
   elif previous['txid']==txid and previous['packet']==packet:outcome='duplicateSamePacket'
   else:outcome='conflictingPacket'
   db.execute('INSERT INTO attempts(nonce,txid,packet,outcome) VALUES(?,?,?,?)',(nonce,txid,packet,outcome));db.execute('COMMIT')
   self.wfile.write((canonical({'status':outcome})+'\n').encode())
  finally:db.close()

class AuthorityHandler(socketserver.StreamRequestHandler):
 def handle(self):
  try:
   message=json.loads(self.rfile.readline(1_000_001));answer=self.submit(message)
  except Exception as e:answer={'status':'fixtureError','error_type':type(e).__name__,'error':str(e)}
  self.wfile.write((canonical(answer)+'\n').encode())
 def submit(self,message):
  if set(message)!={'request'}:return {'status':'rejected','reason':'unsupportedRequestFields'}
  controls=self.server.test_control
  request=message['request'];txid=request['intent']['transaction_id'];body=canonical(request)
  crash_at(controls,'before_reservation')
  db=connect(self.server.database)
  try:
   db.execute('BEGIN IMMEDIATE')
   row=db.execute('SELECT * FROM journal WHERE txid=?',(txid,)).fetchone()
   if row is not None:
    if row['request']!=body:
     db.execute('ROLLBACK');return {'status':'rejected','reason':'transactionConflict'}
    kind='replayed';db.execute('COMMIT')
   else:
    meta=db.execute('SELECT * FROM meta WHERE id=1').fetchone()
    if meta['fixture_sha']!=digest(self.server.fixture):raise RuntimeError('authority fixture identity changed')
    refusal=preflight(self.server.fixture,request,meta,db)
    if refusal:
     db.execute('ROLLBACK');return {'status':'rejected','reason':refusal}
    # The reserved nullifier, state install, exact charge and replay journal
    # enter one SQLite transaction; no detached preflight cache is trusted.
    i=request['intent'];w=i['writes'][0];budget=json.loads(meta['budget'])
    for lane,charge in i['exact_charge'].items():budget[lane]-=charge
    db.execute('UPDATE meta SET head=head+1,state_root=?,state_bytes=?,budget=? WHERE id=1',
      (w['exact_post'],canonical(w['canonical_post_bytes']),canonical(budget)))
    crash_at(controls,'after_install_before_commit')
    # Deliberately broken sibling, enabled only by this negative-control tag:
    # publishing an uncommitted candidate creates an orphan external packet.
    if controls.get('failpoint')=='broken_publish_before_commit':
     rpc(self.server.recipient,{'nonce':i['nullifiers'][0],
       'transaction_id':txid,'packet':i['event']})
     crash_at(controls,'broken_publish_before_commit')
    db.execute('INSERT INTO journal(txid,nonce,request,packet,installed_state) VALUES(?,?,?,?,?)',
      (txid,canonical(i['nullifiers'][0]),body,canonical(i['event']),canonical(w['canonical_post_bytes'])))
    row=db.execute('SELECT * FROM journal WHERE txid=?',(txid,)).fetchone()
    db.execute('COMMIT');kind='accepted'
    crash_at(controls,'after_commit_before_publication')
   # Release comes after durable install and from this stored row, including
   # on retry. Publication is a separate atomic domain: its recipient dedup
   # resource is explicit and transport attempts may repeat.
   if row['published']:
    publication='alreadyPublished'
   else:
    published=rpc(self.server.recipient,{'nonce':json.loads(row['nonce']),
      'transaction_id':row['txid'],'packet':json.loads(row['packet'])})
    publication=published['status']
    if publication=='conflictingPacket':return receipt_from_row(row,kind,'conflictingPacket')
    crash_at(controls,'after_publication_before_client_ack')
    db.execute('BEGIN IMMEDIATE');db.execute('UPDATE journal SET published=1 WHERE txid=?',(txid,));db.execute('COMMIT')
   return receipt_from_row(row,kind,publication)
  finally:db.close()

def server(args):
 address=Path(args.socket);address.parent.mkdir(parents=True,exist_ok=True)
 if address.exists():address.unlink()
 handler=AuthorityHandler if args.role=='authority' else RecipientHandler
 with FixtureServer(str(address),handler) as service:
  service.database=args.database
  service.test_control={'failpoint':args.test_failpoint,'crash_marker':args.test_crash_marker}
  if args.role=='authority':service.fixture=json.loads(Path(args.fixture).read_text());service.recipient=args.recipient
  print(canonical({'ready':args.role,'pid':os.getpid(),'socket':str(address)}),flush=True)
  service.serve_forever(poll_interval=0.05)

def client(args):
 request=json.loads(Path(args.request).read_text())
 if args.barrier:
  limit=time.monotonic()+10
  while not Path(args.barrier).exists():
   if time.monotonic()>limit:raise TimeoutError('client barrier did not open')
   time.sleep(0.005)
 payload={'request':request}
 try:answer=rpc(args.socket,payload);code=0
 except (EOFError,ConnectionResetError,BrokenPipeError) as e:answer={'status':'connectionLost','error_type':type(e).__name__};code=0
 if args.host_state and answer.get('status') in ['accepted','replayed']:
  write_json(args.host_state,{'state_bytes':answer['installed_state'],'sequence':answer['sequence'],'packet':answer['packet']})
 write_json(args.output,{'pid':os.getpid(),'request_sha256':digest(request),'answer':answer})
 print(canonical(answer));return code

def main():
 p=argparse.ArgumentParser();subs=p.add_subparsers(dest='command',required=True)
 s=subs.add_parser('serve');s.add_argument('role',choices=['authority','recipient']);s.add_argument('--socket',required=True);s.add_argument('--database',required=True);s.add_argument('--recipient');s.add_argument('--fixture');s.add_argument('--test-failpoint');s.add_argument('--test-crash-marker')
 c=subs.add_parser('client');c.add_argument('--socket',required=True);c.add_argument('--request',required=True);c.add_argument('--output',required=True);c.add_argument('--barrier');c.add_argument('--host-state')
 args=p.parse_args()
 if args.command=='serve':server(args)
 else:raise SystemExit(client(args))
if __name__=='__main__':main()
