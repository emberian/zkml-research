#!/usr/bin/env python3
"""Actual-process crash/concurrency experiment. All assertions concern this fixture."""
from __future__ import annotations
from contextlib import closing
import copy,hashlib,json,os,platform,shutil,signal,sqlite3,subprocess,sys,tempfile,time,traceback
from pathlib import Path
import protocol
E=Path(__file__).resolve().parent
FIXTURE=json.loads((E/'fixture.json').read_text())
SHA=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
RESULTS=E/'results';RESULTS.mkdir(exist_ok=True)
RUN=RESULTS/f"run_{len(list(RESULTS.glob('run_*')))+1:03}"
RUN.mkdir();SOCKETS=Path(tempfile.mkdtemp(prefix='mmaj-',dir='/tmp'))
COMMANDS=[];CASES=[];PROCESSES=[]

def save(path,value):protocol.write_json(path,value)
def read(path):return json.loads(Path(path).read_text())
def connect_read(path):
 db=sqlite3.connect(f'file:{path}?mode=ro',uri=True);db.row_factory=sqlite3.Row;return db

def inspect_database(path,role):
 with connect_read(path) as db:
  result={'integrity':db.execute('PRAGMA integrity_check').fetchone()[0],
          'journal_mode':db.execute('PRAGMA journal_mode').fetchone()[0],
          'synchronous':db.execute('PRAGMA synchronous').fetchone()[0]}
  if role=='authority':
   result['meta']=dict(db.execute('SELECT * FROM meta').fetchone())
   result['meta']['state_bytes']=json.loads(result['meta']['state_bytes']);result['meta']['budget']=json.loads(result['meta']['budget'])
   result['journal']=[dict(x) for x in db.execute('SELECT * FROM journal ORDER BY seq')]
   for row in result['journal']:
    for key in ['request','packet','installed_state','nonce']:row[key]=json.loads(row[key])
  else:
   result['deliveries']=[dict(x) for x in db.execute('SELECT * FROM deliveries ORDER BY nonce')]
   result['attempts']=[dict(x) for x in db.execute('SELECT * FROM attempts ORDER BY id')]
   for row in result['deliveries']+result['attempts']:
    for key in ['packet','nonce']:row[key]=json.loads(row[key])
  return result

def assert_local_invariant(snapshot,count):
 a=snapshot['authority'];r=snapshot['recipient'];m=a['meta'];j=a['journal']
 assert a['integrity']==r['integrity']=='ok'
 assert a['journal_mode']==r['journal_mode']=='wal'
 assert m['head']==len(j)==count
 assert len({protocol.canonical(x['nonce']) for x in j})==count
 assert len({x['txid'] for x in j})==count
 assert set(m['budget'].values())=={10-count}
 assert m['state_bytes']==([0] if count==0 else j[-1]['installed_state'])
 for row in j:
  assert row['packet']==row['request']['intent']['event']
  assert row['nonce']==row['request']['intent']['nullifiers'][0]
  assert row['installed_state']==row['request']['intent']['writes'][0]['canonical_post_bytes']
 assert len({protocol.canonical(x['nonce']) for x in r['deliveries']})==len(r['deliveries'])
 for row in r['attempts']:
  if row['outcome']!='conflictingPacket':
   delivery=next(x for x in r['deliveries'] if x['nonce']==row['nonce'])
   assert row['packet']==delivery['packet'] and row['txid']==delivery['txid']

class Case:
 def __init__(self,name,test_failpoint=None):
  self.name=name;self.path=RUN/name;self.path.mkdir();self.id=len(CASES);self.commands=[];self.count=0;self.starts=0
  self.a_db=self.path/'authority/journal.sqlite3';self.r_db=self.path/'recipient/inbox.sqlite3'
  protocol.initialize_authority(self.a_db,FIXTURE);protocol.initialize_recipient(self.r_db)
  self.a_socket=SOCKETS/f'a{self.id}.sock';self.r_socket=SOCKETS/f'r{self.id}.sock'
  self.host=self.path/'untrusted_host/state.json';save(self.host,{'state_bytes':[0],'sequence':0})
  self.host_snapshot=self.path/'untrusted_host/genesis_snapshot.json';shutil.copy2(self.host,self.host_snapshot)
  self.requests={}
  for key in ['primary','racing']:
   self.requests[key]=self.path/f'untrusted_host/{key}.json';save(self.requests[key],FIXTURE[key])
  self.r=self.start('recipient');self.a=self.start('authority',test_failpoint=test_failpoint);CASES.append(self)
 def spawn(self,cmd,tag):
  out=self.path/f'{tag}.stdout';err=self.path/f'{tag}.stderr';fo=out.open('w');fe=err.open('w')
  p=subprocess.Popen([str(x) for x in cmd],cwd=E,stdout=fo,stderr=fe);fo.close();fe.close();PROCESSES.append(p)
  rec={'command':[str(x) for x in cmd],'cwd':str(E),'pid':p.pid,'stdout':str(out.relative_to(RUN)),'stderr':str(err.relative_to(RUN)),'started_ns':time.time_ns()}
  COMMANDS.append(rec);self.commands.append(rec);p.record=rec;return p
 def start(self,role,socket_override=None,test_failpoint=None):
  self.starts+=1;tag=f'{role}_start{self.starts}'
  cmd=[sys.executable,E/'protocol.py','serve',role,'--socket',socket_override or (self.a_socket if role=='authority' else self.r_socket),
       '--database',self.a_db if role=='authority' else self.r_db]
  if role=='authority':cmd+=['--recipient',self.r_socket,'--fixture',E/'fixture.json']
  if test_failpoint:cmd+=['--test-failpoint',test_failpoint,'--test-crash-marker',self.path/f'{test_failpoint}.marker.json']
  p=self.spawn(cmd,tag);limit=time.monotonic()+10
  while time.monotonic()<limit:
   if p.poll() is not None:raise RuntimeError(f'{role} failed startup: {p.returncode}')
   if (self.path/f'{tag}.stdout').read_text().strip():return p
   time.sleep(.005)
  raise TimeoutError(f'{role} readiness')
 def finish(self,p,timeout=20):
  code=p.wait(timeout=timeout);p.record['exit_code']=code;p.record['finished_ns']=time.time_ns();return code
 def stop(self,p):
  if p.poll() is None:p.terminate()
  self.finish(p)
 def restart_authority(self):
  self.stop(self.a);self.a=self.start('authority')
 def launch_client(self,key='primary',request=None,barrier=None,host=True,socket_override=None):
  self.count+=1;tag=f'client{self.count}';out=self.path/f'{tag}.json'
  req=self.requests[key]
  if request is not None:req=self.path/f'untrusted_host/{tag}_request.json';save(req,request)
  cmd=[sys.executable,E/'protocol.py','client','--socket',socket_override or self.a_socket,'--request',req,'--output',out]
  if barrier:cmd+=['--barrier',barrier]
  if host:cmd+=['--host-state',self.host]
  return self.spawn(cmd,tag),out
 def client(self,**kwargs):
  p,out=self.launch_client(**kwargs);assert self.finish(p)==0;return read(out)['answer']
 def snapshot(self,label):
  result={'authority':inspect_database(self.a_db,'authority'),'recipient':inspect_database(self.r_db,'recipient'),'host':read(self.host)}
  save(self.path/f'{label}.json',result);return result
 def close(self):self.stop(self.a);self.stop(self.r)


def crash_case(stage,committed,published):
 c=Case(stage,test_failpoint=stage);answer=c.client()
 assert answer['status']=='connectionLost';assert c.finish(c.a)==-signal.SIGKILL
 mark=read(c.path/f'{stage}.marker.json');assert mark['stage']==stage and mark['pid']==c.a.pid
 before=c.snapshot('after_actual_process_kill');assert_local_invariant(before,int(committed))
 assert len(before['recipient']['deliveries'])==int(published)
 assert before['host']=={'state_bytes':[0],'sequence':0}
 if committed:assert before['authority']['journal'][0]['published']==0
 c.a=c.start('authority');retry=c.client();after=c.snapshot('after_exact_retry');assert_local_invariant(after,1)
 assert retry['status']==('replayed' if committed else 'accepted')
 assert retry['packet']==FIXTURE['primary']['intent']['event'];assert len(after['recipient']['deliveries'])==1
 expected_attempts=2 if published else 1;assert len(after['recipient']['attempts'])==expected_attempts
 c.close();return dict(case=stage,crash_exit=-signal.SIGKILL,committed_before_restart=committed,
  recipient_had_packet_before_restart=published,retry=retry['status'],logical_journal_packets=1,recipient_deliveries=1,publication_attempts=expected_attempts)



def publication_before_commit_control():
 c=Case('broken_publish_before_commit',test_failpoint='broken_publish_before_commit');answer=c.client()
 assert answer['status']=='connectionLost' and c.finish(c.a)==-signal.SIGKILL
 broken=c.snapshot('orphan_packet_after_uncommitted_publish');assert_local_invariant(broken,0)
 assert len(broken['recipient']['deliveries'])==1
 assert broken['recipient']['deliveries'][0]['packet']==FIXTURE['primary']['intent']['event']
 c.a=c.start('authority');retry=c.client();assert retry['status']=='accepted'
 recovered=c.snapshot('recovery_after_orphan_packet');assert_local_invariant(recovered,1)
 assert len(recovered['recipient']['deliveries'])==1 and len(recovered['recipient']['attempts'])==2
 c.close();return {'case':c.name,'premise_violated':'publish only after committed journal/install',
  'journal_packets_at_first_publication':0,'recipient_packets_at_first_publication':1,
  'counterexample':'recipient observed a packet whose state transition was rolled back',
  'later_recovery_does_not_erase_the_earlier_ordering_violation':True}


def retry_and_mutation_case():
 c=Case('retry_and_exact_packet')
 attempted_marker=c.path/'untrusted_host/forged_crash_marker.json'
 # A normal client cannot select any fault mode; malformed outer envelopes
 # are rejected before the transaction and cannot enable early publication.
 hook_attempt=protocol.rpc(c.a_socket,{'request':FIXTURE['primary'],
  'failpoint':'broken_publish_before_commit','crash_marker':str(attempted_marker)})
 assert hook_attempt=={'status':'rejected','reason':'unsupportedRequestFields'}
 hook_state=c.snapshot('client_fault_mode_refused');assert_local_invariant(hook_state,0)
 assert not hook_state['recipient']['deliveries'] and not attempted_marker.exists() and c.a.poll() is None
 save(c.path/'fault_channel_refusal.json',hook_attempt)
 first=c.client();assert first['status']=='accepted'
 barrier=c.path/'retry.barrier';pending=[c.launch_client(barrier=barrier,host=False) for _ in range(8)]
 barrier.touch();replies=[]
 for p,out in pending:assert c.finish(p)==0;replies.append(read(out)['answer'])
 assert all(x['status']=='replayed' and x['packet']==first['packet'] for x in replies)
 mutations=[]
 for field in FIXTURE['primary']['context']:
  request=copy.deepcopy(FIXTURE['primary']);request['context'][field]+=1;mutations.append(('context.'+field,request))
 for label,path in [('post_bytes',('writes',0,'canonical_post_bytes')),('exact_charge',('exact_charge','feeDebit')),('read_guard',('read_guards',0,'expected_root')),('nullifier_bytes',('nullifiers',0,'canonical_bytes')),('packet_bytes',('event','canonical_bytes'))]:
  request=copy.deepcopy(FIXTURE['primary']);target=request['intent']
  for part in path[:-1]:target=target[part]
  value=target[path[-1]];target[path[-1]]=value+[17] if isinstance(value,list) else value+1;mutations.append((label,request))
 refusals=[]
 for label,request in mutations:
  reply=c.client(request=request);assert reply=={'status':'rejected','reason':'transactionConflict'};refusals.append(label)
 after=c.snapshot('after_retries_and_mutations');assert_local_invariant(after,1)
 assert len(after['recipient']['deliveries'])==len(after['recipient']['attempts'])==1
 c.close();return dict(case=c.name,untrusted_fault_fields_refused=True,concurrent_exact_retries=8,changed_identity_refusals=refusals,logical_journal_packets=1,recipient_deliveries=1,publication_attempts=1)


def race_cases(rounds=12):
 outputs=[]
 for index in range(rounds):
  c=Case(f'same_parent_race_{index:02}');barrier=c.path/'race.barrier'
  second_socket=SOCKETS/f'a{c.id}second.sock';second_authority=c.start('authority',socket_override=second_socket)
  pending=[c.launch_client(key='primary',barrier=barrier,host=False),
           c.launch_client(key='racing',barrier=barrier,host=False,socket_override=second_socket)]
  barrier.touch();replies=[]
  for p,out in pending:assert c.finish(p)==0;replies.append(read(out)['answer'])
  assert sorted(x['status'] for x in replies)==['accepted','rejected']
  winner=next(x for x in replies if x['status']=='accepted');loser=next(x for x in replies if x['status']=='rejected')
  assert loser['reason'] in ['stalePrefix','stalePreState','alreadyConsumed']
  snapshot=c.snapshot('after_two_process_race');assert_local_invariant(snapshot,1)
  assert len(snapshot['recipient']['deliveries'])==1
  assert snapshot['authority']['journal'][0]['txid']==winner['transaction_id']
  assert c.a.pid!=second_authority.pid and pending[0][0].pid!=pending[1][0].pid
  authority_pids=[c.a.pid,second_authority.pid];client_pids=[p.pid for p,_ in pending]
  c.stop(second_authority);c.close();outputs.append({'case':c.name,'winner':winner['transaction_id'],'loser_reason':loser['reason'],'journal_packets':1,'recipient_deliveries':1,'authority_worker_pids':authority_pids,'client_pids':client_pids})
 return outputs


def host_restore_case():
 c=Case('host_restore_only');first=c.client();assert first['status']=='accepted'
 before=c.snapshot('before_host_restore');shutil.copy2(c.host_snapshot,c.host)
 restored=c.snapshot('after_host_restore');assert restored['host']['sequence']==0 and restored['authority']['meta']['head']==1
 stale=c.client(key='racing');assert stale['status']=='rejected'
 replay=c.client();assert replay['status']=='replayed' and replay['packet']==first['packet']
 after=c.snapshot('after_restore_retry');assert_local_invariant(after,1)
 assert after['authority']==before['authority'];assert after['recipient']==before['recipient']
 assert after['host']['sequence']==1 and after['host']['state_bytes']==[1]
 c.close();return {'case':c.name,'restored_host_revision':0,'authority_revision_kept':1,'stale_fork':stale,'exact_retry':replay['status'],'authority_and_recipient_unchanged':True}


def authority_rollback_case():
 c=Case('authority_rollback_negative_control');backup=c.path/'authority/genesis_backup.sqlite3'
 with closing(sqlite3.connect(c.a_db)) as source,closing(sqlite3.connect(backup)) as destination:source.backup(destination)
 first=c.client();assert first['status']=='accepted';branch1=c.snapshot('first_committed_history')
 c.stop(c.a)
 # SQLite's backup API restores the saved authority image after all service
 # connections have stopped; it also avoids copying a live WAL generation.
 with closing(sqlite3.connect(backup)) as source,closing(sqlite3.connect(c.a_db)) as destination:source.backup(destination)
 c.a=c.start('authority')
 restored=c.snapshot('authority_restored_to_genesis');assert_local_invariant(restored,0)
 second=c.client(key='racing');assert second['status']=='accepted' and second['publication']=='conflictingPacket'
 branch2=c.snapshot('second_committed_history');assert_local_invariant(branch2,1)
 one=branch1['authority']['journal'][0];two=branch2['authority']['journal'][0]
 assert one['nonce']==two['nonce'] and one['txid']!=two['txid'] and one['packet']!=two['packet']
 assert len(branch2['recipient']['deliveries'])==1 and branch2['recipient']['deliveries'][0]['txid']==one['txid']
 assert branch2['recipient']['attempts'][-1]['outcome']=='conflictingPacket'
 c.close();return {'case':c.name,'premise_violated':'independent authority state cannot be rewound','same_nonce':one['nonce'],
  'first_committed_tx':one['txid'],'second_committed_tx':two['txid'],'distinct_committed_packets_across_rollback':2,
  'recipient_rollback':False,'persistent_recipient_refused_conflicting_publication':True,'second_commit_publication':second['publication']}


def main():
 paths=[E/'protocol.py',E/'run.py',E/'fixture.json',E/'ExportFixture.lean',E/'export.py']
 hashes={str(p):SHA(p) for p in paths};t=time.time();report={'status':'running','source_sha256':hashes,'cases':[]}
 try:
  for stage,committed,published in [('before_reservation',False,False),('after_install_before_commit',False,False),('after_commit_before_publication',True,False),('after_publication_before_client_ack',True,True)]:
   report['cases'].append(crash_case(stage,committed,published));print(stage,'passed',flush=True)
  report['cases'].append(publication_before_commit_control());print('early-publication negative control passed',flush=True)
  report['cases'].append(retry_and_mutation_case());print('retry_and_mutation passed',flush=True)
  report['races']=race_cases();print('12 actual process races passed',flush=True)
  report['cases'].append(host_restore_case());print('host_restore passed',flush=True)
  report['cases'].append(authority_rollback_case());print('authority_rollback negative control passed',flush=True)
  report['status']='passed'
 except Exception:
  report['status']='failed';report['exception']=traceback.format_exc();print(report['exception'],flush=True)
 finally:
  for p in PROCESSES:
   if p.poll() is None:p.terminate()
   try:p.wait(timeout=3)
   except subprocess.TimeoutExpired:p.kill();p.wait()
   p.record['exit_code']=p.returncode
  report.update(elapsed_seconds=time.time()-t,inputs_unchanged=all(SHA(p)==h for p,h in hashes.items()),commands=COMMANDS,
    environment={'python':sys.version,'sqlite':sqlite3.sqlite_version,'platform':platform.platform(),'journal_mode':'WAL','synchronous':'FULL'},
    authority_role='distinct persistent authority process/database; independence assumed, not enforced by same-user local filesystem',
    recipient_role='separately persistent nonce/packet deduplication; repeated transport attempts permitted',
    claim_scope='Executed local process-crash/concurrency fixture only; no cryptographic verifier, no power-loss/distributed durability or Lean refinement proof')
  save(RUN/'report.json',report);save(E/'report.json',{'latest_run':str(RUN.relative_to(E)),'status':report['status'],'report_sha256':SHA(RUN/'report.json')})
  shutil.rmtree(SOCKETS)
 print('RESULT',report['status'],RUN,flush=True);return 0 if report['status']=='passed' else 1
if __name__=='__main__':raise SystemExit(main())
