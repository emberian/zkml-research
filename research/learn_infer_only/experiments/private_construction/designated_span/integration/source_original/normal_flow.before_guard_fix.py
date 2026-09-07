#!/usr/bin/env python3
"""Only normal 40 Learn /4 Infer /8 expiry + orderly reopening + exact retries."""
from pathlib import Path
import argparse,hashlib,json,os,sqlite3,subprocess,sys,time
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'source/journal'))
from run import Run
from common import canonical,read_json,write_json,require,sha,digest,rpc

def main():
 parser=argparse.ArgumentParser();parser.add_argument('--root',required=True);args=parser.parse_args()
 root=Path(args.root).resolve();fixture=root.parent/(root.name+'-public-queries');fixture.mkdir(parents=True,exist_ok=False)
 rows=read_json(HERE/'source/crypto/rows.json');policy=[]
 for i,row in enumerate(rows):
  path=fixture/f'row-{i:02d}.json';write_json(path,row);policy.append({'route':0,'path':str(path)})
 write_json(fixture/'policy.json',policy)
 started=time.perf_counter_ns();run=Run(root,fixture/'policy.json',HERE/'source/crypto/crypto.py')
 def private_role(entry,*flags):
  out=subprocess.run([sys.executable,str(HERE/'source'/entry),*map(str,flags)],capture_output=True,timeout=300)
  require(out.returncode==0,'privateRole:'+entry+':'+out.stderr.decode())
  # This log is private even though these roles deliberately emit aggregate-only JSON.
  with (root/'.private/role_calls.jsonl').open('ab') as f:f.write(canonical({'entry':entry,'stdout':out.stdout.decode(),'stderr':out.stderr.decode()})+b'\n')
  return json.loads(out.stdout)
 def progress(stage,**values):
  obj={'stage':stage,'public_elapsed_ns':time.perf_counter_ns()-started,**values}
  write_json(root/'progress.json',obj);print(json.dumps(obj),flush=True)
 try:
  oracle=private_role('oracle.py','prepare','--root',root,'--rows',HERE/'source/crypto/rows.json')
  requests=[];envelopes={};expiries=0;checkpoint=None
  progress('setup_complete',genesis=digest(run.g),recipient_key_count=16)
  for n in range(1,41):
   req=run.prepare('Learn',0,f'learn-{n:02d}',vector=root/'.private/oracle'/f'input-{n:02d}.json')
   reply=run.accepted(req);requests.append(req);envelopes[req['action']['request_id']]=reply['envelope']
   require(reply['delivery']['status']=='verified_not_a_release','learnIndependentDelivery')
   expiries+=req['proposal']['expired_ct'] is not None
   if n%10==0:
    req=run.prepare('Infer',0,f'infer-{n:02d}',query_index=n//10-1)
    reply=run.accepted(req);requests.append(req);envelopes[req['action']['request_id']]=reply['envelope']
    require(reply['delivery']['reader']['status']=='ciphertextAccepted','publicAckWithoutDecode')
    require(not (root/'.private/reader/answers.sqlite3').exists(),'noScalarDatabaseDuringPublicPhase')
    progress('public_events',learns=n,infers=n//10,expiries=expiries,revision=run.head()['revision'])
   if n==20:
    before=run.head();verified=rpc(run.rcfg['socket'],{'op':'verified_status'})
    require(verified['revision']==before['revision']==22 and verified['state_digest']==before['state_digest'],'checkpointAgreement')
    run.close()
    run.reader=run.start('reader',root/'.private/reader/config.json');run.authority=run.start('authority',root/'.private/authority/config.json')
    after=run.head();verified_after=rpc(run.rcfg['socket'],{'op':'verified_status'})
    require(after==before and verified_after==verified,'orderlyReopenExactHead')
    checkpoint={'revision':22,'state_digest':before['state_digest'],'orderly_close_reopen':True,'exact_head_preserved':True}
    write_json(root/'checkpoint.json',checkpoint)
  status=rpc(run.rcfg['socket'],{'op':'status'});verified=rpc(run.rcfg['socket'],{'op':'verified_status'})
  require(status['received']==status['selected']==4 and verified['revision']==44,'publicCompletion')
  require(not (root/'.private/reader/answers.sqlite3').exists(),'publicCompletionBeforeDecode')
  # Exact authorized historical requests, including an inference, are retried while
  # no private decode has happened. They do not advance the continuing history.
  retries=[]
  for req in [requests[0],next(q for q in requests if q['action']['kind']=='Infer')]:
   reply=run.accepted(req);require(reply['status']=='replayed' and reply['envelope']==envelopes[req['action']['request_id']],'exactAuthorizedHistoricalReplay')
   if req['action']['kind']=='Infer':require(reply['delivery']['reader']['status']=='replayed','publicReceiveDedup')
   retries.append(req['action']['request_id'])
  require(run.head()['revision']==44,'replayDoesNotAdvance')
  public_done_ns=time.perf_counter_ns()-started
  # No host-visible calls, progress timings or event handling occur during drain.
  first=private_role('journal/drain.py','--config',root/'.private/reader/drain_config.json')
  comparison=private_role('oracle.py','compare','--root',root)
  second=private_role('journal/drain.py','--config',root/'.private/reader/drain_config.json')
  require(first['new_private_decodes']==4 and second['new_private_decodes']==0 and second['already_private_decoded']==4,'privateDrainDedup')
  replay=run.replay(True)
  with sqlite3.connect(root/'.private/reader/answers.sqlite3') as db:
   require(db.execute('SELECT count(*),sum(decode_count) FROM private_decodes').fetchone()==(4,4),'privateExactlyOnceStored')
  # Public log omission check: no primitive reader-decrypt invocation or scalar
  # field appears in the public command/role/event/server logs.
  logs=[p for p in root.glob('*.jsonl') if p.is_file()]
  for path in logs:
   data=path.read_text();require('reader-decrypt' not in data and 'signed_score' not in data and 'decode_elapsed_ns' not in data,'publicLogOmitsPrivateDecode:'+path.name)
  report={'schema':'designated-span-normal-integration-v1','ok':True,'genesis':digest(run.g),'context_id':run.g['context_id'],
   'learns':40,'infers':4,'exact_original_expiries':expiries,'recipient_key_count':16,'selected_rows':[0,1,2,3],
   'private_integer_comparisons':comparison['private_integer_comparisons'],'all_private_integer_comparisons_match':True,
   'public_acceptance_precedes_any_scalar_decode':True,'public_service_has_recipient_key_paths':False,
   'public_logs_omit_scalar_and_private_decode_calls_and_costs':True,'private_decode_count':4,'private_drain_retry_new_decodes':0,
   'authorized_historical_retries':retries,'checkpoint':checkpoint,'independent_reader':verified,'independent_replay':replay,
   'public_event_phase_elapsed_ns':public_done_ns,'runtime_scope':'public verification/acceptance phase only; private drain costs omitted',
   'scope':'Classical DDH designated fixed-span; full 16-key recipient coalition, honest setup/issuer/erasure, shared-account role separation; no PQ/OS-isolation/recipient-self-restraint claim'}
  require(expiries==8 and replay['revision']==44,'normalCounts')
  write_json(root/'report.json',report)
  print(json.dumps({'ok':True,'report':str(root/'report.json'),'learns':40,'infers':4,'expiries':8,'all_private_integer_comparisons_match':True}),flush=True)
 finally:run.close()
if __name__=='__main__':main()
