"""Actual-process mutation, expiry, crash, race, restore and credential controls."""
import argparse,concurrent.futures,shutil,signal
from datasets import *

def expect_refusal(reply,label):
 require(reply.get('ok') is False,'expectedRefusal:'+label);return {'label':label,'reason':reply['reason']}
def receive(run,envelope,ct):return rpc(run.rcfg['socket'],{'op':'receive','envelope':envelope,'ciphertext':base64.b64encode(ct).decode()})
def clone(x):return copy.deepcopy(x)
def normal_inputs(root):
 root.mkdir(parents=True,exist_ok=False);q=root/'query.json';v=root/'vector.json';other=root/'other.json'
 write_json(q,[1]+[0]*576);write_json(v,[5,-3,2]+[0]*574);write_json(other,[-7,4,1]+[0]*574)
 policy=root/'policy.json';write_json(policy,[{'route':0,'path':str(q)}]);return policy,v,other

def mutations(parent,policy,vector,other):
 run=Run(parent/'mutations',policy);out=[]
 try:
  req=run.prepare('Learn',0,'first',vector=vector)
  values={'genesis':'0'*64,'params_id':'0'*64,'program_id':'0'*64,'program_version':2,'key_id':'0'*64,'public_key_sha256':'0'*64,'recipient':'other','route':1,'parent_revision':1,'parent_state':'0'*64,'nonce':'changed','record_id':'changed','fresh_ct':run.g['zero_ct_sha256'],'feature_policy':'other','range_assertion':[-128,127]}
  for field,value in list(values.items())+[('program_version',True),('program_version',1.0),('range_assertion',[-127.0,127.0])]:
   bad=clone(req);bad['action'][field]=value;out.append(expect_refusal(run.submit(bad),'action_'+field))
  for field,value in {'result_ct':run.g['zero_ct_sha256'],'expired_ct':run.g['zero_ct_sha256'],'next_state':'0'*64}.items():
   bad=clone(req);bad['proposal'][field]=value;out.append(expect_refusal(run.submit(bad),'proposal_'+field))
  bad=clone(req);bad['authorization']['signature']=base64.b64encode(bytes(64)).decode();out.append(expect_refusal(run.submit(bad),'unauthorized_issuer'))
  out.append(expect_refusal(rpc(run.acfg['socket'],{'op':'submit','request':req,'fault':'after_publication'}),'client_fault_hook'))
  require(run.head()['revision']==0,'mutationNoCommit')
  first=run.accepted(req);out.append(expect_refusal(receive(run,first['envelope'],run.host_cas.get(req['proposal']['result_ct']).read_bytes()),'genuine_learn_receipt_cannot_decrypt'))
  inferred=run.prepare('Infer',0,'selected-infer',query_index=0);good=run.accepted(inferred);packet=good['envelope'];ct=run.host_cas.get(inferred['proposal']['result_ct']).read_bytes()
  bad=clone(packet);bad['payload']['request']['action']['recipient']='other';out.append(expect_refusal(receive(run,bad,ct),'recipient_substitution'))
  out.append(expect_refusal(receive(run,packet,run.host_cas.get(run.g['zero_ct_sha256']).read_bytes()),'ciphertext_substitution'))
  dup=receive(run,packet,ct);require(dup['ok'] and dup['status']=='replayed','recipientExactRetry')
  after=run.prepare('Learn',0,'after-infer',vector=other);run.accepted(after)
  retry=run.accepted(req);require(retry['status']=='replayed' and retry['envelope']==first['envelope'],'historicalRetryAfterMixed')
  changed=clone(req);changed['proposal']['next_state']='0'*64;out.append(expect_refusal(run.submit(changed),'changed_same_request_id'))
  # Valid authorization at an old host snapshot: current authority refuses it.
  snapshot={'revision':0,'state_digest':req['action']['parent_state'],'state':initial_state(run.g)}
  stale=run.prepare('Learn',0,'restored-host',vector=other,head=snapshot);out.append(expect_refusal(run.submit(stale),'restored_host_snapshot'))
  # Input record/nonce uniqueness get direct witnesses at a CURRENT head, with valid issuer signature.
  fresh=run.prepare('Learn',0,'uniqueness',vector=other);issuer=read_json(run.root/'.private/issuer/config.json')
  for field,value,label in [('nonce',req['action']['nonce'],'already_consumed_nonce'),('record_id',req['action']['record_id'],'already_admitted_record')]:
   bad=clone(fresh);bad['action'][field]=value;bad['authorization']=sign(bad['action'],issuer['signing_key'],'resident-issuer-v1');out.append(expect_refusal(run.submit(bad),label))
  # Every trusted read rehashes bytes, even when canonical inspection was cached.
  path=Path(run.acfg['cas'])/fresh['action']['fresh_ct'];raw=path.read_bytes();atomic_write(path,raw[:-1]+bytes([raw[-1]^1]))
  out.append(expect_refusal(run.submit(fresh),'corrupt_cached_blob'));atomic_write(path,raw)
  missing=path.with_suffix('.saved');path.rename(missing)
  out.append(expect_refusal(run.submit(fresh),'missing_blob'));missing.rename(path)
  return {'ok':True,'refusals':out,'historical_retry_after_mixed':True,'recipient_exact_retry':True,'replay':run.replay(True)}
 finally:run.close()

def expiry(parent,policy,vector):
 run=Run(parent/'expiry',policy)
 try:
  for n in range(32):run.accepted(run.prepare('Learn',0,f'learn-{n:02d}',vector=vector))
  req=run.prepare('Learn',0,'expiry-32',vector=vector);head=run.head();queue=head['state']['routes']['0']['queue'];old=queue[0]['ct_sha256'];different=queue[1]['ct_sha256']
  require(old!=different,'samePlaintextDifferentCiphertexts')
  bad=clone(req);bad['proposal']['expired_ct']=different;refusal=expect_refusal(run.submit(bad),'different_old_serialized_ciphertext')
  # Actually recompute with the wrong same-plaintext encryption: plaintext cancellation is insufficient.
  output=run.host_cas.fresh_output();run.host_cas.crypto.run('host-learn',acc=run.host_cas.get(head['state']['routes']['0']['acc_ct']),fresh=run.host_cas.get(req['action']['fresh_ct']),old=run.host_cas.get(different),out=output)
  wrong=run.host_cas.finish_output(output);require(wrong!=req['proposal']['result_ct'],'wrongOldChangesCiphertext')
  bad=clone(req);bad['proposal']['result_ct']=wrong;refusal2=expect_refusal(run.submit(bad),'wrong_old_actual_arithmetic')
  run.accepted(req);run.accepted(run.prepare('Infer',0,'after-expiry',query_index=0));require(run.answers()['after-expiry']==160,'expiryOracle')
  return {'ok':True,'learns':33,'expiry':1,'same_plaintext_distinct_old_ciphertexts':True,'wrong_old_changes_result_bytes':True,'refusals':[refusal,refusal2],'oracle_comparisons':1,'oracle_all_match':True,'replay':run.replay(True)}
 finally:run.close()

def crash_case(parent,policy,vector,point):
 run=Run(parent/point,policy)
 try:
  run.accepted(run.prepare('Learn',0,'learn',vector=vector));req=run.prepare('Infer',0,'infer',query_index=0)
  run.stop(run.authority);marker=run.root/'crash_marker.txt';run.authority=run.start('authority',run.root/'.private/authority/config.json',fault=point,marker=marker)
  try:run.submit(req);raise AssertionError('expected SIGKILL')
  except (EOFError,OSError):pass
  code=run.authority.wait(timeout=10);require(code==-signal.SIGKILL,'actualProcessCrash')
  run.authority=run.start('authority',run.root/'.private/authority/config.json');before=run.head();reader_before=rpc(run.rcfg['socket'],{'op':'status'})
  require(before['revision']==(1 if point=='before_reservation' else 2),'crashCommitBoundary')
  require(reader_before['received']==(1 if point=='after_publication' else 0),'crashPublicationBoundary')
  retry=run.accepted(req);again=run.accepted(req);require(retry['envelope']==again['envelope'],'crashExactRetry')
  require(rpc(run.rcfg['socket'],{'op':'status'})['received']==1,'oneLogicalPacket')
  return {'ok':True,'point':point,'process_exit':code,'before_retry_revision':before['revision'],'before_retry_received':reader_before['received'],'after_retry_revision':run.head()['revision'],'logical_packets':1,'exact_retry':True,'replay':run.replay(True)}
 finally:run.close()

def race(parent,policy,vector,other):
 run=Run(parent/'race',policy)
 try:
  head=run.head();a=run.prepare('Learn',0,'candidate-A',vector=vector,head=head);b=run.prepare('Learn',0,'candidate-B',vector=other,head=head)
  address='/tmp/rsj-race-'+os.urandom(6).hex()+'.sock';second=run.start('authority',run.root/'.private/authority/config.json',socket=address)
  messages=[];processes=[]
  for index,(req,sock) in enumerate([(a,run.acfg['socket']),(b,address)]):
   path=run.work/f'race-{index}.json';write_json(path,{'op':'submit','request':req});messages.append(path)
   processes.append(subprocess.Popen([sys.executable,str(HERE/'client.py'),'--socket',sock,'--message',str(path)],stdout=subprocess.PIPE,stderr=subprocess.PIPE))
  replies=[]
  for proc in processes:
   stdout,stderr=proc.communicate(timeout=90);require(proc.returncode==0 and not stderr,'raceClientProcess');replies.append(json.loads(stdout))
  require(sum(x.get('ok') is True for x in replies)==1,'oneRaceWinner');require(run.head()['revision']==1,'oneRaceRevision');winner=a if replies[0]['ok'] else b;accepted=replies[0] if replies[0]['ok'] else replies[1]
  retry=run.accepted(winner);require(retry['envelope']==accepted['envelope'],'raceExactRetry');Path(address).unlink(missing_ok=True)
  return {'ok':True,'authority_pids':[run.authority.pid,second.pid],'client_pids':[p.pid for p in processes],'same_database':True,'replies':replies,'journal_rows':1,'replay':run.replay(True)}
 finally:run.close()

def pending_retries(parent,policy,vector):
 run=Run(parent/'pending_retries',policy)
 try:
  run.accepted(run.prepare('Learn',0,'learn',vector=vector));req=run.prepare('Infer',0,'pending',query_index=0)
  run.stop(run.authority);marker=run.root/'crash_marker.txt';run.authority=run.start('authority',run.root/'.private/authority/config.json',fault='after_commit',marker=marker)
  try:run.submit(req)
  except (EOFError,OSError):pass
  require(run.authority.wait(timeout=10)==-signal.SIGKILL,'pendingActualCrash')
  run.authority=run.start('authority',run.root/'.private/authority/config.json');address='/tmp/rsj-pending-'+os.urandom(6).hex()+'.sock';second=run.start('authority',run.root/'.private/authority/config.json',socket=address)
  path=run.work/'retry.json';write_json(path,{'op':'submit','request':req});procs=[]
  for i in range(8):procs.append(subprocess.Popen([sys.executable,str(HERE/'client.py'),'--socket',run.acfg['socket'] if i%2==0 else address,'--message',str(path)],stdout=subprocess.PIPE,stderr=subprocess.PIPE))
  replies=[]
  for proc in procs:
   stdout,stderr=proc.communicate(timeout=90);require(proc.returncode==0 and not stderr,'pendingClientProcess');replies.append(json.loads(stdout))
  require(all(r.get('ok') and r['status']=='replayed' and r['delivery']['status']=='acknowledged' for r in replies),'pendingRetryReplies')
  require(len({digest(r['envelope']) for r in replies})==1,'pendingExactEnvelope')
  require(run.head()['revision']==2 and rpc(run.rcfg['socket'],{'op':'status'})['received']==1,'pendingOneInstallPacket')
  decrypts=[json.loads(line) for line in (run.root/'commands.jsonl').read_bytes().splitlines() if json.loads(line)['command'][1]=='reader-decrypt'];require(len(decrypts)==1,'pendingOneDecryption')
  Path(address).unlink(missing_ok=True)
  return {'ok':True,'actual_postcommit_SIGKILL':True,'authority_workers':2,'client_processes':8,'exact_reply_envelopes':1,'logical_packets':1,'reader_decrypt_calls':1,'revision':2,'replay':run.replay(True)}
 finally:run.close()

def rollback(parent,policy,vector,other):
 run=Run(parent/'authority_rollback',policy)
 try:
  head=run.head();a=run.prepare('Learn',0,'branch-A',vector=vector,head=head);b=run.prepare('Learn',0,'branch-B',vector=other,head=head)
  snapshot=run.root/'snapshot.sqlite3'
  with sqlite3.connect(run.acfg['db']) as source,sqlite3.connect(snapshot) as dest:source.backup(dest)
  first=run.accepted(a);run.stop(run.authority)
  # Trusted negative fixture deliberately violates independent authority persistence.
  for suffix in ['', '-wal','-shm']:Path(run.acfg['db']+suffix).unlink(missing_ok=True)
  shutil.copyfile(snapshot,run.acfg['db']);run.authority=run.start('authority',run.root/'.private/authority/config.json')
  second=run.accepted(b)
  require(first['envelope']['payload']['revision']==second['envelope']['payload']['revision']==1,'rollbackSameRevision')
  require(first['envelope']['payload']['next_state']!=second['envelope']['payload']['next_state'],'rollbackDistinctActualStates')
  return {'ok':True,'negative_control':'authority rollback violates finality premise','two_valid_authority_signatures':all(bool(verify(r['envelope'],run.g['authority_vk'],'resident-authority-finalization-v1')) for r in [first,second]),
   'same_parent_and_revision':True,'distinct_actual_state_digests':True,'envelopes':[first['envelope'],second['envelope']]}
 finally:run.close()

def compromised_signer(parent,policy,vector):
 run=Run(parent/'compromised_authority_signer',policy)
 try:
  learn=run.prepare('Learn',0,'learn',vector=vector);run.accepted(learn)
  req=run.prepare('Infer',0,'authorized-query',query_index=0)
  # Corrupt authority signer substitutes a public-state ciphertext, preserving the signed query action.
  # Use zero Ct so the false selected score differs from honest query score5 without publishing either value.
  wrong=run.g['zero_ct_sha256'];require(wrong!=req['proposal']['result_ct'],'wrongCiphertextDistinct')
  forged_req=clone(req);forged_req['proposal']['result_ct']=wrong
  p={'schema':'resident-finalized-v1','request':forged_req,'request_sha256':digest(forged_req),'revision':req['action']['parent_revision']+1,'parent_state':req['action']['parent_state'],'next_state':req['action']['parent_state'],
   'delta':{'kind':'Infer','route':0,'query_ct':req['action']['query_ct'],'output_ct':wrong},'output_ct':wrong}
  forged=sign(p,run.acfg['signing_key'],'resident-authority-finalization-v1');reply=receive(run,forged,run.host_cas.get(wrong).read_bytes());require(reply.get('ok'),'expectedTrustedSignerBoundary')
  require(run.head()['revision']==1 and run.answers()['authorized-query']!=5,'forgedOutputNotCommittedOrCorrect')
  return {'ok':True,'negative_control':'baseline reader trusts authority validation; stolen signer bypasses public recomputation','valid_signature_wrong_output_accepted':True,'authority_committed_infer':False,'private_oracle_detected_mismatch':True,'forged_envelope':forged,'reader_ack':reply}
 finally:run.close()

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);a=p.parse_args();root=Path(a.root).resolve();policy,v,other=normal_inputs(root)
 results={}
 cases=[('mutations',lambda:mutations(root,policy,v,other)),('expiry',lambda:expiry(root,policy,v)),*[(point,lambda point=point:crash_case(root,policy,v,point)) for point in ['before_reservation','after_commit','after_publication']],('race',lambda:race(root,policy,v,other)),('pending_retries',lambda:pending_retries(root,policy,v)),('authority_rollback',lambda:rollback(root,policy,v,other)),('compromised_authority_signer',lambda:compromised_signer(root,policy,v))]
 for name,call in cases:
  results[name]=call();write_json(root/'partial_report.json',results);print(json.dumps({'case':name,'ok':True}),flush=True)
 report={'ok':True,'schema':'resident-journal-controls-v1','cases':results,'source_sha256':sources()};write_json(root/'report.json',report)
if __name__=='__main__':main()
