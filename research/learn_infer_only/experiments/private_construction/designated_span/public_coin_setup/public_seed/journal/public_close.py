"""Postshutdown public signature/history/storage closure; no private paths or DDH work."""
from pathlib import Path
import argparse,collections,gzip,json,sqlite3
from driver import check_pins,file_sha
from setup_join import verify_binding
from common import canonical,digest,read_json,require,sha,verify,write_json
HERE=Path(__file__).resolve().parent

def close(root,reports):
 check_pins(reports);binding=verify_binding(root)
 public=read_json(reports/'public_complete.json');g=read_json(reports/'genesis.json')
 require(public['all_public_workers_and_services_closed'] and public['all_public_replay_and_operations_before_private_drain'],'publicWorkerClosed')
 require(public['genesis_sha256']==digest(g)==binding['genesis_sha256'],'genesisBinding')
 for name in ['genesis.json','public_context.json','registry.json','public_transcript.json','context_validation.json','public_setup_verification.json','setup_report.json','public_log_audit.json','orderly_reopen.json','final_seed_replay.json']:
  require((root/name).read_bytes()==(reports/name).read_bytes(),'publicSnapshotIdentity:'+name)
 transcript=read_json(reports/'public_transcript.json');registry=read_json(reports/'registry.json')
 for i,(announcement,slot) in enumerate(zip(transcript['announcements'],registry['slots'],strict=True)):
  payload=verify(announcement,slot['verification_key'],'public-coin-fixed-slot-announcement-v1')
  require(payload['row_id']==slot['row_id']==i and payload['row_sha256']==slot['row_sha256'],'registrationSignatureIdentity')
  require(transcript['complete_domain']['complete_registry'][i]==dict(slot,A=payload['A']),'completeRegistryJoin')
 final=read_json(reports/'final_seed_replay.json');result=json.loads(final['stdout'])
 require(final['exit_code']==0 and result['complete_raw_hash_tape_match'] and result['complete_context_byte_match'] and result['context_id']==g['context_id'] and result['transcript_sha256']==digest(transcript),'finalSeedReplayRecord')
 envelopes=read_json(reports/'accepted_envelopes.json');require(len(envelopes)==37,'37EnvelopeCount')
 expected=[]
 for n in range(1,34):
  expected.append(('Learn',f'learn-{n:02d}'))
  if n in [1,16,32,33]:expected.append(('Infer',f'infer-{n:02d}'))
 state={'schema':'resident-window-state-v1','params_id':g['crypto']['params_id'],'key_id':g['key_id'],'genesis':digest(g),'routes':{str(r):{'queue':[],'acc_ct':g['zero_ct_sha256'],'admissions':0} for r in g['routes']}}
 fresh=[];seen=set();nonces=set();expiries=0;infers=0
 for revision,(envelope,(kind,event)) in enumerate(zip(envelopes,expected,strict=True),1):
  p=verify(envelope,g['authority_vk'],'resident-authority-finalization-v1');req=p['request'];a=req['action'];delta=p['delta'];proposal=req['proposal']
  key=g['issuer_vk'] if kind=='Learn' else g['command_vk'];domain='resident-issuer-v1' if kind=='Learn' else 'resident-query-authorization-v1'
  require(verify(req['authorization'],key,domain)==a,'authorizationSignature')
  require(a['kind']==kind and a['request_id']==event and a['route']==0,'fixedEventOrder')
  require(a['genesis']==digest(g) and a['context_id']==a['key_id']==g['context_id'] and a['public_key_sha256']==g['public_key_sha256'],'receiptSetupIdentity')
  require(p['revision']==revision and a['parent_revision']==revision-1 and p['parent_state']==a['parent_state']==digest(state) and p['request_sha256']==digest(req),'receiptChain')
  require(a['request_id'] not in seen and a['nonce'] not in nonces,'receiptUniqueness');seen.add(a['request_id']);nonces.add(a['nonce'])
  route=state['routes']['0'];require(delta['kind']==kind and delta['route']==0,'deltaIdentity')
  if kind=='Learn':
   entry={'record_id':a['record_id'],'ct_sha256':a['fresh_ct']};old=route['queue'][0] if len(route['queue'])==32 else None
   require(delta['fresh']==entry and delta['expired']==old and proposal['expired_ct']==(old['ct_sha256'] if old else None),'originalExpiryIdentity')
   require(a['fresh_ct'] not in fresh,'freshCiphertextIdentity');fresh.append(a['fresh_ct'])
   if old:route['queue'].pop(0);expiries+=1
   route['queue'].append(entry);route['acc_ct']=delta['acc_ct'];route['admissions']+=1
   require(delta['acc_ct']==proposal['result_ct'] and p['output_ct'] is None,'learnOutputBinding')
  else:
   require(a['row_id']==infers and {'query_ct':a['query_ct'],'route':0} in g['query_policy'],'queryPolicy')
   q=g['query_bindings'][a['query_ct']]
   require(all(a[k]==q[k] for k in ['context_id','row_id','row_sha256','token_sha256']) and a['recipient']==q['recipient_id'],'recipientBinding')
   require(delta['query_ct']==a['query_ct'] and delta['output_ct']==proposal['result_ct']==p['output_ct'] and proposal['expired_ct'] is None,'inferOutputBinding');infers+=1
  require(p['next_state']==proposal['next_state']==digest(state),'stateDigest')
 require(expiries==1 and infers==4 and [e['ct_sha256'] for e in state['routes']['0']['queue']]==fresh[1:],'completeFinalFIFO')
 replay=json.loads(gzip.decompress((reports/'replay.json.gz').read_bytes()))
 require(replay['revision']==37 and replay['genesis']==digest(g) and replay['state_digest']==digest(state) and replay['head']['state']==state and replay['public_recomputation'],'savedFullReplay')
 require([r['envelope'] for r in replay['journal_rows']]==envelopes,'fullReplayHistory')
 events=[json.loads(x) for x in gzip.decompress((reports/'events.jsonl.gz').read_bytes()).splitlines()]
 require(len(events)==38 and [e['reply']['envelope'] for e in events[:37]]==envelopes,'savedEventHistory')
 require(events[-1]['reply']['status']=='replayed' and events[-1]['reply']['envelope']==envelopes[1],'exactHistoricalInferRetry')
 require(public['authorized_historical_retries']==['infer-01'] and public['orderly_reopen']['revision']==18 and public['orderly_reopen']['exact_head_preserved'],'fixedReopenRetry')
 calls=[json.loads(x) for x in gzip.decompress((reports/'commands.jsonl.gz').read_bytes()).splitlines()]
 require(all(c['exit_code']==0 and not c['private_output_omitted'] for c in calls),'successfulPublicCalls')
 require(not {'keygen','initializer','recipient-register','reader-decrypt'}.intersection(c['command'][1] for c in calls),'publicCommandsOnly')
 for role in ['host','authority','reader','independent_public_replay']:
  counts=collections.Counter(c['command'][1] for c in calls if c['role']==role and c['command'][1] in ['host-learn','host-infer'])
  require(counts=={'host-learn':33,'host-infer':4},'completeRoleArithmetic:'+role)
 # Read only the two public journal databases after all services have closed.
 for role,table,headtable in [('authority','journal','meta'),('reader','verified_journal','verified_head')]:
  dbpath=root/role/'journal.sqlite3'
  with sqlite3.connect(f'file:{dbpath}?mode=ro',uri=True) as db:
   require([json.loads(row[0]) for row in db.execute(f'SELECT envelope FROM {table} ORDER BY revision')]==envelopes,'closedDatabaseHistory:'+role)
   row=db.execute(f'SELECT genesis,revision,state,state_digest FROM {headtable}').fetchone()
   require(row[0]==digest(g) and row[1]==37 and json.loads(row[2])==state and row[3]==digest(state),'closedDatabaseHead:'+role)
   if role=='reader':
    require(db.execute('SELECT count(*) FROM received').fetchone()[0]==db.execute('SELECT count(*) FROM expected').fetchone()[0]==4,'fourSelectedCiphertexts')
    require('answer' not in [r[1] for r in db.execute('PRAGMA table_info(received)')],'keylessAcceptorStorage')
 inventories=read_json(reports/'public_ciphertext_inventory.json');objects=0
 for role,directory in [('host',root/'host_cas'),('authority',root/'authority/cas'),('acceptor',root/'reader/cas')]:
  files=sorted(p for p in directory.iterdir() if p.is_file() and len(p.name)==64)
  observed=[{'sha256':file_sha(p),'bytes':p.stat().st_size} for p in files]
  require(observed==inventories[role] and all(p.name==item['sha256'] for p,item in zip(files,observed,strict=True)),'closedCASInventory:'+role);objects+=len(files)
 check_pins(reports)
 output={'schema':'public-seed-journal-postshutdown-verification-v1','ok':True,'genesis_sha256':digest(g),'context_id':g['context_id'],'binding':binding,'authority_signature_checks':37,'authorization_signature_checks':37,'registration_signature_checks':16,'ordered_events':37,'exact_original_expiries':1,'historical_infer_retries':1,'orderly_reopen_revision':18,'closed_public_database_histories':2,'public_cas_objects':objects,'full_arithmetic_replay_record_verified':True,'private_files_read':0,'group_arithmetic_reexecuted':False,'services_started':False,'public_complete_sha256':file_sha(reports/'public_complete.json'),'execution_pins_sha256':file_sha(reports/'execution_pins.json')}
 write_json(reports/'public_verification.json',output);print(json.dumps(output),flush=True)

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True);p.add_argument('--reports',type=Path,required=True);a=p.parse_args()
 require(a.root.resolve()==HERE/'runtime/normal_001' and a.reports.resolve()==HERE/'reports/normal_001','fixedPublicClosePaths')
 close(a.root.resolve(),a.reports.resolve())
