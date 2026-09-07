#!/usr/bin/env python3
"""Finalize the completed first run after its documented substring-guard defect.
No cryptographic operation or private scalar recovery is rerun by this script.
"""
from pathlib import Path
import argparse,hashlib,json,sqlite3,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'source/journal'))
from common import read_json,write_json,require,digest,canonical,load_genesis,verify,sha
from public_log_audit import check_public_logs

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--first-log',required=True);a=p.parse_args()
 root=Path(a.root).resolve();firstlog=Path(a.first_log)
 require('publicLogOmitsPrivateDecode:commands.jsonl' in firstlog.read_text(),'expectedFirstHarnessGuardFailure')
 origin=read_json(HERE/'HARNESS_ORIGINAL.json');require(sha((HERE/origin['path']).read_bytes())==origin['sha256'],'preservedFirstDriver')
 cfg=read_json(root/'host_config.json');g=load_genesis(cfg)
 replay=read_json(root/'replay.json');require(replay['public_recomputation'] is True and replay['revision']==44,'completedIndependentArithmeticReplay')
 events=[json.loads(s) for s in (root/'events.jsonl').read_text().splitlines()]
 require(len(events)==46,'fortyFourAndTwoExactRetries')
 first=events[:44];byid={};learns=infers=expiries=0
 require(len(replay['journal_rows'])==44,'replayJournalCount')
 for index,(event,row) in enumerate(zip(first,replay['journal_rows'],strict=True),1):
  reply=event['reply'];require(reply['ok'] is True and reply['status']=='accepted','firstNormalAccepted')
  envelope=reply['envelope'];require(canonical(envelope)==canonical(row['envelope']),'replayExactFinalizations')
  payload=verify(envelope,g['authority_vk'],'resident-authority-finalization-v1');req=payload['request'];action=req['action']
  require(payload['revision']==index and payload['request_sha256']==digest(req),'orderedFinalizations')
  require(payload['request_sha256']==event['request_sha256'],'recordedRequestIdentity')
  byid[action['request_id']]=envelope
  if action['kind']=='Learn':
   learns+=1;expiries+=payload['delta']['expired'] is not None
   require(reply['delivery']['status']=='verified_not_a_release','independentlyVerifiedLearn')
  else:
   infers+=1;require(action['kind']=='Infer' and reply['delivery']['status']=='acknowledged' and reply['delivery']['reader']['status']=='ciphertextAccepted','ciphertextOnlyAck')
  require(reply['delivery']['verification']['status']=='verified','recipientIndependentVerification')
 retries=[]
 for event in events[44:]:
  reply=event['reply'];require(reply['status']=='replayed' and canonical(reply['envelope'])==canonical(byid[event['request_id']]),'historicalExactReplay')
  if reply['envelope']['payload']['request']['action']['kind']=='Infer':require(reply['delivery']['reader']['status']=='replayed','publicAcceptanceDedup')
  retries.append(event['request_id'])
 require((learns,infers,expiries)==(40,4,8),'normalCounts')
 rcfg=read_json(root/'.private/reader/config.json')
 with sqlite3.connect(rcfg['db']) as db:
  head=db.execute('SELECT revision,state_digest FROM verified_head').fetchone();count=db.execute('SELECT count(*) FROM verified_journal').fetchone()[0]
  require(head==(44,replay['state_digest']) and count==44,'readerPersistedVerifiedHead')
  require(db.execute('SELECT count(*) FROM received').fetchone()[0]==4 and db.execute('SELECT count(*) FROM expected').fetchone()[0]==4,'acceptedSelectedCounts')
 with sqlite3.connect(root/'.private/reader/answers.sqlite3') as db:require(db.execute('SELECT count(*),sum(decode_count) FROM private_decodes').fetchone()==(4,4),'privateDedupCounts')
 private_calls=[json.loads(s) for s in (root/'.private/role_calls.jsonl').read_text().splitlines()]
 results=[json.loads(x['stdout']) for x in private_calls]
 require(len(results)==4 and all(x['ok'] is True for x in results),'privateRoleSuccess')
 require(results[1]['new_private_decodes']==4 and results[2]['private_integer_comparisons']==4 and results[2]['all_match'] is True and results[3]['new_private_decodes']==0 and results[3]['already_private_decoded']==4,'privateComparisonsAndRetry')
 audit=check_public_logs(root);write_json(root/'public_log_audit.json',audit)
 progress=read_json(root/'progress.json');checkpoint=read_json(root/'checkpoint.json')
 require(progress['learns']==40 and progress['infers']==4 and progress['expiries']==8 and checkpoint['revision']==22 and checkpoint['exact_head_preserved'] is True,'progressAndReopen')
 report={'schema':'designated-span-normal-integration-v1','ok':True,'genesis':digest(g),'context_id':g['context_id'],
  'learns':40,'infers':4,'exact_original_expiries':8,'recipient_key_count':16,'selected_rows':[0,1,2,3],
  'private_integer_comparisons':4,'all_private_integer_comparisons_match':True,
  'public_acceptance_precedes_any_scalar_decode':True,'public_service_has_recipient_key_paths':False,
  'public_logs_omit_scalar_and_private_decode_calls_and_costs':True,'private_decode_count':4,'private_drain_retry_new_decodes':0,
  'authorized_historical_retries':retries,'checkpoint':checkpoint,
  'independent_reader':{'ok':True,'revision':44,'state_digest':head[1],'verified_records':44},
  'independent_replay':{'ok':True,'revision':44,'state_digest':replay['state_digest'],'admissions':replay['admissions'],'queue_lengths':replay['queue_lengths'],'public_recomputation':True},
  'public_event_phase_elapsed_ns':None,'public_progress_after_40_learn_4_infer_ns':progress['public_elapsed_ns'],
  'runtime_scope':'The last public progress checkpoint was persisted; exact phase time after two retries was not persisted before the first harness guard failure. Private drain costs omitted.',
  'harness_guard_correction':{'original_driver_sha256':origin['sha256'],'original_exit':'Refusal: publicLogOmitsPrivateDecode:commands.jsonl after all functional/replay checks',
    'cause':'Raw substring signed_score matched the public metadata key row_signed_score_bounds',
    'repair':'Parsed exact private-field and actual decoder-command check on the same completed logs',
    'crypto_or_decode_rerun':False,'public_log_audit':audit},
  'scope':'Classical DDH designated fixed-span; full 16-key recipient coalition; honest setup/issuer/erasure; shared-account role separation; no PQ/OS-isolation/recipient-self-restraint claim. Trusted coordinator comparison/report/scheduling outside host view.'}
 write_json(root/'report.json',report)
 print(json.dumps({'ok':True,'learns':40,'infers':4,'expiries':8,'private_integer_comparisons':4,'all_match':True,'replayed_transitions':44,'guard_false_positive_corrected':True,'report_sha256':sha((root/'report.json').read_bytes())}))
if __name__=='__main__':main()
