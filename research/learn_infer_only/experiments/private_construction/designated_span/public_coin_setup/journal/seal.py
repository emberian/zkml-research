#!/usr/bin/env python3
"""Inspect normal saved public evidence; no DDH arithmetic, RPC or private file access."""
from pathlib import Path
import argparse,base64,collections,gzip,hashlib,json,os
from cryptography.hazmat.primitives.asymmetric.ed25519 import Ed25519PublicKey
HERE=Path(__file__).resolve().parent

def rawsha(raw):return hashlib.sha256(raw).hexdigest()
def canonical(x):return json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=True,allow_nan=False).encode()
def digest(x):return rawsha(canonical(x))
def load(p):return json.loads(Path(p).read_bytes())
def write(p,x):Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def verify(envelope,key,domain):
 assert set(envelope)=={'domain','payload','signature'} and envelope['domain']==domain
 Ed25519PublicKey.from_public_bytes(bytes.fromhex(key)).verify(base64.b64decode(envelope['signature'],validate=True),canonical({'domain':domain,'payload':envelope['payload']}))
 return envelope['payload']
def main():
 parser=argparse.ArgumentParser();parser.add_argument('--reports',type=Path,required=True);a=parser.parse_args();reports=a.reports.resolve()
 pins=load(reports/'execution_pins.json')
 failed=HERE/'reports/normal_001';oldpins=load(failed/'execution_pins.json')
 for n,h in oldpins['source_files_sha256'].items():assert rawsha((failed/'source_snapshot'/n).read_bytes())==h
 oldcalls=[json.loads(x) for x in (failed/'commands.jsonl').read_bytes().splitlines()]
 assert [c['command'][1] for c in oldcalls]==['params','auth-init'] and [c['exit_code'] for c in oldcalls]==[0,1]
 for n,h in pins['source_files_sha256'].items():assert rawsha((HERE/n).read_bytes())==h
 for kind in ['native_dependency','interpreter']:assert rawsha(Path(pins[kind]['path']).read_bytes())==pins[kind]['sha256']
 for n,h in pins['signature_dependency']['files_sha256'].items():assert rawsha(Path(n).read_bytes())==h
 origins=load(HERE/'SOURCE_PINS.json')['files']
 for n,item in origins.items():assert rawsha(Path(item['origin']).read_bytes())==rawsha((HERE/n).read_bytes())==item['sha256']
 g=load(reports/'genesis.json');context=load(reports/'public_context.json');t=load(reports/'public_transcript.json');registry=load(reports/'registry.json');validation=load(reports/'context_validation.json');verification=load(reports/'public_setup_verification.json');binding=g['public_coin_setup']
 for n,h in binding['public_artifacts_sha256'].items():
  if n.startswith('announcements/'):
   index=int(Path(n).stem[1:]);assert digest(t['announcements'][index])==h
  else:assert rawsha((reports/n).read_bytes())==h
 assert digest(context)==g['context_id']==t['context_id']==verification['context_id']==g['key_id']==g['public_key_sha256']
 assert binding['setup_source_sha256']==t['setup_source_sha256']==rawsha((HERE/'source/public_setup/setup.py').read_bytes())
 assert binding['join_source_sha256']==rawsha((HERE/'setup_join.py').read_bytes())
 assert binding['dependency_inventory_sha256']==rawsha((HERE/'SOURCE_PINS.json').read_bytes())
 assert t['registry_sha256']==digest(registry) and t['crypto_sources']==g['crypto_sources'] and t['native_dependency']==g['native_dependency']
 assert verification['complete_context_byte_match'] and verification['transcript_sha256']==digest(t)
 assert validation['validated'] and validation['context_id']==g['context_id'] and validation['source_sha256']==g['crypto_sources']
 assert rawsha((reports/'context_validation.json').read_bytes())==g['context_validation_sha256']
 assert len(t['announcements'])==len(registry['slots'])==16
 fixed_rows=load(HERE/'source/crypto/rows.json');assert context['rows']==fixed_rows and t['rows_sha256']==digest(fixed_rows)
 expected_policy=[];expected_bindings={}
 for i,row in enumerate(fixed_rows):
  recipient=context['recipients'][i];assert recipient['row_id']==i and recipient['row_sha256']==digest(row)
  query={'schema':'resident-designated-query-v1','params_id':g['crypto']['params_id'],'context_id':g['context_id'],**{k:recipient[k] for k in ['row_id','row_sha256','recipient_id','token_sha256']},'coefficients':row}
  h=digest(query);expected_policy.append({'query_ct':h,'route':0});expected_bindings[h]={k:query[k] for k in ['context_id','row_id','row_sha256','recipient_id','token_sha256']}
 assert g['query_policy']==expected_policy and g['query_bindings']==expected_bindings
 for i,(announcement,slot) in enumerate(zip(t['announcements'],registry['slots'],strict=True)):
  p=verify(announcement,slot['verification_key'],'public-coin-fixed-slot-announcement-v1')
  assert p['row_id']==slot['row_id']==i and p['row_sha256']==slot['row_sha256']==digest(fixed_rows[i])
  assert p['A']==context['recipients'][i]['A']
 envelopes=load(reports/'accepted_envelopes.json');assert len(envelopes)==44
 expected=[]
 for n in range(1,41):
  expected.append(('Learn',f'learn-{n:02d}'))
  if n%10==0:expected.append(('Infer',f'infer-{n:02d}'))
 state={'schema':'resident-window-state-v1','params_id':g['crypto']['params_id'],'key_id':g['key_id'],'genesis':digest(g),'routes':{str(r):{'queue':[],'acc_ct':g['zero_ct_sha256'],'admissions':0} for r in g['routes']}}
 seen_ids=set();seen_nonces=set();fresh=[];expiries=0;inferences=0
 for revision,(envelope,(kind,event_id)) in enumerate(zip(envelopes,expected,strict=True),1):
  p=verify(envelope,g['authority_vk'],'resident-authority-finalization-v1');req=p['request'];action=req['action'];delta=p['delta'];proposal=req['proposal']
  key=g['issuer_vk'] if kind=='Learn' else g['command_vk'];domain='resident-issuer-v1' if kind=='Learn' else 'resident-query-authorization-v1'
  assert verify(req['authorization'],key,domain)==action
  assert action['kind']==kind and action['request_id']==event_id and action['route']==0
  assert action['genesis']==digest(g) and action['context_id']==g['context_id'] and action['key_id']==g['key_id']
  assert action['params_id']==g['crypto']['params_id'] and action['program_id']==g['crypto']['program_id'] and action['public_key_sha256']==g['public_key_sha256']
  assert p['revision']==revision and action['parent_revision']==revision-1
  assert p['parent_state']==action['parent_state']==digest(state) and p['request_sha256']==digest(req)
  assert action['request_id'] not in seen_ids and action['nonce'] not in seen_nonces
  seen_ids.add(action['request_id']);seen_nonces.add(action['nonce']);route=state['routes']['0']
  assert delta['kind']==kind and delta['route']==0
  if kind=='Learn':
   entry={'record_id':action['record_id'],'ct_sha256':action['fresh_ct']};old=route['queue'][0] if len(route['queue'])==32 else None
   assert delta['fresh']==entry and delta['expired']==old and proposal['expired_ct']==(old['ct_sha256'] if old else None)
   assert action['fresh_ct'] not in fresh;fresh.append(action['fresh_ct'])
   if old:route['queue'].pop(0);expiries+=1
   route['queue'].append(entry);route['acc_ct']=delta['acc_ct'];route['admissions']+=1
   assert delta['acc_ct']==proposal['result_ct'] and p['output_ct'] is None
  else:
   assert action['row_id']==inferences and {'query_ct':action['query_ct'],'route':0} in g['query_policy']
   q=g['query_bindings'][action['query_ct']]
   assert all(action[k]==q[k] for k in ['context_id','row_id','row_sha256','token_sha256']) and action['recipient']==q['recipient_id']
   assert delta['query_ct']==action['query_ct'] and delta['output_ct']==proposal['result_ct']==p['output_ct'] and proposal['expired_ct'] is None
   inferences+=1
  assert p['next_state']==proposal['next_state']==digest(state)
 assert expiries==8 and inferences==4 and len(fresh)==40
 assert [e['ct_sha256'] for e in state['routes']['0']['queue']]==fresh[8:]
 replay=json.loads(gzip.decompress((reports/'replay.json.gz').read_bytes()))
 assert replay['genesis']==digest(g) and replay['revision']==44 and replay['state_digest']==digest(state) and replay['head']['state']==state
 assert [r['envelope'] for r in replay['journal_rows']]==envelopes and replay['public_recomputation']
 calls=[json.loads(x) for x in gzip.decompress((reports/'commands.jsonl.gz').read_bytes()).splitlines()]
 names=[c['command'][1] for c in calls]
 assert not {'keygen','initializer','recipient-register','reader-decrypt'}.intersection(names)
 assert all(c['exit_code']==0 and not c['private_output_omitted'] for c in calls)
 assert [c['command'][1] for c in calls if c['role']=='honest_public_setup']==['auth-init']+['recipient-init']*16+['public-build','verify-public']
 for role in ['host','authority','reader','independent_public_replay']:
  arithmetic=collections.Counter(c['command'][1] for c in calls if c['role']==role and c['command'][1] in ['host-learn','host-infer'])
  assert arithmetic=={'host-learn':40,'host-infer':4}
 events=[json.loads(x) for x in gzip.decompress((reports/'events.jsonl.gz').read_bytes()).splitlines()]
 assert len(events)==46 and [e['reply']['envelope'] for e in events[:44]]==envelopes
 for e,index in zip(events[-2:],[0,10],strict=True):assert e['reply']['status']=='replayed' and e['reply']['envelope']==envelopes[index]
 for call in calls:
  if call['role'] in ['host','authority','reader','public_transport','independent_public_replay']:
   assert call['command'][1] in ['inspect','host-learn','host-infer'] and not {'--sk','--vector'}.intersection(call['command'])
 report=load(reports/'report.json');public=load(reports/'public_complete.json')
 assert report['ok'] and report['all_private_integer_comparisons_match'] and report['private_integer_comparisons']==4
 assert report['public_complete_sha256']==rawsha((reports/'public_complete.json').read_bytes())
 assert report['genesis_sha256']==public['genesis_sha256']==digest(g) and public['all_public_workers_and_services_closed']
 assert public['all_public_replay_and_operations_before_private_drain'] and public['private_answer_db_absent_through_public_checks']
 result={'schema':'public-coin-journal-saved-public-seal-v1','ok':True,'genesis_sha256':digest(g),'context_id':g['context_id'],'source_pins_checked':len(pins['source_files_sha256']),'failed_attempt_source_pins_checked':len(oldpins['source_files_sha256']),'failed_attempt_stopped_before_registration':True,'unchanged_origin_files_checked':len(origins),'signature_dependency_files_checked':len(pins['signature_dependency']['files_sha256']),'registration_signatures_checked':16,'authority_envelope_signatures_checked':44,'issuer_or_command_signatures_checked':44,'ordered_events':44,'learns':40,'infers':4,'exact_fifo_expiries':8,'authorized_historical_retries':2,'public_command_count':len(calls),'public_command_counts':dict(collections.Counter(names)),'saved_full_arithmetic_replay_status':True,'group_arithmetic_rerun':False,'RPC_or_services_started':False,'private_files_read_or_hashed':0,'private_comparisons':'attributed to pinned executed report; not independently opened','phase_order':'source and saved public-complete/report fields checked; no timing leakage theorem','seal_source_sha256':rawsha(Path(__file__).read_bytes())}
 write(reports/'seal.json',result)
 # Exclude ignored runtime, bytecode and the manifest itself. Source snapshots
 # contain public code only and preserve the first failed attempt's exact pins.
 paths=[]
 for directory,subdirs,names in os.walk(HERE):
  subdirs[:]=[n for n in subdirs if n not in ['runtime','__pycache__']]
  for name in names:
   p=Path(directory)/name
   if p.suffix!='.pyc' and p.name!='FINAL_MANIFEST.json':paths.append(p)
 manifest={'schema':'public-coin-journal-final-public-manifest-v1','scope':'public code/reports only; no private runtime material','files':{str(p.relative_to(HERE)):{'sha256':rawsha(p.read_bytes()),'bytes':p.stat().st_size} for p in sorted(paths)}}
 write(HERE/'FINAL_MANIFEST.json',manifest);print(json.dumps(result,sort_keys=True))
if __name__=='__main__':main()
