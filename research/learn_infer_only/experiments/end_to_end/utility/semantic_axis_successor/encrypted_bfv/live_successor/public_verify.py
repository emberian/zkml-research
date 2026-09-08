"""Separate public replay/storage audit; no private config/key/input/answer read."""
import hashlib,json,os,sqlite3,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_bytes())
def file_sha(p):
 h=hashlib.sha256()
 with Path(p).open('rb') as f:
  while raw:=f.read(1024*1024):h.update(raw)
 return h.hexdigest()
def dump(p,x):Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def main():
 start=time.perf_counter_ns();freeze=load(ROOT/'freeze.json');runtime=Path(freeze['runtime']);reports=Path(freeze['reports']);run=runtime/'run';snap=runtime/'e2e'
 target=reports/'public_verification.json';assert not target.exists()
 for p,h in freeze['public_source_dependencies'].items():assert file_sha(p)==h,p
 for p,h in freeze['snapshot_source_pins'].items():assert file_sha(snap/p)==h,p
 phase=load(reports/'public_phase.json');assert phase['ok'] and phase['all_services_closed'] and phase['reader_decryptions']==0
 for row in phase['services']:
  try:os.kill(row['pid'],0)
  except ProcessLookupError:continue
  raise AssertionError('Previously recorded service PID is still live')
 sys.path.insert(0,str(snap/'journal'))
 from model import CAS,Crypto,initial_state,check_request,transition,apply_delta,validate_state,verify,digest
 g=load(run/'genesis.json');cfg=load(run/'host_config.json')
 assert set(cfg)=={'crypto_binary','crypto_binary_sha256','genesis_path','genesis_sha256','command_log'}
 assert file_sha(cfg['crypto_binary'])==cfg['crypto_binary_sha256']==freeze['snapshot_source_pins']['resident-crypto']
 assert digest(g)==cfg['genesis_sha256']
 cas=CAS(runtime/'independent_public_cas',g,Crypto(cfg,'independent_public_verifier',reports/'independent_public_commands.jsonl'))
 query_hashes={x['query_ct'] for x in g['query_policy']}
 input_pins={}
 for p in sorted((run/'host_cas').iterdir()):
  assert p.is_file() and len(p.name)==64 and file_sha(p)==p.name
  input_pins[str(p.relative_to(run))]=file_sha(p);cas.import_file(p,'query' if p.name in query_hashes else 'ct')
 envelopes=load(reports/'accepted_envelopes.json');assert len(envelopes)==3
 state=initial_state(g);ids=set();nonces=set();records=set()
 for revision,envelope in enumerate(envelopes,1):
  payload=verify(envelope,g['authority_vk'],'resident-authority-finalization-v1');request=payload['request'];a=request['action']
  assert a['kind']==['Infer','Learn','Infer'][revision-1] and a['route']==0
  check_request(request,g,cas)
  assert payload['revision']==revision and a['parent_revision']==revision-1
  assert payload['request_sha256']==digest(request) and payload['parent_state']==a['parent_state']==digest(state)
  assert a['request_id'] not in ids and a['nonce'] not in nonces;ids.add(a['request_id']);nonces.add(a['nonce'])
  if a['kind']=='Learn':assert a['record_id'] not in records;records.add(a['record_id'])
  else:assert a['query_ct']==file_sha(run/'queries/q01.json')
  computed,delta,proposal=transition(state,a,g,cas)
  assert delta==payload['delta'] and proposal==request['proposal']
  assert payload['output_ct']==(proposal['result_ct'] if a['kind']=='Infer' else None)
  state=apply_delta(state,delta,g);assert computed==state and validate_state(state,g,cas)==payload['next_state']==proposal['next_state']
 with sqlite3.connect(f'file:{run / "authority/journal.sqlite3"}?mode=ro',uri=True) as db:
  stored=[json.loads(r[0]) for r in db.execute('SELECT envelope FROM journal ORDER BY revision')]
  head=db.execute('SELECT revision,state,state_digest FROM meta').fetchone()
  pending=db.execute("SELECT count(*) FROM journal WHERE published=0 AND json_extract(request,'$.action.kind')='Infer'").fetchone()[0]
 assert stored==envelopes and head[0]==3 and json.loads(head[1])==state and head[2]==digest(state) and pending==2
 with sqlite3.connect(f'file:{run / "verified_state.sqlite3"}?mode=ro',uri=True) as db:
  stored=[json.loads(r[0]) for r in db.execute('SELECT envelope FROM verified_journal ORDER BY revision')]
  head=db.execute('SELECT revision,state,state_digest FROM verified_head').fetchone()
  selected=db.execute('SELECT count(*) FROM expected').fetchone()[0]
  received=db.execute('SELECT count(*) FROM received').fetchone()[0]
 assert stored==envelopes and head[0]==3 and json.loads(head[1])==state and head[2]==digest(state) and selected==2 and received==0
 assert load(reports/'public_storage.json')=={'verified_journal':envelopes,'verified_state':state,'verified_records':3,'registered_tickets':2,'received':0}
 cas_sets={}
 for name in ['host_cas','authority/cas','verified_cas']:
  files={p.name:file_sha(p) for p in (run/name).iterdir() if p.is_file()}
  assert all(n==h for n,h in files.items());cas_sets[name]=files
  for r in state['routes'].values():assert r['acc_ct'] in files
  for envelope in envelopes:
   output=envelope['payload']['output_ct']
   if output:assert output in files
 for name in ['commands.jsonl','verified_commands.jsonl']:
  rows=[json.loads(x) for x in (run/name).read_bytes().splitlines()]
  assert all(x['exit_code']==0 and x['command'][1]!='reader-decrypt' for x in rows)
 for p,h in input_pins.items():assert file_sha(run/p)==h
 for p,h in freeze['public_source_dependencies'].items():assert file_sha(p)==h,p
 model_pins={n:file_sha(Path(freeze['model_path'])/n) for n in freeze['model_files']}
 assert all(model_pins[n]==row['sha256'] for n,row in freeze['model_files'].items())
 result={'ok':True,'events':3,'independent_arithmetic_transitions':3,'durable_journals_equal':True,
         'registered_tickets':2,'received_before_private_phase':0,'authority_pending_infers':2,
         'all_service_pids_absent':True,'private_files_read':False,'private_decryptions':0,
         'freeze_sha256':file_sha(ROOT/'freeze.json'),'public_phase_sha256':file_sha(reports/'public_phase.json'),
         'accepted_envelopes_sha256':file_sha(reports/'accepted_envelopes.json'),
         'public_cas_files':cas_sets,'public_input_pins_before_after':input_pins,
         'model_files_after_public_phase':model_pins,'model_bytes_unchanged_before_private_drain':True,
         'final_state_digest':digest(state),'elapsed_ns':time.perf_counter_ns()-start,
         'verifier_sha256':file_sha(__file__)}
 dump(target,result);print(json.dumps({'ok':True,'events':3,'private_decryptions':0,'public_verification_sha256':file_sha(target)}))
if __name__=='__main__':main()
