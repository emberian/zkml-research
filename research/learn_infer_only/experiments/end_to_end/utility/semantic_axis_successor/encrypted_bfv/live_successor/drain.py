"""Offline full-key receive and private integer audit after public closure."""
import gzip,hashlib,json,os,sqlite3,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent
load=lambda p:json.loads(Path(p).read_bytes())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,x,private=False):
 Path(p).write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
 if private:os.chmod(p,0o600)
def main():
 started=time.perf_counter_ns();freeze=load(ROOT/'freeze.json');runtime=Path(freeze['runtime']);reports=Path(freeze['reports']);run=runtime/'run';snap=runtime/'e2e'
 marker=runtime/'.private/drain_started.json';assert not marker.exists()
 for p,h in freeze['public_source_dependencies'].items():assert sha(p)==h,p
 for p,h in freeze['snapshot_source_pins'].items():assert sha(snap/p)==h,p
 gate_path=reports/'public_verification.json';gate_hash=sha(gate_path);gate=load(gate_path)
 assert gate['ok'] and gate['private_decryptions']==0 and gate['received_before_private_phase']==0
 assert gate['freeze_sha256']==sha(ROOT/'freeze.json') and gate['public_phase_sha256']==sha(reports/'public_phase.json')
 assert gate['accepted_envelopes_sha256']==sha(reports/'accepted_envelopes.json')
 phase=load(reports/'public_phase.json');assert phase['all_services_closed']
 for row in phase['services']:
  try:os.kill(row['pid'],0)
  except ProcessLookupError:continue
  raise AssertionError('Public service is still live')
 dump(marker,{'public_verification_sha256':gate_hash,'attempt':1},True)
 sys.path.insert(0,str(snap/'verified_reader'))
 from service import VerifiedReader
 cfg=load(run/'.private/verified_reader/config.json');reader=VerifiedReader(cfg)
 with sqlite3.connect(cfg['db']) as db:assert db.execute('SELECT count(*) FROM received').fetchone()[0]==0
 before_log=(run/'verified_commands.jsonl').read_bytes()
 receipts=[];envelopes=load(reports/'accepted_envelopes.json')
 for envelope in envelopes:
  payload=envelope['payload']
  if payload['request']['action']['kind']!='Infer':continue
  output=payload['output_ct'];raw=(run/'verified_cas'/output).read_bytes();assert hashlib.sha256(raw).hexdigest()==output
  receipt=reader.receive(envelope,raw);assert receipt['ok'] and receipt['status']=='received';receipts.append(receipt)
 with sqlite3.connect(cfg['db']) as db:
  answers={rid:json.loads(raw)['signed_score'] for rid,raw in db.execute('SELECT request_id,answer FROM received')}
  journal=[json.loads(r[0]) for r in db.execute('SELECT envelope FROM verified_journal ORDER BY revision')]
 assert journal==envelopes and len(receipts)==2
 private_work=run/'.private/issuer/live_encoder';vector=load(private_work/'vector.json')
 query=load(run/'queries/q01.json')['coefficients'];rawscores=load(private_work/'raw_scores.json')
 data=load(runtime/'.private/input.json');assert data['route']==0 and data['label']==1
 assert len(rawscores)==2 and [r['axis'] for r in rawscores]==['a','b']
 for row in rawscores:
  logits=row['logits_in_bit_order'];assert len(logits)==2
  assert row['predicted_bit']==(0 if logits[0]>=logits[1] else 1)
  assert row['exact_tie']==(logits[0]==logits[1])
 expected_vector=[0]*577;expected_vector[2*rawscores[0]['predicted_bit']+rawscores[1]['predicted_bit']]=127
 assert vector==expected_vector and query==[127]+[0]*576
 exact=sum(v*q for v,q in zip(vector,query))
 expected={'before-live-observation':0,'after-live-observation':exact};assert answers==expected
 score=load(private_work/'score_results.json')
 assert score['execution_completed'] and score['score_attempts']==score['actual_model_forward_calls']==1
 assert score['actual_forward_examples']==2 and score['generated_tokens']==score['weight_updates']==0
 after_log=(run/'verified_commands.jsonl').read_bytes();assert after_log.startswith(before_log)
 added=after_log[len(before_log):];rows=[json.loads(x) for x in added.splitlines()]
 decrypts=[r for r in rows if r['command'][1]=='reader-decrypt']
 assert len(decrypts)==2 and all(r['exit_code']==0 and r['stdout'] is None and r['stderr'] is None and r['private_output_omitted'] for r in decrypts)
 assert all(r['command'][1] in ['inspect','reader-decrypt'] for r in rows)
 assert not any(json.loads(x)['command'][1]=='reader-decrypt' for x in (run/'commands.jsonl').read_bytes().splitlines())
 with sqlite3.connect(run/'.private/reader/answers.sqlite3') as db:assert db.execute('SELECT count(*) FROM received').fetchone()[0]==0
 assert sha(gate_path)==gate_hash
 dump(runtime/'.private/integer_audit.json',{'expected':expected,'answers':answers,'vector':vector,'raw_scores':rawscores,
      'public_verification_sha256':gate_hash,'all_match':True},True)
 with gzip.open(reports/'private_receive_commands.jsonl.gz','wb') as f:f.write(added)
 cost_fields=['cpu_load_wall_seconds','cpu_load_process_cpu_seconds','transfer_to_mps_wall_seconds',
              'forward_wall_seconds','forward_process_cpu_seconds','likelihood_and_transfer_wall_seconds',
              'total_wall_seconds_including_imports','total_process_cpu_seconds_including_imports',
              'memory_before_load','memory_after_load','memory_at_end','runtime','settings','model_parameter_count']
 report={'ok':True,'learns':1,'infers':2,'events':3,'expiries':0,'actual_model_forward_calls':1,
         'actual_axis_examples':2,'generated_tokens':0,'weight_updates':0,'cached_feature_substitution':False,
         'oracle_comparisons':2,'all_oracle_matches':True,'output_changed_after_learning':exact!=0,
         'output_change_discloses_selected_score_under_fixed_mapping':True,
         'verified_decryptions_after_public_verification':2,'baseline_decryptions':0,
         'public_phase_decryptions':0,'public_services_remained_closed':True,
         'public_verification_sha256':gate_hash,'offline_receive_receipts':receipts,
         'same_durable_verified_journal':True,'authority_outbox_still_pending':True,
         'model_cost':{k:score[k] for k in cost_fields},'private_receive_and_audit_wall_ns':time.perf_counter_ns()-started,
         'scope':'One fixed fresh text illustration, no accuracy estimate. Plaintext trusted issuer, full BFV reader key, public routes, rank4 per route, same-account roles; no no-master-read or end-to-end PQ claim.'}
 dump(reports/'report.json',report)
 print(json.dumps({'ok':True,'all_oracle_matches':True,'verified_decryptions_after_public_verification':2,
                   'output_changed_after_learning':exact!=0}))
if __name__=='__main__':main()
