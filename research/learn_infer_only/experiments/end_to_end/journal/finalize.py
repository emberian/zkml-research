"""Foldable public validation/cost index; reads no plaintext oracle or secret key."""
import json,tarfile
from common import *
HERE=Path(__file__).resolve().parent

def record(path):
 p=HERE/path;return {'path':path,'sha256':sha(p.read_bytes()),'bytes':p.stat().st_size}
def main():
 paths={'utility':'results/utility_002/report.json','private':'results/private_002/report.json','controls':'results/controls_002/report.json','live_text':'results/live_text_002/report.json','signer_route':'results/signer_route_001/report.json'}
 reports={k:read_json(HERE/v) for k,v in paths.items()};require(all(x['ok'] for x in reports.values()),'finalReportNotGreen')
 sources={p.name:sha(p.read_bytes()) for p in sorted(HERE.glob('*.py'))};write_json(HERE/'source_manifest.json',sources)
 core=['common.py','model.py','roles.py','authority.py','reader.py'];pins=[]
 for gpath in [HERE/'results/utility_002/history_0/genesis.json',HERE/'results/utility_002/history_1/genesis.json',HERE/'results/private_002/genesis.json',HERE/'results/live_text_002/genesis.json']:
  g=read_json(gpath);require(g['journal_sources']=={k:sources[k] for k in core},'executedCoreChanged');pins.append({'path':str(gpath.relative_to(HERE)),'genesis':digest(g)})
 archive=HERE/'results/source_snapshots/repaired_core.tar.gz'
 with tarfile.open(archive,'w:gz') as out:
  for p in sorted(HERE.glob('*.py')):out.add(p,arcname=p.name)
 write_json(HERE/'results/source_snapshots/repaired_core.json',sources)
 utility=reports['utility'];private=reports['private'];controls=reports['controls']['cases'];live=reports['live_text'];route=reports['signer_route']
 costs=[]
 for history in utility['histories']:
  h=history['history'];head=read_json(HERE/f'results/utility_002/history_{h}/replay.json')['head'];refs=set()
  for row in head['state']['routes'].values():refs.add(row['acc_ct']);refs.update(e['ct_sha256'] for e in row['queue'])
  cas=HERE/f'results/utility_002/history_{h}/authority/cas'
  costs.append({'history':h,'events':history['events'],'elapsed_ns_including_full_replay_and_role_orchestration':history['elapsed_ns'],
   'exact_current_state_ciphertexts':len(refs),'exact_current_state_ciphertext_bytes':sum((cas/x).stat().st_size for x in refs),
   'retained_genesis_zero_bytes_separate':85103,'storage_snapshot':history['storage'],'command_census':history['commands']})
 review=HERE.parent.parent/'adversarial_review/end_to_end/journal_repair_review_001.json'
 result={'schema':'resident-journal-validation-v1','claim_label':'EXECUTED; research fixture, no implementation-refinement or succinct-proof claim','ok':True,
  'credential_tier':'R: trusted full-key reader, honest issuer, query authorizer and baseline validating authority; Ed25519 authentication is classical',
  'utility':{'events':utility['events'],'learns':sum(x['learns'] for x in utility['histories']),'infers':utility['oracle_comparisons'],'expiries':sum(x['expiries'] for x in utility['histories']),
   'oracle_all_match':utility['all_oracle_matches'],'nonempty_outputs':sum(x['nonempty_encrypted_outputs'] for x in utility['histories']),'known_empty_route_outputs':sum(x['known_empty_route_outputs'] for x in utility['histories'])},
  'private_ingress':{k:private[k] for k in ['learns','infers','expiries','oracle_comparisons','oracle_all_match','private_input_mode_0600']},
  'live_text':{k:live[k] for k in ['learns','infers','oracle_comparisons','oracle_all_match','live_text_encoder_executed','output_changed_after_learning']},
  'controls':{'mutation_refusals':len(controls['mutations']['refusals']),'actual_SIGKILL_boundaries':[k for k in ['before_reservation','after_commit','after_publication'] if controls[k]['process_exit']==-9],
   'same_parent_authority_workers':len(controls['race']['authority_pids']),'pending_retry_clients':controls['pending_retries']['client_processes'],'pending_retry_reader_decryptions':controls['pending_retries']['reader_decrypt_calls'],
   'authority_rollback_distinct_successors':controls['authority_rollback']['distinct_actual_state_digests'],'signer_routed_unselected_coordinate':route['actual_bfv_routed_other_coordinate'],'signer_scope':route['scope']},
  'costs':costs,'report_artifacts':{k:record(v) for k,v in paths.items()},'executed_genesis_pins':pins,'source_sha256':sources,
  'independent_review':{'path':str(review),'sha256':sha(review.read_bytes())},'repaired_source_archive':record('results/source_snapshots/repaired_core.tar.gz'),
  'residuals':['NoMasterRead absent: reader full key persists.','Baseline authority signer can substitute output through an available independent query ticket; verified-reader successor is separate.',
   'Single issuer/test oracle knows its complete deterministic observation history.','Ciphertext key/range/feature provenance rests on honest authorized issuance.','No OS separation, remote attestation, physical durability or Rust/SQLite-to-Lean refinement theorem.',
   'Current window is bounded; retained ciphertext blobs and journal grow with history.','Query authorization is a disclosure policy, not an interface privacy theorem.']}
 write_json(HERE/'validation.json',result);print(json.dumps({'ok':True,'utility':result['utility'],'private_ingress':result['private_ingress'],'live_text':result['live_text']}))
if __name__=='__main__':main()
