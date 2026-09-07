#!/usr/bin/env python3
"""Export public ciphertext/protocol evidence and aggregate trusted comparisons.

Never copies .private files or prints/hashes private vectors, keys or scores.
This output is a research artifact; its oracle comparison bit is outside the
cryptographic host-view claim.
"""
from pathlib import Path
import argparse,collections,hashlib,json,shutil,sqlite3,sys
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'source/journal'))
from common import read_json,write_json,sha,canonical,require
from public_log_audit import check_public_logs

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--out',required=True);a=p.parse_args()
 root=Path(a.root).resolve();out=Path(a.out).resolve();out.mkdir(parents=True,exist_ok=False)
 report=read_json(root/'report.json');require(report['ok'] is True,'completedNormalRun')
 genesis=read_json(root/'genesis.json')
 for name,expected in genesis['journal_sources'].items():require(sha((HERE/'source/journal'/name).read_bytes())==expected,'executedJournalSourcePin:'+name)
 for name,expected in genesis['crypto_sources'].items():require(sha((HERE/'source/crypto'/name).read_bytes())==expected,'executedCryptoSourcePin:'+name)
 native=genesis['native_dependency'];require(sha(Path(native['path']).read_bytes())==native['sha256'],'executedNativePin')
 check_public_logs(root)
 names=['public_log_audit.json','report.json','genesis.json','context_validation.json','public_context.json','checkpoint.json','progress.json','replay.json','commands.jsonl','role_calls.jsonl','events.jsonl','server_processes.jsonl','reader-server.jsonl','authority-server.jsonl']
 for name in names:
  path=root/name
  if path.exists():shutil.copy2(path,out/name)
 queryout=out/'queries';queryout.mkdir()
 for path in sorted((root/'queries').glob('*.json')):shutil.copy2(path,queryout/path.name)
 # Private inventory exposes only counts/lengths, never private file hashes.
 private=root/'.private';keys=list((private/'reader/recipient_keys').glob('*.key'))
 remains=list(private.rglob('*.delivery'))+list(private.rglob('*.pending'))+list(private.rglob('.designated-setup-*'))
 require(len(keys)==16 and all(p.stat().st_size==435 for p in keys),'retainedDedicatedKeyInventory')
 require(not remains,'transientSetupInventory')
 rcfg=read_json(private/'reader/config.json')
 secretfields=[k for k in rcfg if any(term in k for term in ['recipient_key','secret','private_db','private_cost'])]
 require(not secretfields,'publicServiceConfigHasNoRecipientMaterial')
 with sqlite3.connect(rcfg['db']) as db:
  publictables={r[0] for r in db.execute("SELECT name FROM sqlite_master WHERE type='table'")}
  require('private_decodes' not in publictables,'privateDecodeTableSeparate')
  accepted_count=db.execute('SELECT count(*) FROM received').fetchone()[0]
  columns=[r[1] for r in db.execute('PRAGMA table_info(received)')]
  require('answer' not in columns and 'envelope' in columns,'acceptedCiphertextOnlySchema')
 privatecfg=read_json(private/'reader/drain_config.json')
 require(Path(privatecfg['private_db']).resolve()!=Path(rcfg['db']).resolve(),'separateAnswerPersistence')
 with sqlite3.connect(privatecfg['private_db']) as db:
  privatecount,decodecount=db.execute('SELECT count(*),sum(decode_count) FROM private_decodes').fetchone()
 calls=[json.loads(line) for line in (root/'commands.jsonl').read_text().splitlines()]
 durations=collections.defaultdict(list);counter=collections.Counter();modes=collections.Counter();failures=[]
 keygen=None
 for call in calls:
  command=call['command'][1]
  require(command!='reader-decrypt' and call['private_output_omitted'] is False,'publicCommandDomain')
  if call['exit_code']:failures.append({'command':command,'exit_code':call['exit_code']})
  payload=json.loads(call['stdout']);durations[(call['role'],command)].append(call['elapsed_ns'])
  counter.update(payload.get('counts',{}))
  if command=='keygen':keygen=payload
 require(not failures,'publicCLIAllSuccess')
 require(keygen is not None and keygen['master_serialized'] is False and keygen['projection_delivery_files_remaining']==0 and keygen['private_pending_files_remaining']==0,'reportedSetupLifecycle')
 inventory={'inventory_scope':'Only this run .private tree; Path.rglob for delivery/pending/setup names plus source-reported never-serialized master. No assertion about memory, backups, physical disk remnants or unobserved copies.',
  'retained_recipient_key_files':16,'recipient_key_bytes_each':435,'retained_recipient_key_bytes_total':sum(p.stat().st_size for p in keys),
  'retained_projection_delivery_files':0,'retained_pending_scalar_files':0,'retained_setup_directories':0,
  'initializer_reports_master_never_serialized':True,'physical_erasure_proved':False,
  'public_service_config_private_credential_fields':secretfields,'public_acceptance_schema_columns':columns,
  'public_accepted_ciphertexts':accepted_count,'private_answer_records':privatecount,'private_stored_decode_count':decodecount,
  'public_and_private_db_paths_distinct':True,'private_vectors_preserved_outside_export':len(list((private/'oracle').glob('input-*.json'))),
  'private_file_hashes_exported':False,'private_decode_costs_exported':False,'host_view_excludes_this_trusted_research_inventory':True}
 write_json(out/'CREDENTIAL_INVENTORY.json',inventory)
 sizes={}
 for name in ['host_cas','authority/cas','reader/cas']:
  fs=[p for p in (root/name).iterdir() if p.is_file() and len(p.name)==64]
  sizes[name]={'objects':len(fs),'bytes':sum(p.stat().st_size for p in fs)}
 childcounts=collections.Counter()
 for phase in keygen['phases']:childcounts.update(phase.get('counts',{}))
 totalcounts=counter+childcounts
 costs={'scope':'public CLI only, including setup; excludes private drain and private oracle; overlapping categories are not summed as wall time',
  'public_cli_calls':len(calls),'crypto_processes_including_setup_children':len(calls)+len(keygen['phases']),
  'top_level_cli_native_counts':dict(counter),'setup_child_native_counts':dict(childcounts),'public_total_native_counts_including_setup_children':dict(totalcounts),
  'role_commands':[{'role':role,'command':command,'count':len(xs),'total_ns':sum(xs),'min_ns':min(xs),'max_ns':max(xs)} for (role,command),xs in sorted(durations.items())],
  'public_event_phase_elapsed_ns':report['public_event_phase_elapsed_ns'],'public_progress_after_40_learn_4_infer_ns':report.get('public_progress_after_40_learn_4_infer_ns'),'cas_storage':sizes,
  'context_bytes':(root/'public_context.json').stat().st_size,'state_bytes':148147,'recipient_output_bytes':691,
  'initializer_subprocess_phases':keygen['phases'],'private_decode_timing_omitted':True}
 write_json(out/'PUBLIC_COSTS.json',costs)
 manifest={'schema':'designated-integration-evidence-v1','files_sha256':{str(p.relative_to(out)):sha(p.read_bytes()) for p in sorted(out.rglob('*')) if p.is_file()},
  'source_sha256':{str(p.relative_to(HERE)):sha(p.read_bytes()) for p in sorted((HERE/'source').rglob('*')) if p.is_file() and '__pycache__' not in p.parts},
  'executed_first_driver_sha256':read_json(HERE/'HARNESS_ORIGINAL.json')['sha256'],'current_driver_sha256':sha((HERE/'normal_flow.py').read_bytes()),
  'finalizer_sha256':sha((HERE/'finalize_normal_001.py').read_bytes()),'public_log_audit_sha256':sha((HERE/'public_log_audit.py').read_bytes()),'exporter_sha256':sha(Path(__file__).read_bytes()),
  'no_private_files_or_hashes_copied':True,'trusted_oracle_comparison_outside_host_view':True}
 write_json(out/'MANIFEST.json',manifest)
 print(json.dumps({'ok':True,'exported_files':len(manifest['files_sha256']),'manifest_sha256':sha((out/'MANIFEST.json').read_bytes()),'public_cli_calls':len(calls),'private_key_count':16}))
if __name__=='__main__':main()
