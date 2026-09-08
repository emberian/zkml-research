#!/usr/bin/env python3
"""Normal33/4/1; public worker closes before separately gated private scalar drain."""
from pathlib import Path
import argparse,collections,gzip,hashlib,importlib.metadata,importlib.util,json,os,platform,select,sqlite3,subprocess,sys,time
HERE=Path(__file__).resolve().parent
SOURCE=HERE/'source'
sys.dont_write_bytecode=True
sys.path.insert(0,str(SOURCE/'journal'));sys.path.insert(0,str(SOURCE))
from run import Run
from common import CAS,Crypto,canonical,digest,read_json,require,rpc,sha,write_json
from public_log_audit import check_public_logs
from setup_join import setup,verify_binding,verify_dependencies
WRAPPERS=['driver.py','setup_join.py','private_oracle.py','public_close.py','launch.py','CONTRACT.md','SOURCE_PINS.json','WRAPPER_ORIGINS.json']

def file_sha(path):return sha(Path(path).read_bytes())
def prepare(reports):
 reports.mkdir(parents=True,exist_ok=False)
 immutable=verify_dependencies()
 files={name:item['sha256'] for name,item in immutable['files'].items()}
 files.update({name:file_sha(HERE/name) for name in WRAPPERS})
 native=Path('/opt/homebrew/opt/openssl@3/lib/libcrypto.3.dylib').resolve();interpreter=Path(sys.executable).resolve()
 signature={};dist=importlib.metadata.distribution('cryptography')
 for directory in importlib.util.find_spec('cryptography').submodule_search_locations or []:
  for p in Path(directory).rglob('*'):
   if p.is_file() and p.suffix in ['.py','.so','.dylib']:signature[str(p.resolve())]=file_sha(p)
 require(signature and any(Path(p).suffix=='.so' for p in signature),'nonemptySignaturePins')
 pins={'schema':'public-seed-journal-execution-pins-v1','source_files_sha256':files,'native_dependency':{'path':str(native),'sha256':file_sha(native)},'interpreter':{'path':str(interpreter),'sha256':file_sha(interpreter),'version':sys.version},'signature_dependency':{'version':dist.version,'files_sha256':signature},'platform':platform.platform(),'normal_workload':{'learns':33,'infers':4,'expiries':1,'finalized_events':37,'reopen_revision':18,'historical_infer_retries':1},'prepared_only':True}
 write_json(reports/'execution_pins.json',pins)
 print(json.dumps({'prepared':True,'source_files':len(files),'signature_files':len(signature),'crypto_commands':0,'services':0}),flush=True)

def check_pins(reports):
 verify_dependencies()
 pins=read_json(reports/'execution_pins.json')
 for name,h in pins['source_files_sha256'].items():require(file_sha(HERE/name)==h,'sourcePin:'+name)
 for kind in ['native_dependency','interpreter']:require(file_sha(pins[kind]['path'])==pins[kind]['sha256'],'environmentPin:'+kind)
 for name,h in pins['signature_dependency']['files_sha256'].items():require(file_sha(name)==h,'signaturePin:'+name)
 return pins

class PublicRun(Run):
 def __init__(self,root):
  self.root=root;self.processes=[];self.events=[];self.calls=[];self.started=time.perf_counter_ns();self.worker=None;self.worker_events=[];self.worker_report=None
  # The parent Run constructor invokes legacy roles.setup; deliberately initialize
  # only its transport fields here after the separate honest public ceremony.
  self.g=read_json(root/'genesis.json');self.acfg=read_json(root/'.private/authority/config.json');self.rcfg=read_json(root/'.private/reader/config.json');self.hcfg=read_json(root/'host_config.json')
  self.host_cas=CAS(root/'host_cas',self.g,Crypto(self.hcfg,'public_transport',root/'commands.jsonl'));self.work=root/'work';self.work.mkdir()
  try:
   self.host_cas.import_file(root/'zero.ct');self.reader=self.start('reader',root/'.private/reader/config.json');self.authority=self.start('authority',root/'.private/authority/config.json')
   self.upload(root/'zero.ct');self.upload(root/'zero.ct',address=self.rcfg['socket'])
   for q in sorted((root/'queries').glob('*.json')):self.host_cas.import_file(q,'query');self.upload(q,'query')
   self.worker_argv=[sys.executable,str(SOURCE/'host_runtime/host.py'),'serve','--config',str(root/'host_config.json'),'--cas',str(self.host_cas.root)]
   self.worker_log=(root/'host_worker.stderr').open('wb');self.worker_started=time.perf_counter_ns()
   self.worker=subprocess.Popen(self.worker_argv,stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=self.worker_log)
   require(select.select([self.worker.stdout],[],[],300)[0],'hostReadyTimeout');ready=json.loads(self.worker.stdout.readline())
   require(ready.get('ok') and ready.get('ready') and ready['context_id']==self.g['context_id'],'hostReadyIdentity')
   self.worker_startup_ns=time.perf_counter_ns()-self.worker_started
  except Exception:self.close();raise
 def role(self,command,**kwargs):
  if command!='propose':return super().role(command,**kwargs)
  require(set(kwargs)=={'config','head','authorization','cas','out'},'normalHostArguments')
  require(Path(kwargs['config'])==self.root/'host_config.json' and Path(kwargs['cas'])==self.host_cas.root,'fixedHostPaths')
  message={k:str(kwargs[k]) for k in ['head','authorization','out']};raw=canonical(message)+b'\n';started=time.perf_counter_ns()
  self.worker.stdin.write(raw);self.worker.stdin.flush();require(select.select([self.worker.stdout],[],[],300)[0],'hostResponseTimeout')
  line=self.worker.stdout.readline();reply=json.loads(line);elapsed=time.perf_counter_ns()-started
  require(reply.get('ok'),'normalHostReply');require(reply['request_stats']['cas_get_calls']==reply['request_stats']['full_blob_sha256_calls'],'everyHostGetHashed')
  action=read_json(kwargs['authorization'])['payload'];record={'event_id':action['request_id'],'kind':action['kind'],'caller_ns':elapsed,'inside_propose_ns':reply['elapsed_ns'],'request_bytes':len(raw),'response_bytes':len(line),'request_stats':reply['request_stats'],'cumulative_stats':reply['cumulative_stats'],'inspection_cache_entries':reply['inspection_cache_entries']}
  self.worker_events.append(record)
  with (self.root/'host_worker.jsonl').open('ab') as sink:sink.write(canonical(record)+b'\n')
  call={'role_process':'propose','transport':'persistent_public_stdio','worker_argv':self.worker_argv,'message':message,'elapsed_ns':elapsed,'exit_code':0,'stdout':canonical(reply['result']).decode(),'stderr':''};self.calls.append(call)
  with (self.root/'role_calls.jsonl').open('ab') as sink:sink.write(canonical(call)+b'\n')
  return reply['result']
 def reopen(self):
  before=self.head();verified=rpc(self.rcfg['socket'],{'op':'verified_status'});require(before['revision']==verified['revision']==18,'reopenRevision18')
  Run.close(self)
  self.reader=self.start('reader',self.root/'.private/reader/config.json');self.authority=self.start('authority',self.root/'.private/authority/config.json')
  require(self.head()==before and rpc(self.rcfg['socket'],{'op':'verified_status'})==verified,'orderlyReopenIdentity')
  return {'revision':18,'state_digest':before['state_digest'],'orderly_close_reopen':True,'exact_head_preserved':True}
 def close(self):
  if self.worker is not None:
   if self.worker.poll() is None:
    self.worker.stdin.close();self.worker.wait(timeout=30)
   rows=self.worker_events
   self.worker_report={'worker_processes':1,'worker_pid':self.worker.pid,'requests':len(rows),'startup_ns':getattr(self,'worker_startup_ns',None),'lifetime_including_idle_pipeline_and_shutdown_ns':time.perf_counter_ns()-self.worker_started,'clean_exit':self.worker.returncode==0,'stats':rows[-1]['cumulative_stats'] if rows else {},'inspection_cache_entries':rows[-1]['inspection_cache_entries'] if rows else 0,'proposal_caller_total_ns':sum(r['caller_ns'] for r in rows),'proposal_function_total_ns':sum(r['inside_propose_ns'] for r in rows),'stdio_request_bytes':sum(r['request_bytes'] for r in rows),'stdio_response_bytes':sum(r['response_bytes'] for r in rows)}
   self.worker_log.close();self.worker=None
  if hasattr(self,'acfg'):Run.close(self)

def private_call(root,entry,*flags):
 private=root/'.private/postprotocol';private.mkdir(mode=0o700,exist_ok=True)
 command=[sys.executable,str(entry),*map(str,flags)];start=time.perf_counter_ns();out=subprocess.run(command,capture_output=True,timeout=300)
 with (private/'calls.jsonl').open('ab') as sink:sink.write(canonical({'argv':command,'elapsed_ns':time.perf_counter_ns()-start,'exit_code':out.returncode,'stdout':out.stdout.decode(),'stderr':out.stderr.decode()})+b'\n')
 os.chmod(private/'calls.jsonl',0o600);require(out.returncode==0,'privateRoleFailed');return json.loads(out.stdout)

def public_run(root,reports):
 check_pins(reports);require(not root.exists() and not (reports/'launched.json').exists(),'freshNormalRunOnly')
 write_json(reports/'launched.json',{'execution_pins_sha256':file_sha(reports/'execution_pins.json'),'runtime':str(root),'normal_workload_only':True})
 phase='public';instance=None;started=time.perf_counter_ns()
 def progress(stage,**extra):
  obj={'phase':'public','stage':stage,'public_elapsed_ns':time.perf_counter_ns()-started,**extra};write_json(reports/'checkpoint.json',obj);print(json.dumps(obj),flush=True)
 try:
  setup_result=setup(root)
  # Plaintext fixture preparation performs no decode and has no public secret values.
  fixture=subprocess.run([sys.executable,str(HERE/'private_oracle.py'),'prepare','--root',str(root)],capture_output=True,timeout=30)
  require(fixture.returncode==0,'knownFixturePreparation')
  write_json(root/'.private/oracle/preparation_call.json',{'stdout':fixture.stdout.decode(),'stderr':fixture.stderr.decode(),'exit_code':fixture.returncode},True)
  instance=PublicRun(root);progress('setup_complete',genesis=digest(instance.g),context_id=instance.g['context_id'])
  requests=[];accepted=[];fresh=[];expiry=0;checkpoint=None
  for n in range(1,34):
   req=instance.prepare('Learn',0,f'learn-{n:02d}',vector=root/f'.private/oracle/input-{n:02d}.json');reply=instance.accepted(req)
   require(reply['status']=='accepted' and reply['delivery']['status']=='verified_not_a_release','normalLearnAcceptance')
   if n>32:require(req['proposal']['expired_ct']==fresh[n-33],'exactOriginalFIFOExpiry');expiry+=1
   else:require(req['proposal']['expired_ct'] is None,'noEarlyExpiry')
   fresh.append(req['action']['fresh_ct']);requests.append(req);accepted.append(reply['envelope'])
   if n in {1:0,16:1,32:2,33:3}:
    row={1:0,16:1,32:2,33:3}[n]
    req=instance.prepare('Infer',0,f'infer-{n:02d}',query_index=row);reply=instance.accepted(req)
    require(reply['status']=='accepted' and reply['delivery']['reader']['status']=='ciphertextAccepted','normalCiphertextAcceptance')
    requests.append(req);accepted.append(reply['envelope']);progress('events',learns=n,infers=row+1,expiries=expiry,revision=len(accepted))
   require(not (root/'.private/reader/answers.sqlite3').exists(),'noPrivateDrainDuringPublicOperations')
   if n==16:checkpoint=instance.reopen();write_json(root/'orderly_reopen.json',checkpoint);progress('orderly_reopen_complete',revision=18)
   elif n%4==0 and n not in [32]:progress('events',learns=n,infers=sum(k<=n for k in [1,16,32,33]),expiries=expiry,revision=len(accepted))
  head=instance.head();status=rpc(instance.rcfg['socket'],{'op':'status'});verified=rpc(instance.rcfg['socket'],{'op':'verified_status'})
  require(head['revision']==verified['revision']==37 and status['received']==status['selected']==4,'publicEventCounts')
  retries=[]
  for req in [next(r for r in requests if r['action']['kind']=='Infer')]:
   reply=instance.accepted(req);original=next(e for e in accepted if e['payload']['request']['action']['request_id']==req['action']['request_id'])
   require(reply['status']=='replayed' and reply['envelope']==original,'authorizedHistoricalExactRetry')
   if req['action']['kind']=='Infer':require(reply['delivery']['reader']['status']=='replayed','acceptorRetryDedup')
   retries.append(req['action']['request_id'])
  require(instance.head()==head and rpc(instance.rcfg['socket'],{'op':'status'})==status and rpc(instance.rcfg['socket'],{'op':'verified_status'})==verified,'historicalRetriesPreserveHeadAndSelection')
  with sqlite3.connect(instance.rcfg['db']) as db:
   vstate=json.loads(db.execute('SELECT state FROM verified_head').fetchone()[0]);history=[json.loads(r[0]) for r in db.execute('SELECT envelope FROM verified_journal ORDER BY revision')]
   require('answer' not in [r[1] for r in db.execute('PRAGMA table_info(received)')],'acceptorHasNoAnswerColumn')
  require(history==accepted and vstate==head['state'] and digest(vstate)==verified['state_digest'],'exactIndependentHistoryAndHead')
  require([e['ct_sha256'] for e in vstate['routes']['0']['queue']]==fresh[1:],'exactFinalOriginalQueue')
  progress('full_public_replay_started',revision=37)
  replay_start=time.perf_counter_ns();replay=instance.replay(True);replay_ns=time.perf_counter_ns()-replay_start
  require(replay['revision']==37 and replay['state_digest']==verified['state_digest'] and replay['admissions']=={'0':33,'1':0} and replay['queue_lengths']=={'0':32,'1':0},'completePublicArithmeticReplay')
  final_argv=[sys.executable,str(SOURCE/'seed_setup/seed_setup.py'),'verify-public','--registry',str(root/'registry.json'),'--registry-sha256',digest(read_json(root/'registry.json')),'--context',str(root/'public_context.json'),'--transcript',str(root/'public_transcript.json')]
  final_setup=subprocess.run(final_argv,capture_output=True,timeout=300)
  require(final_setup.returncode==0,'finalCompleteSeedReplay');write_json(root/'final_seed_replay.json',{'argv':final_argv,'exit_code':final_setup.returncode,'stdout':final_setup.stdout.decode(),'stderr':final_setup.stderr.decode()})
  require(json.loads(final_setup.stdout)['complete_raw_hash_tape_match'] and json.loads(final_setup.stdout)['complete_context_byte_match'],'finalRawTapeAndContextMatch')
  binding=verify_binding(root);check_pins(reports)
  require(not (root/'.private/reader/answers.sqlite3').exists(),'fullPublicReplayBeforePrivateDecode')
  audit=check_public_logs(root);write_json(root/'public_log_audit.json',audit)
  calls=[json.loads(line) for line in (root/'commands.jsonl').read_bytes().splitlines()];commands=[c['command'][1] for c in calls]
  require(not {'keygen','initializer','recipient-register','reader-decrypt'}.intersection(commands),'noDealerOrPrivateDecodeInPublicPath')
  setup_commands=[c['command'][1] for c in calls if c['role']=='honest_public_setup']
  require(setup_commands==['auth-init']+['recipient-init']*16+['public-build','verify-public'],'registrationBeforePublicSampling')
  costs=collections.defaultdict(list);counts=collections.Counter();host_calls=collections.Counter();cache={}
  for call in calls:
   command=call['command'][1];payload=json.loads(call['stdout']);require(call['exit_code']==0 and not call['private_output_omitted'],'successfulPublicCalls')
   costs[(call['role'],command)].append(call['elapsed_ns']);counts.update(payload.get('counts',{}))
   if call['role'] in ['host','authority','reader','public_transport','independent_public_replay']:
    require(command in ['inspect','host-learn','host-infer'] and '--sk' not in call['command'] and '--vector' not in call['command'],'keylessPublicRoleArguments')
   if call['role']=='host':
    host_calls[command]+=1
    if command=='inspect':cache[payload['sha256']]=payload
  scalar_dir=root/'.private/reader/recipient_keys';keys=list(scalar_dir.iterdir());require(sorted(p.name for p in keys)==[f'r{i:02d}.key' for i in range(16)] and all(p.stat().st_size==435 and p.stat().st_mode&0o777==0o600 for p in keys),'recipientCredentialCountOnly')
  require(not any(k in instance.rcfg for k in ['recipient_key_dir','private_db','private_cost_log']),'acceptorHasNoScalarPaths')
  storage={};inventories={}
  for role,directory in [('host',instance.host_cas.root),('authority',Path(instance.acfg['cas'])),('acceptor',Path(instance.rcfg['cas']))]:
   files=[p for p in directory.iterdir() if p.is_file() and len(p.name)==64];inventories[role]=[{'sha256':file_sha(p),'bytes':p.stat().st_size} for p in sorted(files)]
   require(all(x['sha256']==p.name for x,p in zip(inventories[role],sorted(files),strict=True)),'publicCASInventoryIdentity')
   storage[role]={'objects':len(files),'bytes':sum(p.stat().st_size for p in files)}
  # Final public shutdown: no public operation below this boundary.
  instance.close();require(all(p.poll() is not None for p in instance.processes),'allServicesClosed')
  host_report=instance.worker_report;require(host_report['clean_exit'] and host_report['requests']==37 and host_report['stats']['crypto_calls']==dict(host_calls) and host_report['inspection_cache_entries']==len(cache),'persistentHostCompletedExactly37')
  host_report['cache_canonical_json_bytes']=len(canonical(cache));host_report['cache_bytes_are_not_heap_rss']=True
  public_report={'schema':'public-seed-durable-journal-public-v1','ok':True,'genesis_sha256':digest(instance.g),'context_id':instance.g['context_id'],'learns':33,'infers':4,'expiries':1,'finalized_events':37,'exact_fifo_expiry_and_final_queue':True,'ordered_authority_acceptor_histories_match':True,'independent_replay':replay,'public_replay_ns':replay_ns,'orderly_reopen':checkpoint,'authorized_historical_retries':retries,'setup':setup_result,'binding':binding,'public_log_audit':audit,'public_calls':len(calls),'native_counts':dict(counts),'role_command_costs':[{'role':r,'command':c,'count':len(xs),'sum_ns':sum(xs),'min_ns':min(xs),'max_ns':max(xs)} for (r,c),xs in sorted(costs.items())],'retained_public_cas':storage,'host_worker':host_report,'all_public_replay_and_operations_before_private_drain':True,'all_public_workers_and_services_closed':True,'private_answer_db_absent_through_public_checks':True,'public_acceptor_has_recipient_key_paths':False,'scalar_master_generated':False,'scalar_projection_delivery_generated':False,'credential_count_without_private_reads':16}
  write_json(reports/'accepted_envelopes.json',accepted);write_json(reports/'public_ciphertext_inventory.json',inventories)
  for name in ['commands.jsonl','role_calls.jsonl','events.jsonl','host_worker.jsonl','server_processes.jsonl','reader-server.jsonl','authority-server.jsonl','replay.json']:
   if (root/name).exists():
    with gzip.open(reports/(name+'.gz'),'wb') as sink:sink.write((root/name).read_bytes())
  for name in ['genesis.json','public_context.json','registry.json','public_transcript.json','context_validation.json','public_setup_verification.json','setup_report.json','public_log_audit.json','orderly_reopen.json','final_seed_replay.json']:
   (reports/name).write_bytes((root/name).read_bytes())
  public_report['whole_public_phase_ns']=time.perf_counter_ns()-started
  write_json(reports/'public_complete.json',public_report)
  print(json.dumps({'phase':'public_complete','learns':33,'infers':4,'expiries':1,'all_services_closed':True,'public_seconds':public_report['whole_public_phase_ns']/1e9}),flush=True)
  return public_report

 except Exception as error:
  if instance is not None:instance.close()
  write_json(reports/'failure.json',{'ok':False,'phase':phase,'error_type':type(error).__name__,'reason':str(error),'checkpoint_preserved':True});raise

def private_run(root,reports):
 check_pins(reports)
 gate=read_json(reports/'PUBLIC_GATE.json');require(gate['ok'] and gate['all_public_process_groups_absent'],'publicGateBeforePrivateWorker')
 require(gate['execution_pins_sha256']==file_sha(reports/'execution_pins.json'),'privateExecutionPins')
 require(gate['public_verification_sha256']==file_sha(reports/'public_verification.json'),'privatePublicVerifierPin')
 seal=read_json(reports/'PUBLIC_SEAL.json');require(file_sha(reports/'PUBLIC_SEAL.json')==gate['public_seal_sha256'],'privatePublicSealPin')
 for name,item in seal['files'].items():require(file_sha(reports/name)==item['sha256'],'privateClosedEvidencePin:'+name)
 public_report=read_json(reports/'public_complete.json')
 require(public_report['all_public_workers_and_services_closed'] and public_report['all_public_replay_and_operations_before_private_drain'],'publicWorkerClosed')
 marker=root/'.private/postprotocol/private_started.json';require(not marker.exists(),'onePrivateWorkerOnly')
 write_json(marker,{'public_gate_sha256':file_sha(reports/'PUBLIC_GATE.json'),'no_retry':True},True)
 first=private_call(root,SOURCE/'journal/drain.py','--config',root/'.private/reader/drain_config.json')
 comparison=private_call(root,HERE/'private_oracle.py','compare','--root',root)
 require(first['new_private_decodes']==4 and first['already_private_decoded']==0 and first['private_decodes_total']==4 and comparison['all_match'],'normalPrivateComparison')
 report={'schema':'public-seed-durable-journal-normal-v1','ok':True,'learns':33,'infers':4,'exact_original_expiries':1,'finalized_events':37,'all_private_integer_comparisons_match':True,'private_integer_comparisons':4,'private_decoder_processes':4,'genesis_sha256':public_report['genesis_sha256'],'context_id':public_report['context_id'],'public_complete_sha256':file_sha(reports/'public_complete.json'),'public_gate_sha256':file_sha(reports/'PUBLIC_GATE.json'),'execution_pins_sha256':file_sha(reports/'execution_pins.json'),'whole_public_worker_ns':public_report['whole_public_phase_ns'],'all_public_operations_replay_and_services_close_before_any_private_drain':True,'scalar_master_generated':False,'scalar_projection_delivery_generated':False,'scope':['Concrete SHAKE256 with one complete fresh registry; conditional classical ROM/DDH, not concrete-hash/QROM/timing privacy.','All16 recipient scalars retain the full per-input row span, including expired inputs; no selected-only release.','Known deterministic fixture and shared OS; no private-lifetime confidentiality, isolation or new utility.','Aggregate correctness publication outside the closed public transcript; private scores, hashes and decode durations omitted.']}
 write_json(reports/'report.json',report);print(json.dumps({'ok':True,'all_private_integer_comparisons_match':True}),flush=True)
 return report

def main():
 p=argparse.ArgumentParser();p.add_argument('mode',choices=['prepare','public','private']);p.add_argument('--reports',type=Path,required=True);p.add_argument('--root',type=Path);a=p.parse_args();reports=a.reports.resolve()
 require(reports==HERE/'reports/normal_001','oneFixedReportDirectory')
 if a.mode=='prepare':prepare(reports)
 else:
  require(a.root is not None and a.root.resolve()==HERE/'runtime/normal_001','oneFixedRuntimeDirectory')
  require((reports/'LAUNCH.json').exists(),'authorizedLauncherRequired')
  launch=read_json(reports/'LAUNCH.json')
  require(launch['schema']=='public-seed-journal-authorized-launch-v1' and launch['execution_pins_sha256']==file_sha(reports/'execution_pins.json'),'exactAuthorizedLauncherPins')
  (public_run if a.mode=='public' else private_run)(a.root.resolve(),reports)
if __name__=='__main__':main()
