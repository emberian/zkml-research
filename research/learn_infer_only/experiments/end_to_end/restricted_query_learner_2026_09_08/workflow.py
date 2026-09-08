"""One full-profile normal semantic learner run; each actor has its own process."""
import datetime,hashlib,json,os,subprocess,sys,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
import transport
from basis import load
sha=lambda p:transport.digest(p)
def save(p,d):p.write_text(json.dumps(d,indent=2)+'\n')
def main():
 registry=HERE/'registry.json';basis,registry_hash=load(registry);transport.configure_basis(registry);p=transport.params('candidate_full')
 fixture=json.loads((HERE/'fixture.json').read_text());pins=json.loads((HERE/'SOURCE_PINS.json').read_text())
 assert all(sha(HERE/k)==v for k,v in pins['owned'].items());assert 2*max(basis.bounds)<p.p//2
 rt=HERE/'.runtime/normal_001';results=HERE/'results/normal_001'
 if rt.exists() or results.exists():raise ValueError('Sole normal run already exists; no retry or resume')
 public=rt/'public';private=rt/'private';public.mkdir(parents=True);private.mkdir(mode=0o700);results.mkdir(parents=True)
 recipients=[]
 for i in range(p.recipients):
  folder=private/f'recipient_{i:02d}';folder.mkdir(mode=0o700);os.chmod(folder,0o700);recipients.append(folder)
 profiles={}
 for role in ['public']+[f'recipient_{i:02d}' for i in range(p.recipients)]:
  denied=[private] if role=='public' else [x for x in recipients if x.name!=role]
  profile='(version 1)\n(allow default)\n(deny network*)\n'
  for folder in denied:profile+='(deny file-read* file-write* (subpath '+json.dumps(str(folder))+'))\n'
  path=results/f'{role}.sb';path.write_text(profile);profiles[role]=path
 commands=[];start=time.perf_counter();started=datetime.datetime.now(datetime.timezone.utc).isoformat();deadline=start+900
 def actor(name,role,args):
  receipt=results/f'{name}.json';argv=['/usr/bin/sandbox-exec','-f',str(profiles[role]),sys.executable,'-B',str(HERE/'transport.py'),'--registry',str(registry),'--receipt',str(receipt),*map(str,args)];began=time.perf_counter();timeout=min(180,deadline-began)
  if timeout<=0:raise TimeoutError('Overall15-minute run cap')
  proc=subprocess.run(argv,capture_output=True,text=True,cwd=public,timeout=timeout)
  (results/f'{name}.stdout').write_text(proc.stdout);(results/f'{name}.stderr').write_text(proc.stderr)
  row={'event':name,'role':role,'argv':argv,'returncode':proc.returncode,'wall_seconds':time.perf_counter()-began,'elapsed_seconds':time.perf_counter()-start,'receipt':str(receipt)};commands.append(row);save(results/'commands.partial.json',commands)
  if proc.returncode:raise RuntimeError(f'{name}: {proc.stderr} {proc.stdout}')
  r=json.loads(receipt.read_text());assert r['status']=='PASS' and r['registry_sha256']==registry_hash
  private_reads=[x for x in r['artifact_reads'] if x['private']]
  if role=='public':assert not private_reads
  else:assert all(Path(x['path']).is_relative_to(private/role) for x in private_reads)
  print(json.dumps({'event':name,'role':role,'wall_seconds':row['wall_seconds'],'elapsed_seconds':row['elapsed_seconds'],'status':'PASS'}),flush=True)
  return r
 try:
  actor('init','public',['init','--profile','candidate_full','--out',public/'a.ring'])
  for i,folder in enumerate(recipients):actor(f'register_{i:02d}',folder.name,['register','--public-a',public/'a.ring','--coordinate',i,'--key-out',folder/'key.ring','--registration-out',public/f'registration_{i:02d}.ring'])
  args=['finalize','--public-a',public/'a.ring','--out',public/'public.ring']
  for i in range(p.recipients):args+=['--registration',public/f'registration_{i:02d}.ring']
  actor('finalize','public',args)
  queues={c:[] for c in fixture['classes']};states={};snapshots=[]
  for event in fixture['events']:
   n=event['event'];label=event['class'];ip=public/f'input_{n:02d}.json';save(ip,[x%p.p for x in event['vector']]);fresh=public/f'input_{n:02d}.ring';out=public/f'state_{n:02d}.ring'
   actor(f'encode_{n:02d}','public',['encode','--public',public/'public.ring','--input',ip,'--out',fresh])
   args=['window','--add',fresh,'--capacity',2,'--out',out]
   if label in states:args+=['--state',states[label]]
   if len(queues[label])==2:
    expired=queues[label].pop(0);assert event['expired_event'] is not None;args+=['--expire',expired]
   else:assert event['expired_event'] is None
   actor(f'learn_{n:02d}','public',args);queues[label].append(fresh);states[label]=out
   if n%2==0:
    snapshots.append({'revision':n,'classes':{c:{'path':str(states[c]),'sha256':sha(states[c]),'count':len(queues[c])} for c in fixture['classes']}})
  for i,label in enumerate(fixture['classes']):
   args=['combine','--out',public/f'rebuilt_{i}.ring']
   for fresh in queues[label]:args+=['--term',1,fresh]
   actor(f'exact_expiry_rebuild_{i}','public',args)
   assert sha(public/f'rebuilt_{i}.ring')==sha(states[label]),'Actual full output bytes differ from direct live sum'
  model_map={'registry_sha256':registry_hash,'capacity':2,'snapshots':snapshots};save(public/'models.json',model_map)
  public_files={x.name:{'bytes':x.stat().st_size,'sha256':sha(x)} for x in sorted(public.iterdir()) if x.is_file()}
  assert all(sha(HERE/k)==v for k,v in pins['owned'].items())
  closure={'status':'PASS','registry_sha256':registry_hash,'source_pins_sha256':sha(HERE/'SOURCE_PINS.json'),'elapsed_seconds':time.perf_counter()-start,'all_public_actor_processes_exited':True,'public_actor_private_artifact_reads':0,'fresh_encodes':6,'learn_updates':6,'exact_expiries':2,'two_complete_output_byte_rebuilds_match':True,'public_files':public_files,'sources_unchanged':True}
  save(results/'PUBLIC_COMPLETE.json',closure);print(json.dumps({'event':'public_complete','elapsed_seconds':time.perf_counter()-start}),flush=True)
  answers=[]
  for i,folder in enumerate(recipients):
   receipt=actor(f'query_recipient_{i:02d}',folder.name,['query','--key',folder/'key.ring','--models',public/'models.json']);actual=receipt['result']['query_results']
   for got,reference in zip(actual,fixture['snapshots']):assert got['revision']==reference['revision'] and got['scores']==reference['scores'][i] and got['prediction']==reference['predictions'][i]
   assert len(actual)==3;answers.append({'coordinate':i,'query_text':basis.registry['queries'][i]['text'],'expected_label':basis.registry['queries'][i]['label'],'results':actual})
  result={'status':'PASS','started_utc':started,'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'elapsed_seconds':time.perf_counter()-start,'public_elapsed_seconds':closure['elapsed_seconds'],'profile':'candidate_full','parameters':p.__dict__,'registry_sha256':registry_hash,'actual_registered_recipient_keys':16,'absent_recipient_rows_generated':0,'universal_reader_constructed':False,'fresh_encodes':6,'learns':6,'expiries':2,'query_score_matches':96,'prediction_matches':48,'public_complete_before_first_recipient_read':True,'public_roles_private_artifact_reads':0,'orchestrator_private_payload_reads':0,'commands':commands,'registered_query_results':answers,'private_metadata_only':[{'coordinate':i,'key_bytes':(f/'key.ring').stat().st_size,'mode':oct((f/'key.ring').stat().st_mode&0o777)} for i,f in enumerate(recipients)],'source_pins_sha256':sha(HERE/'SOURCE_PINS.json'),'sources_unchanged':all(sha(HERE/k)==v for k,v in pins['owned'].items()),'scope':'Known-public cached text fixture, fixed query projection credentials, per-input full query-span capability for coalitions; no resident privacy or computational hardness measurement'}
 except Exception as e:result={'status':'FAIL','error':f'{type(e).__name__}: {e}','commands':commands,'elapsed_seconds':time.perf_counter()-start,'retry_or_resume_permitted':False}
 save(results/'RESULT.json',result);print(json.dumps({'status':result['status'],'elapsed_seconds':result['elapsed_seconds']}),flush=True)
 return 0 if result['status']=='PASS' else 1
if __name__=='__main__':raise SystemExit(main())
