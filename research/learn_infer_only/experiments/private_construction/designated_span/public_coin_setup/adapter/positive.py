#!/usr/bin/env python3
"""Only approved normal setup,33Learn/4Infer/1expiry and exact comparisons."""
from pathlib import Path
import argparse,collections,hashlib,json,os,subprocess,sys,time
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE/'source/crypto'))
import crypto as c


def save(path,obj,private=False):
 path=Path(path);path.parent.mkdir(parents=True,exist_ok=True)
 path.write_bytes(c.canonical(obj)+b'\n');os.chmod(path,0o600 if private else 0o644)


def main():
 parser=argparse.ArgumentParser();parser.add_argument('--root',required=True);args=parser.parse_args()
 root=Path(args.root).resolve();root.mkdir(parents=True,exist_ok=False)
 private=root/'.private';private.mkdir(mode=0o700)
 for directory in ['pending','recipients']:(private/directory).mkdir(mode=0o700)
 for directory in ['announcements','inputs','ciphertexts','states','queries','outputs']:(root/directory).mkdir()
 sources=[HERE/'setup.py',HERE/'positive.py']+[HERE/'source/crypto'/name for name in ['crypto.py','group.py','native_pow.py','rows.json']]
 pins={str(p.relative_to(HERE)):c.sha(p.read_bytes()) for p in sources}
 from native_pow import LIBRARY
 native_pin={'path':str(LIBRARY),'sha256':c.sha(LIBRARY.read_bytes())}
 save(root/'execution_pins.json',{'source_sha256':pins,'native_dependency':native_pin,'reviewed_source_pins':json.loads((HERE/'SOURCE_PINS.json').read_text())})
 started=time.perf_counter_ns();deadline=time.monotonic()+900;public_calls=[];private_calls=[];context_id=None
 def call(program,command,private_output=False,**kwargs):
  c.require(time.monotonic()<deadline,'bounded positive wall budget')
  c.require(all(c.sha((HERE/name).read_bytes())==expected for name,expected in pins.items()),'source remains frozen')
  c.require(c.sha(LIBRARY.read_bytes())==native_pin['sha256'],'native remains frozen')
  argv=[sys.executable,str(program),command]
  if program.name=='crypto.py' and command!='params':
   argv+=['--context',str(root/'context.json')]
   if command!='validate-context':argv+=['--validated-context-sha256',context_id]
  for key,value in kwargs.items():
   if value is not None:argv+=['--'+key.replace('_','-'),str(value)]
  begin=time.perf_counter_ns();out=subprocess.run(argv,capture_output=True,timeout=300)
  elapsed=time.perf_counter_ns()-begin
  record={'program':str(program.relative_to(HERE)),'command':command,'argv':argv,'elapsed_ns':elapsed,'exit_code':out.returncode}
  if out.returncode:
   # Failures in private operations do not print a decoder's stdout/stderr.
   if not private_output:record.update(stdout=out.stdout.decode(),stderr=out.stderr.decode())
   save(root/'STOPPED.json',record);raise RuntimeError('normal operation failed:'+command)
  result=json.loads(out.stdout);record['counts']=result.get('counts',{})
  if private_output:
   record['private_output']=result;private_calls.append(record)
   with (private/'commands.jsonl').open('ab') as sink:sink.write(c.canonical(record)+b'\n')
   os.chmod(private/'commands.jsonl',0o600)
  else:
   c.require('signed_score' not in result and command!='reader-decrypt','public exact-field omission')
   record['result']=result;public_calls.append(record)
   with (root/'commands.jsonl').open('ab') as sink:sink.write(c.canonical(record)+b'\n')
  return result
 def progress(stage,**extra):
  record={'stage':stage,'elapsed_ns':time.perf_counter_ns()-started,**extra};save(root/'progress.json',record);print(json.dumps(record),flush=True)
 setup=HERE/'setup.py';backend=HERE/'source/crypto/crypto.py'
 registry=root/'registry.json'
 reg=call(setup,'auth-init',private=private/'auth',out=registry)
 reg_sha=reg['registry_sha256']
 for i in range(c.K):
  call(setup,'recipient-init',registry=registry,registry_sha256=reg_sha,row=i,auth_key=private/'auth'/f'r{i:02d}.sigkey',pending=private/'pending'/f'r{i:02d}.scalar',out=root/'announcements'/f'r{i:02d}.json')
 progress('all_recipient_announcements_before_public_coins',recipient_count=16)
 built=call(setup,'public-build',registry=registry,registry_sha256=reg_sha,announcements=root/'announcements',context=root/'context.json',transcript=root/'public_transcript.json',zero=root/'zero.ct')
 context_id=built['context_id']
 checked=call(setup,'verify-public',registry=registry,registry_sha256=reg_sha,context=root/'context.json',transcript=root/'public_transcript.json')
 validation=call(backend,'validate-context');c.require(validation['validated'] is True and validation['context_id']==context_id,'full trusted context validation')
 c.require(validation['source_sha256']==json.loads((HERE/'SOURCE_PINS.json').read_text())['frozen_crypto'],'frozen context validation sources')
 save(root/'context_validation.json',validation)
 for i in range(c.K):
  pending=private/'pending'/f'r{i:02d}.scalar'
  call(backend,'recipient-finalize',row=i,secret=pending,out=private/'recipients'/f'r{i:02d}.key')
  pending.unlink()
 setup_ns=time.perf_counter_ns()-started
 c.require(not list((private/'pending').iterdir()),'no redundant pending scalar files')
 progress('setup_complete',context_id=context_id,setup_elapsed_ns=setup_ns)
 body=c.read_json(root/'context.json',exact=True);ctx={'id':context_id,'body':body}
 queue=[];plain_queue=[];acc=root/'zero.ct';expiries=0;comparisons=[];queue_identity_checks=0;queue_time_ns=0
 selected={1:0,16:1,32:2,33:3}
 for t in range(1,34):
  x=[((t+3)*(j+5)%17)-8 for j in range(c.D)];vector=root/'inputs'/f'x{t:02d}.json';save(vector,x)
  fresh=root/'ciphertexts'/f'c{t:02d}.ct';call(backend,'issuer-encrypt',pk=root/'context.json',vector=vector,out=fresh)
  old=queue[0] if len(queue)==c.W else None
  output=root/'states'/f'a{t:02d}.ct';call(backend,'host-learn',acc=acc,fresh=fresh,old=old,out=output)
  if old:queue.pop(0);plain_queue.pop(0);expiries+=1
  queue.append(fresh);plain_queue.append(x);acc=output
  # Independent exact-byte group product of the retained original ciphertexts.
  begin=time.perf_counter_ns();product=[1]*(c.D+1)
  for path in queue:
   raw=path.read_bytes();c.require(len(raw)==c.PARAMS['state_bytes'],'reference state width')
   values=[int.from_bytes(raw[i:i+c.WIDTH],'big') for i in range(c.HEADER.size,len(raw),c.WIDTH)]
   product=[a*b%c.P for a,b in zip(product,values,strict=True)]
  c.require(output.read_bytes()==c.pack(ctx,c.STATE,product),'exact original queue product bytes')
  queue_time_ns+=time.perf_counter_ns()-begin;queue_identity_checks+=1
  if t in selected:
   row=selected[t];queryvector=root/'queries'/f'y{row:02d}.vector.json';save(queryvector,c.ROWS[row])
   query=root/'queries'/f'q{row:02d}.json';call(backend,'encode-query',vector=queryvector,out=query)
   transformed=root/'outputs'/f'o{row:02d}.ct';call(backend,'host-infer',acc=acc,query=query,out=transformed)
   answer=call(backend,'reader-decrypt',private_output=True,sk=private/'recipients'/f'r{row:02d}.key',ct=transformed)
   expected=sum(sum(v[j] for v in plain_queue)*c.ROWS[row][j] for j in range(c.D))
   c.require(answer['signed_score']==expected and answer['key_id']==context_id and answer['row_id']==row,'independent integer recipient comparison')
   comparisons.append({'learns':t,'row_id':row,'expected':expected,'actual':answer['signed_score'],'matches':True})
  if t%8==0 or t==33:progress('normal_closure',learns=t,infers=len(comparisons),expiries=expiries)
 save(private/'integer_comparisons.json',comparisons,True)
 c.require(expiries==1 and len(comparisons)==4 and queue_identity_checks==33,'positive counts')
 # Inventory is counts only; no hashes/contents of private key files.
 keyfiles=list((private/'recipients').glob('*.key'))
 c.require(len(keyfiles)==16 and all(p.stat().st_size==435 for p in keyfiles),'dedicated key inventory')
 commands=[r['command'] for r in public_calls]+[r['command'] for r in private_calls]
 c.require(not {'keygen','initializer','recipient-register'}.intersection(commands),'no legacy dealer path executed')
 counts=collections.Counter()
 for r in public_calls+private_calls:counts.update(r['counts'])
 total_ns=time.perf_counter_ns()-started
 report={'schema':'public-coin-setup-positive-v1','ok':True,'context_id':context_id,'setup_elapsed_ns':setup_ns,'total_harness_elapsed_ns':total_ns,
  'learns':33,'infers':4,'exact_original_expiries':1,'exact_queue_byte_checks':33,'queue_reference_ns':queue_time_ns,
  'independent_integer_comparisons':4,'all_match':True,'full_public_transcript_recomputation':checked['complete_context_byte_match'],
  'frozen_context_validation':True,'pivot_rank':16,'integer_pivot_determinant':-812032080,'public_field_samples':561,'public_tau_samples':16,
  'recipient_scalar_files':16,'recipient_scalar_file_bytes':435,'independent_registration_signing_key_files':16,
  'remaining_pending_scalar_files':0,'scalar_master_computed_in_executed_setup_path':False,'projection_key_delivery_computed_in_executed_setup_path':False,
  'unused_legacy_dealer_commands_present_in_frozen_backend':True,'public_process_calls':len(public_calls),'private_decode_process_calls':len(private_calls),
  'native_counts_all_actual_processes':dict(counts),'context_bytes':(root/'context.json').stat().st_size,'public_transcript_bytes':(root/'public_transcript.json').stat().st_size,
  'state_bytes':c.PARAMS['state_bytes'],'recipient_output_bytes':c.PARAMS['output_bytes'],
  'security_scope':'Accepted public tau/U/A transcript, honest independent direct field sampling and recipient keys; OS RNG state/physical timing excluded; known fixture and shared-account processes establish no operator confidentiality; classical DDH fixed span, no malicious setup or selected-only release claim.',
  'timing_scope':'Research costs including private role processing are outside the accepted-value cryptographic transcript; exact private per-call decode costs retained privately.'}
 save(root/'report.json',report)
 costs={'public_calls':[{'program':r['program'],'command':r['command'],'elapsed_ns':r['elapsed_ns'],'counts':r['counts']} for r in public_calls],
        'private_decode_calls':4,'private_decode_elapsed_ns_total':sum(r['elapsed_ns'] for r in private_calls),
        'scope':'Research measurement on a known public fixture, outside the accepted-value security transcript'}
 save(root/'costs.json',costs)
 print(json.dumps({'ok':True,'report':str(root/'report.json'),'learns':33,'infers':4,'expiry':1,'all_match':True,'seconds':total_ns/1e9}),flush=True)
if __name__=='__main__':main()
