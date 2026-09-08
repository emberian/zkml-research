#!/usr/bin/env python3
"""New setup/configuration only; frozen operational core is unchanged."""
from pathlib import Path
import argparse,json,os,subprocess,sys,time
HERE=Path(__file__).resolve().parent
SOURCE=HERE/'source'
sys.path.insert(0,str(SOURCE/'journal'))
from common import Crypto,create_signing_key,digest,read_json,require,sha,write_json,canonical
CORE_NAMES=['common.py','model.py','roles.py','authority.py','reader.py','drain.py','run.py','../verified_reader/service.py']
CRYPTO_NAMES=['crypto.py','group.py','native_pow.py','rows.json']

def verify_dependencies():
 pins=read_json(HERE/'SOURCE_PINS.json')
 for name,item in pins['files'].items():require(sha((HERE/name).read_bytes())==item['sha256'],'immutableDependency:'+name)
 return pins

def verify_binding(root):
 root=Path(root);g=read_json(root/'genesis.json');b=g['public_coin_setup']
 require(b['schema']=='public-coin-journal-genesis-binding-v1','publicSetupBindingSchema')
 for name,expected in b['public_artifacts_sha256'].items():require(sha((root/name).read_bytes())==expected,'boundSetupArtifact:'+name)
 require(b['setup_source_sha256']==sha((SOURCE/'public_setup/setup.py').read_bytes()),'boundSetupSource')
 require(b['join_source_sha256']==sha(Path(__file__).read_bytes()),'boundJoinSource')
 require(b['dependency_inventory_sha256']==sha((HERE/'SOURCE_PINS.json').read_bytes()),'boundDependencies')
 t=read_json(root/'public_transcript.json');v=read_json(root/'public_setup_verification.json');reg=read_json(root/'registry.json')
 require(t['context_id']==g['context_id']==v['context_id'],'boundContextIdentity')
 require(t['setup_source_sha256']==b['setup_source_sha256'],'transcriptSourceIdentity')
 require(t['crypto_sources']==g['crypto_sources'],'transcriptCryptoIdentity')
 require(t['native_dependency']==g['native_dependency'],'transcriptNativeIdentity')
 require(t['registry_sha256']==digest(reg)==b['public_artifacts_sha256']['registry.json'],'transcriptRegistryIdentity')
 require(v['complete_context_byte_match'] and v['no_private_file_read_by_public_verifier'] and v['transcript_sha256']==digest(t),'trustedFullPublicVerificationRecord')
 require(len(t['announcements'])==len(reg['slots'])==16,'fixedRegistrationSize')
 for i,a in enumerate(t['announcements']):require(a==read_json(root/f'announcements/r{i:02d}.json'),'transcriptAnnouncementIdentity')
 return {'ok':True,'genesis_sha256':digest(g),'public_artifacts_checked':len(b['public_artifacts_sha256']),'public_transcript_sha256':digest(t),'registration_sha256':digest(reg),'trusted_setup_binding_only':True}

def setup(root):
 verify_dependencies();root=Path(root).resolve();root.mkdir(parents=True,exist_ok=False,mode=0o700)
 private=root/'.private';private.mkdir(mode=0o700)
 for role in ['issuer','command','authority','reader','pending']:(private/role).mkdir(mode=0o700)
 (private/'reader/recipient_keys').mkdir(mode=0o700)
 (root/'announcements').mkdir();(root/'query_vectors').mkdir();(root/'queries').mkdir()
 binary=SOURCE/'crypto/crypto.py';adapter=SOURCE/'public_setup/setup.py'
 native=Path('/opt/homebrew/opt/openssl@3/lib/libcrypto.3.dylib').resolve()
 base={'crypto_binary':str(binary),'crypto_binary_sha256':sha(binary.read_bytes()),'crypto_sources':{n:sha((binary.parent/n).read_bytes()) for n in CRYPTO_NAMES},'native_dependency':{'path':str(native),'sha256':sha(native.read_bytes())}}
 log=root/'commands.jsonl';crypto=Crypto(base,'honest_setup',log);params=crypto.run('params');begun=time.perf_counter_ns()
 def call(command,**kwargs):
  verify_dependencies();argv=[str(adapter),command]
  for k,v in kwargs.items():argv.extend(['--'+k.replace('_','-'),str(v)])
  start=time.perf_counter_ns();out=subprocess.run([sys.executable,*argv],capture_output=True,timeout=300)
  record={'role':'honest_public_setup','command':argv,'elapsed_ns':time.perf_counter_ns()-start,'exit_code':out.returncode,'stdout':out.stdout.decode(),'stderr':out.stderr.decode(),'private_output_omitted':False}
  with log.open('ab') as sink:sink.write(canonical(record)+b'\n')
  require(out.returncode==0,'publicSetupCommand:'+command);return json.loads(out.stdout)
 registry=root/'registry.json';reg=call('auth-init',private=private/'registration',out=registry)
 for i in range(16):call('recipient-init',registry=registry,registry_sha256=reg['registry_sha256'],row=i,auth_key=private/'registration'/f'r{i:02d}.sigkey',pending=private/'pending'/f'r{i:02d}.scalar',out=root/'announcements'/f'r{i:02d}.json')
 built=call('public-build',registry=registry,registry_sha256=reg['registry_sha256'],announcements=root/'announcements',context=root/'public_context.json',transcript=root/'public_transcript.json',zero=root/'zero.ct')
 verification=call('verify-public',registry=registry,registry_sha256=reg['registry_sha256'],context=root/'public_context.json',transcript=root/'public_transcript.json')
 write_json(root/'public_setup_verification.json',verification)
 pk=root/'public_context.json';base.update(crypto_context=str(pk),crypto_context_sha256=sha(pk.read_bytes()))
 require(base['crypto_context_sha256']==built['context_id'],'contextByteIdentity')
 validation=crypto.run('validate-context');require(validation['validated'] and validation['context_id']==built['context_id'] and validation['source_sha256']==base['crypto_sources'],'fullContextValidation')
 write_json(root/'context_validation.json',validation)
 for i in range(16):
  pending=private/'pending'/f'r{i:02d}.scalar';crypto.run('recipient-finalize',row=i,secret=pending,out=private/'reader/recipient_keys'/f'r{i:02d}.key');pending.unlink()
 require(not list((private/'pending').iterdir()),'pendingCopiesRemoved')
 require(not built['scalar_master_computed_in_this_path'] and not built['scalar_projection_delivery_computed_in_this_path'],'noScalarDealerSetup')
 issuer_vk=create_signing_key(private/'issuer/signing.key');command_vk=create_signing_key(private/'command/signing.key');authority_vk=create_signing_key(private/'authority/signing.key')
 policy=[];bindings={};rows=read_json(binary.parent/'rows.json')
 for index,row in enumerate(rows):
  vector=root/'query_vectors'/f'q{index:02d}.json';write_json(vector,row);out=root/'queries'/f'q{index:02d}.json'
  meta=crypto.run('encode-query',vector=vector,out=out);query=read_json(out)
  policy.append({'query_ct':meta['sha256'],'route':0});bindings[meta['sha256']]={k:query[k] for k in ['context_id','row_id','row_sha256','recipient_id','token_sha256']}
 bound=['public_transcript.json','registry.json','public_setup_verification.json',*[f'announcements/r{i:02d}.json' for i in range(16)]]
 setup_binding={'schema':'public-coin-journal-genesis-binding-v1','public_artifacts_sha256':{name:sha((root/name).read_bytes()) for name in bound},'setup_source_sha256':sha(adapter.read_bytes()),'join_source_sha256':sha(Path(__file__).read_bytes()),'dependency_inventory_sha256':sha((HERE/'SOURCE_PINS.json').read_bytes()),'sampling_premise':'honest independent direct public tau/U; accepted values only, OS RNG state excluded','registration_premise':'fixed authenticated slots and independent honest recipient-owned scalars','scalar_master_computed_in_executed_setup_path':False,'scalar_projection_delivery_computed_in_executed_setup_path':False}
 g={'schema':'resident-genesis-v1','crypto':params,'key_id':built['context_id'],'context_id':built['context_id'],'public_key_sha256':sha(pk.read_bytes()),'zero_ct_sha256':sha((root/'zero.ct').read_bytes()),'capacity':32,'routes':[0,1],'issuer_vk':issuer_vk,'command_vk':command_vk,'authority_vk':authority_vk,'recipient':'dedicated-fixed-span-recipient-coalition','query_policy':policy,'query_bindings':bindings,'feature_policy':'trusted-issuer-signed577-int8-bound127-v1','custody':'Honest direct public tau/U setup and honest independent registration. No scalar master/projection delivery executed. All16 recipient-owned scalar keys remain in private drain; full per-input fixed span. Shared OS, no physical isolation.','journal_program':'designated-ddh-keyless-recomputation-delta-journal-two-phase-v1','crypto_binary_sha256':base['crypto_binary_sha256'],'crypto_sources':base['crypto_sources'],'native_dependency':base['native_dependency'],'context_validation_sha256':sha((root/'context_validation.json').read_bytes()),'journal_sources':{n:sha((SOURCE/'journal'/n).read_bytes()) for n in CORE_NAMES},'public_coin_setup':setup_binding}
 write_json(root/'genesis.json',g);base.update(genesis_path=str(root/'genesis.json'),genesis_sha256=digest(g),command_log=str(log));write_json(root/'host_config.json',base)
 prefix='/tmp/pcj-'+os.urandom(6).hex()
 for role in ['issuer','command','authority','reader']:
  cfg={**base,'role':role}
  if role!='reader':cfg['signing_key']=str(private/role/'signing.key')
  if role=='issuer':cfg['public_key']=str(pk)
  if role in ['authority','reader']:
   role_dir=root/role;role_dir.mkdir();cfg.update(db=str(role_dir/'journal.sqlite3'),cas=str(role_dir/'cas'),socket=prefix+'-'+role+'.sock')
  if role=='authority':cfg['reader_socket']=prefix+'-reader.sock'
  if role=='reader':
   cfg['verified_reader_source_sha256']=sha((SOURCE/'verified_reader/service.py').read_bytes())
   drain={**cfg,'role':'recipient_private_drain','recipient_key_dir':str(private/'reader/recipient_keys'),'private_db':str(private/'reader/answers.sqlite3'),'private_cost_log':str(private/'reader/decode_costs.jsonl')}
   write_json(private/'reader/drain_config.json',drain,True)
  write_json(private/role/'config.json',cfg,True)
 result={'ok':True,'genesis_sha256':digest(g),'context_id':g['context_id'],'setup_elapsed_ns':time.perf_counter_ns()-begun,'binding':verify_binding(root),'recipient_scalar_files':16,'pending_scalar_files':0,'scalar_master_generated':False,'scalar_projection_delivery_generated':False}
 write_json(root/'setup_report.json',result);return result
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);a=p.parse_args();print(json.dumps(setup(a.root)))
