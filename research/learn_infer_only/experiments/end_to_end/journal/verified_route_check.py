"""Exact same routed-coordinate envelope: baseline accepts, verified reader refuses."""
import argparse
from controls import *
SERVICE=HERE.parent/'verified_reader/service.py'

def put(address,path,kind='ct'):
 raw=Path(path).read_bytes();reply=rpc(address,{'op':'put','kind':kind,'sha256':sha(raw),'data':base64.b64encode(raw).decode()});require(reply.get('ok'),'verifiedPut')
def main():
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);a=p.parse_args();root=Path(a.root).resolve();policy,vector,other=normal_inputs(root);run=Run(root/'run',policy);vp=None
 try:
  learn=run.prepare('Learn',0,'learn',vector=vector);honest_learn=run.accepted(learn)['envelope'];selected=run.prepare('Infer',0,'selected-coordinate-zero',query_index=0)
  query={'schema':'resident-public-query-v1','params_id':run.g['crypto']['params_id'],'coefficients':[0,1]+[0]*575};qhash=run.host_cas.put(canonical(query),'query')
  out=run.host_cas.fresh_output();run.host_cas.crypto.run('host-infer',acc=run.host_cas.get(run.head()['state']['routes']['0']['acc_ct']),query=run.host_cas.get(qhash,'query'),out=out);routed=run.host_cas.finish_output(out)
  bad=clone(selected);bad['proposal']['result_ct']=routed
  payload={'schema':'resident-finalized-v1','request':bad,'request_sha256':digest(bad),'revision':2,'parent_state':selected['action']['parent_state'],'next_state':selected['action']['parent_state'],
   'delta':{'kind':'Infer','route':0,'query_ct':selected['action']['query_ct'],'output_ct':routed},'output_ct':routed}
  forged=sign(payload,run.acfg['signing_key'],'resident-authority-finalization-v1');baseline=receive(run,forged,run.host_cas.get(routed).read_bytes());require(baseline.get('ok') and run.answers()['selected-coordinate-zero']==-3,'baselineRoutedDisclosure')
  private=run.root/'.private/verified_reader';private.mkdir(mode=0o700);address='/tmp/rsj-vroute-'+os.urandom(6).hex()+'.sock'
  cfg={**run.rcfg,'db':str(private/'answers.sqlite3'),'cas':str(run.root/'verified_reader/cas'),'socket':address,'verified_reader_source_sha256':sha(SERVICE.read_bytes())};write_json(private/'config.json',cfg,True)
  argv=[sys.executable,str(SERVICE),'--config',str(private/'config.json')];log=open(run.root/'verified-reader-server.jsonl','ab');vp=subprocess.Popen(argv,stdout=log,stderr=log);run.processes.append(vp)
  start=time.monotonic()
  while not Path(address).exists():require(vp.poll() is None,'verifiedStartup');require(time.monotonic()-start<30,'verifiedStartupTimeout');time.sleep(.02)
  for h in {run.g['zero_ct_sha256'],learn['action']['fresh_ct'],learn['proposal']['result_ct'],routed}:put(address,run.host_cas.get(h))
  qpath=run.host_cas.get(selected['action']['query_ct'],'query');put(address,qpath,'query')
  registration=rpc(address,{'op':'register','authorization':selected['authorization'],'query':base64.b64encode(qpath.read_bytes()).decode()});require(registration.get('ok'),'verifiedTicket')
  sync=rpc(address,{'op':'sync','envelope':honest_learn});require(sync.get('ok'),'verifiedLearn')
  rejected=rpc(address,{'op':'sync','envelope':forged});expect_refusal(rejected,'exact_routed_envelope_sync');require(rejected['reason']=='verifiedArithmeticProposal','expectedArithmeticRefusal')
  receive_bad=rpc(address,{'op':'receive','envelope':forged,'ciphertext':base64.b64encode(run.host_cas.get(routed).read_bytes()).decode()});expect_refusal(receive_bad,'unverified_routed_release')
  require(rpc(address,{'op':'status'})['received']==0,'noRoutedDecryption')
  # Retarget only trusted authority delivery configuration to the same recipient's verified service.
  run.stop(run.authority);run.acfg['reader_socket']=address;write_json(run.root/'.private/authority/config.json',run.acfg,True);run.authority=run.start('authority',run.root/'.private/authority/config.json')
  honest=run.submit(selected);require(honest.get('ok') and honest['delivery']['status']=='pending','commitBeforeVerification')
  sync_honest=rpc(address,{'op':'sync','envelope':honest['envelope']});require(sync_honest.get('ok'),'verifiedSelectedArithmetic')
  released=run.accepted(selected);require(released['status']=='replayed' and released['envelope']==honest['envelope'],'verifiedExactRetryRelease')
  with sqlite3.connect(cfg['db']) as db:
   rows=db.execute('SELECT answer FROM received').fetchall();require(len(rows)==1 and json.loads(rows[0][0])['signed_score']==5,'verifiedSelectedOracle')
  status=rpc(address,{'op':'verified_status'});require(status['revision']==2 and status['verified_records']==2,'verifiedMixedHead')
  report={'ok':True,'schema':'resident-exact-routed-envelope-composition-v1','same_forged_envelope_sha256':digest(forged),'baseline_disclosed_unselected_coordinate':True,
   'verified_sync_refusal':rejected,'verified_release_refusal':receive_bad,'verified_reader_disclosures_before_honest_output':0,'genuine_selected_output_oracle_match':True,
   'commit_then_verify_then_exact_retry_release':True,'verified_status':status,'verified_reader_source_sha256':sha(SERVICE.read_bytes()),'verified_reader_command':argv,'forged_envelope':forged,
   'source_sha256':sources(),'scope':'Same genesis/key, signed action and exact routed ciphertext envelope. Separate verified reader checks actual public transition before release. Full reader/issuer/query-authorizer and independent reader persistence assumptions remain.'}
  write_json(root/'report.json',report);print(json.dumps({'ok':True,'same_envelope_baseline_accepts_verified_refuses':True,'genuine_selected_output_matches':True}));Path(address).unlink(missing_ok=True)
 finally:run.close()
if __name__=='__main__':main()
