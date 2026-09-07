"""Tested live text encoder -> real signed encrypted Learn -> finalized Infer."""
import argparse
from datasets import *

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--input',required=True);a=p.parse_args()
 root=Path(a.root).resolve();root.parent.mkdir(parents=True,exist_ok=True)
 inputs=root.parent/(root.name+'_policy.json');write_json(inputs,[{'route':0 if i<8 else 1,'path':str(UTILITY/'public_queries'/f'q{i:02d}.json')} for i in range(16)])
 run=Run(root,inputs)
 try:
  private_input=read_json(a.input);route=private_input['route'];qi=route*8
  before=run.prepare('Infer',route,'before-live-observation',query_index=qi);run.accepted(before)
  folder=run.work/'live-learn';folder.mkdir();write_json(folder/'head.json',run.head());private_work=root/'.private/issuer/live_encoder'
  argv=[sys.executable,str(UTILITY/'live_encoder/issue_text.py'),'--input',str(Path(a.input).resolve()),'--issuer-config',str(root/'.private/issuer/config.json'),
   '--head',str(folder/'head.json'),'--private-workdir',str(private_work),'--out',str(folder/'issued'),'--request-id','live-learn','--nonce','nonce-live-learn','--record-id','opaque-live-observation-1']
  start=time.perf_counter_ns();process=subprocess.run(argv,capture_output=True,timeout=300);elapsed=time.perf_counter_ns()-start
  # Encoder's complete plaintext/vector evidence remains in its private workdir.
  public_call={'role':'trusted_live_issuer_frontend','argv':argv,'elapsed_ns':elapsed,'exit_code':process.returncode,'stdout':process.stdout.decode(),'stderr':process.stderr.decode()}
  write_json(root/'live_frontend_call.json',public_call);require(process.returncode==0,'liveIssuerFrontend:'+process.stdout.decode())
  auth=folder/'issued/authorization.json';ct=folder/'issued/fresh.ct';run.host_cas.import_file(ct);run.upload(ct)
  run.role('propose',config=root/'host_config.json',head=folder/'head.json',authorization=auth,cas=root/'host_cas',out=folder/'request.json')
  req=read_json(folder/'request.json');run.upload(run.host_cas.get(req['proposal']['result_ct']));run.accepted(req)
  after=run.prepare('Infer',route,'after-live-observation',query_index=qi);run.accepted(after)
  # Trusted oracle only. Neither text, feature vector, private score nor their hashes are emitted.
  vector=read_json(private_work/'vector.json');query=read_json(root/'queries'/f'q{qi:02d}.json')['coefficients'];expected=sum(x*y for x,y in zip(vector,query));answers=run.answers()
  require(answers['before-live-observation']==0 and answers['after-live-observation']==expected,'liveEncoderOracle')
  report={'ok':True,'schema':'resident-live-text-journal-v1','live_text_encoder_executed':True,'learns':1,'infers':2,'oracle_comparisons':2,'oracle_all_match':True,'output_changed_after_learning':expected!=0,
   'nonzero_learned_state_ciphertext':req['proposal']['result_ct']!=run.g['zero_ct_sha256'],'encoder_frontend_sha256':sha((UTILITY/'live_encoder/issue_text.py').read_bytes()),
   'encoder_frontend_elapsed_ns':elapsed,'replay':run.replay(True),'storage':storage(run),'commands':report_calls(run),'source_sha256':sources(),
   'scope':'New illustrative text through tested plaintext issuer encoder and actual encrypted journal. Trusted issuer asserts feature/range provenance; no hidden encoder, semantic provenance proof, or held-out utility estimate for this single text.'}
  write_json(root/'report.json',report);print(json.dumps({k:report[k] for k in ['ok','learns','infers','oracle_all_match','output_changed_after_learning']}))
 finally:run.close()
if __name__=='__main__':main()
