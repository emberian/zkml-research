"""Scoped baseline falsifier: route an unselected coordinate through one ticket."""
import argparse
from controls import *

def main():
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);a=p.parse_args();root=Path(a.root).resolve();policy,vector,other=normal_inputs(root)
 run=Run(root/'run',policy)
 try:
  learn=run.prepare('Learn',0,'learn',vector=vector);run.accepted(learn)
  selected=run.prepare('Infer',0,'selected-coordinate-zero',query_index=0)
  malicious_query={'schema':'resident-public-query-v1','params_id':run.g['crypto']['params_id'],'coefficients':[0,1]+[0]*575}
  qhash=run.host_cas.put(canonical(malicious_query),'query');require({'query_ct':qhash,'route':0} not in run.g['query_policy'],'unselectedQuery')
  out=run.host_cas.fresh_output();run.host_cas.crypto.run('host-infer',acc=run.host_cas.get(run.head()['state']['routes']['0']['acc_ct']),query=run.host_cas.get(qhash,'query'),out=out)
  routed=run.host_cas.finish_output(out);require(routed!=selected['proposal']['result_ct'],'differentActualOutputCiphertext')
  forged_req=clone(selected);forged_req['proposal']['result_ct']=routed
  payload={'schema':'resident-finalized-v1','request':forged_req,'request_sha256':digest(forged_req),'revision':selected['action']['parent_revision']+1,'parent_state':selected['action']['parent_state'],'next_state':selected['action']['parent_state'],
   'delta':{'kind':'Infer','route':0,'query_ct':selected['action']['query_ct'],'output_ct':routed},'output_ct':routed}
  envelope=sign(payload,run.acfg['signing_key'],'resident-authority-finalization-v1');reply=receive(run,envelope,run.host_cas.get(routed).read_bytes())
  require(reply.get('ok'),'baselineSignerSubstitution');actual=run.answers()['selected-coordinate-zero'];require(actual==-3 and actual!=5,'routedCoordinateOracle')
  # Signature cannot manufacture a new independent command authorization.
  missing=clone(envelope);missing['payload']['request']['action']['nonce']='unsigned-extra-ticket';missing=sign(missing['payload'],run.acfg['signing_key'],'resident-authority-finalization-v1')
  refusal=expect_refusal(receive(run,missing,run.host_cas.get(routed).read_bytes()),'signer_alone_cannot_mint_query_ticket')
  report={'ok':True,'schema':'resident-signer-route-control-v1','authorized_query_ticket_count':1,'unauthorized_query_vector_used_only_by_attacker_computation':True,'actual_bfv_routed_other_coordinate':True,
   'baseline_reader_accepted_valid_authority_signature':True,'selected_output_oracle_mismatch':True,'authority_committed_infer':False,'extra_unsigned_ticket_refused':refusal,
   'scope':'One extra state-coordinate disclosure per independently authorized available release ticket. General read-all requires enough such opportunities; signer alone cannot mint authorizer signatures or bypass nonce dedup.',
   'forged_envelope':envelope,'reader_ack':reply,'source_sha256':sources()}
  write_json(root/'report.json',report);print(json.dumps({'ok':True,'routed_other_coordinate':True,'independent_ticket_still_required':True}))
 finally:run.close()
if __name__=='__main__':main()
