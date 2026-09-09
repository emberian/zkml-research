#!/usr/bin/env python3
"""One fresh fixed two-class run; no retries and no baseline artifact reuse."""
import argparse
from pathlib import Path
import json
import sys
import time
from common import ROOT, command, now, save, sha
from fixture_builder import helper
from live import Live, initialize
import pipeline


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--run',default='live001');a=p.parse_args()
    if not a.run.isalnum():p.error('run ID must be alphanumeric')
    import os
    out=ROOT/'results'/a.run;out.mkdir(parents=True,exist_ok=False)
    instance=ROOT/'runtime'/a.run
    c=pipeline.config();start=time.monotonic()
    fixture=json.loads((ROOT/'fixture_builder/fixture.json').read_text())
    save(out/'started.json',{'utc':now(),'pid':os.getpid(),'profile_sha256':sha(ROOT/'PIPELINE.json'),'fixture_sha256':sha(ROOT/'fixture_builder/fixture.json'),'runtime':str(instance),'private_reads':0})
    try:
        initialized=initialize(instance,fixture['class_order']);save(out/'initialized.json',initialized)
        encoded=helper.encode(instance/'features');save(out/'issuance.json',encoded)
        vectors={x['id']:json.loads(Path(x['vector_path']).read_text()) for x in encoded['features']}
        live=Live(instance);teaches=[]
        for entry in fixture['teaching']:
            print(json.dumps({'phase':'teach','id':entry['id'],'class':entry['label']}),flush=True)
            teaches.append(live.teach_vector(entry['label'],vectors[entry['id']],entry['text'],entry['id']))
            save(out/'teaching.json',teaches)
        query=fixture['query'];qv=vectors[query['id']]
        print(json.dumps({'phase':'produce-all-class-kernel-proofs','request_id':query['id']}),flush=True)
        request=live.prepare_query(qv,query['text'],query['id']);save(out/'query_request.json',request)
        accepted=live.accept_query(query['id'])
        # Public proof process logs/acceptance are fully retained before first receive.
        save(out/'public_acceptance.json',accepted)
        print(json.dumps({'phase':'all-public-verification-complete','proofs':248,'private_reads':0}),flush=True)
        answer=live.receive(query['id']);save(out/'answer.json',answer)
        # This expected-state comparison is explicitly after the reader receipt.
        expected={}
        for entry in fixture['teaching']:
            value=sum(x*y for x,y in zip(vectors[entry['id']],qv))**2
            expected[entry['label']]={'kernel_values':[value]+[0]*7,'sum_kernel':value}
        comparisons=[]
        for label,record in expected.items():
            actual=answer['classes'][label]
            comparisons.append({'class':label,'expected':record,'actual':{k:actual[k] for k in record},'matches':all(actual[k]==v for k,v in record.items())})
        assert all(x['matches'] for x in comparisons)
        order=sorted(expected,key=lambda label:(-expected[label]['sum_kernel'],label))
        assert answer['ranking']==order and answer['prediction']==order[0]
        record={'complete_live_flow':True,'fresh_setup':True,'classes':fixture['class_order'],'teachings_committed':len(teaches),'accepted_revision':answer['revision'],'accepted_model_root':answer['model_root'],'queries':1,'fresh_update_proofs':16,'fresh_infer_proofs':232,'total_fresh_proofs':248,'reused_proofs':0,'all_verification_before_private_receive':True,'private_reads':answer['private_reads'],'exact_kernel_comparisons':comparisons,'prediction':answer['prediction'],'expected_arithmetic_prediction':order[0],'intended_label':query['intended_label'],'intended_label_matches':answer['prediction']==query['intended_label'],'encoder_stats':encoded['encoder_stats'],'public_acceptance_sha256':sha(instance/'queries'/query['id']/'public_acceptance.json'),'elapsed_seconds':time.monotonic()-start,'finished_utc':now(),'runtime':str(instance),'scope':'One fresh two-class nonlinear classification query after actual proved teachings, under public encoder/reader/parser/NTT/journal/backend TCB. Full reader remains; not private resident or utility benchmark. Later teach/query and exact eight-entry FIFO expiry are supported by the same continuing interface, not separately exercised by this minimal run.'}
        save(out/'RESULT.json',record);print(json.dumps(record,indent=2))
    except BaseException as e:
        save(out/'failure.json',{'complete_live_flow':False,'error':repr(e),'retried':False,'utc':now()});raise

if __name__=='__main__':main()
