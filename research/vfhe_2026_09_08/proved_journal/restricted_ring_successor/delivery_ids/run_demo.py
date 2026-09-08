#!/usr/bin/env python3
"""One existing recipient, two deliveries; public accepted-prefix import only."""
import copy
import json
import shutil
import sqlite3
import time
from pathlib import Path
import delivery as d

s = d.s
HERE = Path(__file__).resolve().parent
SOURCE = HERE.parent
ORIGINAL = SOURCE / 'runtime/normal001'
EVIDENCE = SOURCE / 'results/normal001'

def initialize(root):
    root.mkdir(parents=True)
    for name in ('public','cas','logs','proposals'): (root/name).mkdir()
    for name in ('genesis.json','registry.json'): shutil.copyfile(ORIGINAL/name,root/name)
    for i in range(16):
        name='registration_%02d.ring'%i
        shutil.copyfile(ORIGINAL/'public'/name,root/'public'/name)
    service=s.Service(root)
    classes={c:{'state_sha256':None,'queue':[]} for c in service.genesis['classes']}
    state={'genesis':service.gid,'revision':0,'classes':classes,'model_root':s.model_root(classes),'last_receipt_sha256':None}
    db=s.connection(root)
    try:
        db.execute('CREATE TABLE head(id INTEGER PRIMARY KEY CHECK(id=1),body TEXT NOT NULL,sha256 TEXT NOT NULL)')
        db.execute('CREATE TABLE journal(revision INTEGER PRIMARY KEY,request_id TEXT UNIQUE NOT NULL,request_sha256 TEXT NOT NULL,receipt TEXT NOT NULL,receipt_sha256 TEXT NOT NULL)')
        db.execute('INSERT INTO head VALUES(1,?,?)',(s.canonical(state).decode(),s.digest(state)))
    finally: db.close()
    d.once(root/'delivery_credentials.json',{'genesis':service.gid,'credential_root':str(ORIGINAL),
        'scope':'Reuse this accepted setup only; original key is opened solely by its authorized recipient actor.'})
    return service

def import_accepted(service, records):
    # Trusted local checkpoint import. Does not substitute for new submit()
    # verification and does not claim a fresh arithmetic/proof execution.
    imported=[]
    for accepted in records:
        receipt=accepted['receipt']; request=receipt['request']
        s.need(accepted['status']=='accepted' and accepted['receipt_sha256']==s.digest(receipt),'import_accepted_receipt')
        s.need(receipt['all_candidate_bytes_equal'] is True and receipt['request_sha256']==s.digest(request),'import_prior_verification_record')
        state=service.head()['head']; service.binding(state,request)
        s.need(receipt['revision']==state['revision']+1,'import_revision')
        for field in ('input_sha256','fresh_sha256','candidate_sha256'):
            digest=request[field]; source=ORIGINAL/'cas'/digest
            s.need(s.sha(source)==digest,'import_original_public_cas')
            destination=service.root/'cas'/digest
            if not destination.exists(): shutil.copyfile(source,destination)
            service.cas(digest)
        new={'genesis':service.gid,'revision':receipt['revision'],'classes':service.next_classes(state,request),
             'model_root':request['next_model_root'],'last_receipt_sha256':accepted['receipt_sha256']}
        db=s.connection(service.root)
        try:
            db.execute('BEGIN IMMEDIATE'); s.need(service.head(db)['head']==state,'import_current_parent')
            db.execute('INSERT INTO journal VALUES(?,?,?,?,?)',(new['revision'],request['request_id'],s.digest(request),s.canonical(receipt).decode(),s.digest(receipt)))
            db.execute('UPDATE head SET body=?,sha256=? WHERE id=1',(s.canonical(new).decode(),s.digest(new)))
            db.execute('COMMIT')
        finally: db.close()
        imported.append({'revision':new['revision'],'receipt_sha256':s.digest(receipt),'head_sha256':s.digest(new)})
    return imported

def main():
    root=HERE/'runtime/demo001'; results=HERE/'results/demo001'
    assert not root.exists() and not results.exists(),'Sole bounded delivery demonstration already exists'
    results.mkdir(parents=True)
    started=time.monotonic()
    pinned=[SOURCE/'ring_service.py',SOURCE/'run_demo.py',EVIDENCE/'accepted_updates.json',EVIDENCE/'final_head.json',
            EVIDENCE/'recipient_00.json',ORIGINAL/'genesis.json',ORIGINAL/'registry.json',ORIGINAL/'journal.sqlite3']
    before={str(p):s.sha(p) for p in pinned}
    d.once(results/'LAUNCH.json',{'source_pins':before,'delivery_source_sha256':s.sha(HERE/'delivery.py'),
        'driver_sha256':s.sha(Path(__file__)),'workload':'Trusted public checkpoint4; recipient0 delivery; import accepted5/6; recipient0 delivery; exact retries/refusals; no new crypto setup/teach.'})
    records=s.read(EVIDENCE/'accepted_updates.json'); service=initialize(root)
    imports=import_accepted(service,records[:4]); service.audit()
    published4=service.publish()
    req4=d.make_request(root,0,'request-r4','delivery-r4',published4['models'])
    d.once(results/'request4.json',req4)
    result4=d.deliver(root,req4); assert result4['status']=='delivered'
    d.once(results/'delivery4.json',result4)
    retry4=d.deliver(root,req4); assert retry4['status']=='replayed' and retry4['receipt']==result4['receipt']
    d.once(results/'retry4.json',retry4)
    imports+=import_accepted(service,records[4:]); service.audit()
    final=service.head(); assert final==s.read(EVIDENCE/'final_head.json')
    published6=service.publish()
    req6=d.make_request(root,0,'request-r6','delivery-r6',published6['models'])
    d.once(results/'request6.json',req6)
    result6=d.deliver(root,req6); assert result6['status']=='delivered'
    d.once(results/'delivery6.json',result6)
    historical=d.deliver(root,req4); assert historical['status']=='replayed' and historical['receipt']==result4['receipt']
    d.once(results/'historical_retry4.json',historical)
    refusals=[]
    for name,request in [('same-request-new-delivery',{**req6,'delivery_id':'delivery-new'}),
                         ('same-delivery-new-request',{**req6,'request_id':'request-new'}),
                         ('old-head-fresh-ids',{**req4,'request_id':'request-stale','delivery_id':'delivery-stale'})]:
        try: d.deliver(root,request)
        except s.Refused as error: refusals.append({'case':name,'code':error.code})
        else: raise AssertionError('Expected exact delivery refusal')
    assert [r['code'] for r in refusals]==['delivery_id_or_request_conflict','delivery_id_or_request_conflict','delivery_not_current_head']
    fixture=s.read(EVIDENCE/'fixture.json')
    for got,expected in [(result4,fixture['snapshots'][1]),(result6,fixture['snapshots'][2])]:
        assert got['receipt']['query_results']==[{'revision':expected['revision'],'scores':expected['scores'][0],'prediction':expected['predictions'][0]}]
    assert service.head()==final
    assert all(s.sha(Path(p))==h for p,h in before.items())
    for delivery_id in ('delivery-r4','delivery-r6'):
        shutil.copytree(root/'deliveries'/delivery_id,results/delivery_id)
    d.once(results/'imports.json',imports); d.once(results/'refusals.json',refusals)
    d.once(results/'final_head.json',final)
    result={'status':'PASS','elapsed_seconds':time.monotonic()-started,'same_recipient_coordinate':0,
        'accepted_revisions_delivered':[4,6],'distinct_delivery_ids':['delivery-r4','delivery-r6'],
        'new_recipient_actor_invocations':2,'scalar_scores_matched':4,'decisions_matched':2,
        'exact_retries':2,'historical_retry_returns_original_receipt':True,'retry_actor_invocations':0,
        'conflicting_request_or_delivery_ids_refused':2,'fresh_stale_head_refused':True,
        'public_validations_before_each_recipient':True,'orchestrator_private_payload_reads':0,
        'new_setup_key_or_encode_runs':0,'new_update_recomputations':0,'frozen_source_and_runtime_pins_unchanged':True,
        'head_import_scope':'Trusted local transfer of prior accepted receipts, not new verification or new teachings',
        'crypto_scope':'Same existing registered recipient key; local delivery identity does not cryptographically bind its use to history.'}
    d.once(results/'RESULT.json',result)
    print(json.dumps(result,indent=2),flush=True)

if __name__=='__main__': main()
