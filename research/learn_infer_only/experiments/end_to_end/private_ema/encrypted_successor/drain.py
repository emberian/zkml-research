"""Deferred private reader correctness drain; no host/issuer invocations."""
import datetime
import os
import subprocess
import time
from pathlib import Path
from common import ROOT,UTILITY,RUNTIME,REPORTS,BIN,load,save,sha,meta,lines,verify_freeze

def main():
    os.umask(0o077)
    freeze=verify_freeze();closed=load(REPORTS/'public_phase.json');verified=load(REPORTS/'public_verification.json')
    assert closed['completed'] and verified['passed'] and verified['closed_public_phase_sha256']==sha(REPORTS/'public_phase.json')
    for row in closed['public_transcripts'].values():assert meta(row['path'])==row
    assert not (REPORTS/'private_drain.json').exists()
    started=time.perf_counter();started_utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
    key=RUNTIME/'private/reader/client_key.bin';private=RUNTIME/'private/audit';private.mkdir(exist_ok=False)
    operations=[];output_checks=[];state_checks=[]
    fixture=load(UTILITY/'materialized_fixture.json')['events'];actual={e['event_id']:e for e in lines(REPORTS/'events.jsonl')}

    def read(name,kind,ct):
        assert meta(BIN/'reader')==freeze['files'][str(BIN/'reader')]
        target=private/(name+'.json')
        command=[str(BIN/'reader'),kind,str(key),str(ct),str(target)]
        t=time.perf_counter();r=subprocess.run(command,capture_output=True,text=True,timeout=30)
        entry={'name':name,'command':command,'exit_code':r.returncode,'wall_seconds':time.perf_counter()-t,
               'stdout':r.stdout,'stderr':r.stderr,'ciphertext':meta(ct)}
        assert r.returncode==0,(name,r.stderr)
        entry['reported']=__import__('json').loads(r.stdout);operations.append(entry)
        save(REPORTS/'reader_operations.json',operations)
        assert target.stat().st_mode&0o777==0o600
        return load(target)

    for init in closed['initial_states']:
        got=read(f"initial_{init['history_id']}_{init['route']}",'state',init['state']['path'])
        matches=got['state']==[0,0,0,0]
        state_checks.append({'kind':'initial','history_id':init['history_id'],'route':init['route'],'matches':matches})
        assert matches
    for checkpoint in closed['checkpoints']:
        target=next(e for e in fixture if e['history_id']==checkpoint['history_id'] and e['kind']=='Learn' and e['learn_step']==64*checkpoint['phase'])
        for route in [0,1]:
            got=read(f"checkpoint_{checkpoint['history_id']}_{checkpoint['phase']}_{route}",'state',checkpoint['states'][str(route)]['path'])
            matches=got['state']==target['state_after'][route]
            state_checks.append({'kind':'checkpoint','history_id':checkpoint['history_id'],'phase':checkpoint['phase'],
                                 'route':route,'matches':matches})
            assert matches
    final_correct=final_queries=all_correct=0
    for e in fixture:
        if e['kind']!='Infer':continue
        got=read(e['event_id'],'output',actual[e['event_id']]['output']['path'])
        matches=got['negative']==(e['ema_score']<0)
        output_checks.append({'event_id':e['event_id'],'matches_frozen_oracle':matches})
        assert matches
        correct=(-1 if got['negative'] else 1)==e['target'];all_correct+=int(correct)
        if e['phase']==3:final_queries+=1;final_correct+=int(correct)
    assert len(output_checks)==96 and len(state_checks)==16 and final_queries==32
    for row in closed['public_transcripts'].values():assert meta(row['path'])==row
    verify_freeze()
    out={'passed':True,'started_utc':started_utc,'completed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
         'wall_seconds':time.perf_counter()-started,'public_phase_closed_before_drain':True,
         'public_phase_sha256':sha(REPORTS/'public_phase.json'),'public_verification_sha256':sha(REPORTS/'public_verification.json'),
         'reader_invocations':len(operations),'output_checks':output_checks,'state_checks':state_checks,
         'all_outputs_match':True,'all_initial_checkpoint_states_match':True,
         'selected_final_correct':final_correct,'selected_final_queries':final_queries,
         'all_checkpoint_correct':all_correct,'all_checkpoint_queries':96,
         'full_client_key_retained':True,'plaintext_audit_values_reported_publicly':False,
         'sources_unchanged':True,'public_transcripts_unchanged':True}
    save(REPORTS/'private_drain.json',out)
    print({k:v for k,v in out.items() if k not in ['output_checks','state_checks']})

if __name__=='__main__':main()
