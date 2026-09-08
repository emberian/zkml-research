"""Authorized primary-state/sign private drain after the complete public seal."""
import datetime
import json
import os
import subprocess
import signal
import time
from common import *


def main():
    os.umask(0o077);frozen=verify_freeze();seal=load(REPORTS/'public_seal.json');verified=load(REPORTS/'public_verification.json')
    assert seal['public_complete_and_verified'] and verified['passed'] and not (REPORTS/'failure.json').exists()
    for row in seal['records']:assert meta(row['path'])==row
    assert seal['freeze_sha256']==sha(ROOT/'freeze.json') and verified['public_phase_sha256']==sha(REPORTS/'public_phase.json')
    for row in load(REPORTS/'public_storage.json')['artifacts']:assert meta(row['path'])==row
    cutoff=datetime.datetime.fromisoformat(load(REPORTS/'started.json')['cutoff_utc'])
    private=RUNTIME/'private/audit';private.mkdir(exist_ok=False,mode=0o700)
    opened=0;checks=[];initial_checks=[];final_correct=all_correct=0;start=time.perf_counter()
    operations=(REPORTS/'reader_operations.jsonl').open('x')
    started=datetime.datetime.now(datetime.timezone.utc).isoformat();seal_hash=sha(REPORTS/'public_seal.json')
    actual={e['event_id']:e for e in lines(REPORTS/'events.jsonl')}
    try:
        def read(name,kind,path):
            nonlocal opened
            remaining=(cutoff-datetime.datetime.now(datetime.timezone.utc)).total_seconds()
            assert remaining>0,'drain deadline reached; no further reader calls'
            assert meta(READER)==frozen['files'][str(READER)]
            target=private/f'{name}.json';assert not target.exists()
            command=[str(READER),kind,str(CK),str(path),str(target)]
            begin=time.perf_counter()
            process=subprocess.Popen(command,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
            timed_out=False
            try:stdout,stderr=process.communicate(timeout=min(30,remaining))
            except subprocess.TimeoutExpired:
                timed_out=True;os.killpg(process.pid,signal.SIGKILL);stdout,stderr=process.communicate()
            record={'name':name,'command':command,'returncode':process.returncode,'wall_seconds':time.perf_counter()-begin,
                    'timed_out':timed_out,'stdout':stdout.decode(),'stderr':stderr.decode(),'ciphertext':meta(path)}
            if process.returncode==0:record['reported']=json.loads(stdout)
            append(operations,record);opened+=1
            assert process.returncode==0 and not timed_out,f'{name}: reader failed; no retry'
            assert target.stat().st_mode&0o777==0o600
            return load(target)
        for initial in load(REPORTS/'public_phase.json')['initials']:
            name=f'initial_{initial["history_id"]}_{initial["route"]}'
            matches=read(name,'state',initial['state']['path'])['state']==[0,0,0,0]
            initial_checks.append({'history_id':initial['history_id'],'route':initial['route'],'matches':matches})
            assert matches,f'{name}: initial oracle mismatch'
        for event in load(FIXTURE)['events']:
            name=event['event_id'];learn=event['kind']=='Learn';path=actual[name]['output']['path']
            got=read(name,'state' if learn else 'output',path)
            matches=got['state']==event['state_after'][event['route']] if learn else got['negative']==(event['ema_score']<0)
            checks.append({'event_id':name,'kind':event['kind'],'primary_only':True,'matches_frozen_oracle':matches})
            assert matches,f'{name}: primary plaintext oracle mismatch'
            if not learn:
                correct=(-1 if got['negative'] else 1)==event['target'];all_correct+=int(correct)
                if event['phase']==3:final_correct+=int(correct)
        assert opened==484 and len(checks)==480
        save(REPORTS/'private_drain.json',{'passed':True,'claim':'EXECUTED','started_utc':started,
             'finished_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'wall_seconds':time.perf_counter()-start,
             'public_seal_sha256_before_drain':seal_hash,'reader_invocations':opened,'initial_checks':initial_checks,'event_checks':checks,
             'primary_learn_state_checks':384,'primary_infer_sign_checks':96,'independent_replay_plaintext_checks':0,
             'all_match':True,'final_correct':final_correct,'final_queries':32,'all_checkpoint_correct':all_correct,'all_checkpoint_queries':96,
             'full_reader_client_key_retained':True,'plaintext_values_reported_publicly':False})
        print(json.dumps({'private_drain_passed':True,'reader_invocations':opened,'final_correct':final_correct,'final_queries':32}),flush=True)
    except BaseException as error:
        save(REPORTS/'failure.json',{'phase':'private_drain','error':repr(error),'reader_invocations':opened,
             'initial_checks':initial_checks,'event_checks':checks,'private_plaintext_values_reported':False,'no_retry':True})
        raise
    finally:operations.close()


if __name__=='__main__':main()
