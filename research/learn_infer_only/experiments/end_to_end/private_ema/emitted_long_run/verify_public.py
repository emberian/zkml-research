"""Independent complete public-record/storage verification before private drain."""
import datetime
from collections import Counter
from common import *


def main():
    frozen=verify_freeze();closed=load(REPORTS/'public_phase.json');fixture=load(FIXTURE)['events']
    assert closed['completed'] is True and not (REPORTS/'failure.json').exists()
    assert closed['freeze_sha256']==sha(ROOT/'freeze.json') and closed['reader_invocations']==0
    for entry in closed['transcripts'].values():assert meta(entry['path'])==entry
    operations=lines(REPORTS/'operations.jsonl');events=lines(REPORTS/'events.jsonl');pairs=lines(REPORTS/'replays.jsonl')
    assert len(operations)==1364 and len(events)==len(pairs)==480
    assert Counter(row['role'] for row in operations)=={'host':960,'issuer':404}
    cache=dict(frozen['files']);artifacts={}
    def current(path):
        path=str(path)
        if path not in cache:cache[path]=meta(path)
        return cache[path]
    for i,operation in enumerate(operations):
        assert operation['index']==i and operation['returncode']==0 and operation['timed_out'] is False
        assert operation['binary_before']==operation['binary_after']==current(operation['command'][0])
        assert operation['public_inputs_before']==operation['public_inputs_after']
        assert all(row==current(row['path']) for row in operation['public_inputs_before'])
        assert operation['runtime_environment']=={'RAYON_NUM_THREADS':'1'}
        output=operation['output'];assert output==current(output['path'])
        assert output['path'] not in artifacts;artifacts[output['path']]=output
        assert Path(output['path']).parent==RUNTIME/'public'
        command=operation['command']
        if operation['role']=='host':
            assert len(command)==7 and command[0]==str(HOST) and command[1]=='host' and command[-1]==output['path']
            assert operation['public_inputs_before']==[current(p) for p in command[2:6]]
            report=operation['reported'];plan=report['fft_plan_observation']
            assert plan['actual_plan_debug']==EXPECTED_PLAN and plan['expected_plan_matched'] is True
            assert plan['polynomial_size']==1024 and plan['fourier_size']==512
            assert report['client_key_read'] is False and report['all_output_bits_encrypted'] is True
            learn=report['operation']=='learn';assert report['operation'] in ['learn','infer']
            assert command[2]==str(FORMAL/f'artifacts/{report["operation"]}.json') and command[3]==str(SK)
            assert report['gate_api_calls']==({'xor':342,'and':196,'trivial_encrypt':2} if learn else {'xor':6,'and':3,'trivial_encrypt':2})
            envelope_check(output['path'],1 if learn else 4,32 if learn else 1)
        else:
            assert len(command)==5 and command[0]==str(ISSUER) and command[2]==str(PK) and command[-1]==output['path']
            kind,count={'init':(1,32),'learn':(2,10),'query':(3,2)}[command[1]]
            envelope_check(output['path'],kind,count)
    assert Counter(o['reported']['operation'] for o in operations if o['role']=='issuer')=={'init':4,'learn':384,'query':16}
    assert len(closed['initials'])==4
    initials={(r['history_id'],r['route']):r['state'] for r in closed['initials']}
    assert set(initials)=={(hid,route) for hid in [67000,67001] for route in [0,1]}
    for (hid,route),state in initials.items():assert state==current(RUNTIME/'public'/f'initial_{hid}_{route}.ct')
    assert len(closed['query_artifacts'])==16
    parents={};current_history=None;checkpoints=[]
    for expected,event,pair in zip(fixture,events,pairs):
        for key in ['event_id','event_ordinal','history_id','history_index','kind','learn_step','phase','route','record_id']:
            assert event[key]==expected[key]
        if expected['history_id']!=current_history:
            current_history=expected['history_id'];parents={str(r):initials[current_history,r] for r in [0,1]}
        assert event['parents_before']==parents
        route=str(expected['route']);name=expected['event_id'];learn=expected['kind']=='Learn'
        assert pair['event_id']==name and pair['kind']==expected['kind']
        assert pair['complete_output_bytes_equal'] and pair['inputs_equal_across_invocations'] and pair['same_observed_plan']
        left,right=operations[pair['primary_operation']],operations[pair['replay_operation']]
        assert left['name']==name+'.primary' and right['name']==name+'.replay'
        assert left['reported']['operation']==right['reported']['operation']==expected['kind'].lower()
        assert left['output']['path']==str(RUNTIME/'public'/f'{name}.ct') and right['output']['path']==str(RUNTIME/'public'/f'{name}.replay.ct')
        assert left['public_inputs_before']==right['public_inputs_before']
        assert left['wrapper_pid']==pair['primary_process'] and right['wrapper_pid']==pair['replay_process'] and pair['primary_process']!=pair['replay_process']
        assert left['command'][4]==parents[route]['path']
        request=(RUNTIME/'public'/f'{name}.input.ct') if learn else Path(closed['query_artifacts'][str(expected['record_id'])]['path'])
        assert event['request']==current(request) and left['command'][5]==str(request)
        assert pair['primary']==left['output']==event['output']==current(pair['primary']['path'])
        assert pair['replay']==right['output']==current(pair['replay']['path'])
        assert Path(pair['primary']['path']).read_bytes()==Path(pair['replay']['path']).read_bytes()
        if learn:parents[route]=event['output']
        assert event['parents_after']==parents
        if learn and expected['learn_step'] in [64,128,192]:checkpoints.append({'history_id':current_history,'phase':expected['phase'],'states':dict(parents)})
    assert checkpoints==closed['checkpoints']
    assert set(str(p) for p in (RUNTIME/'public').iterdir())==set(artifacts)
    save(REPORTS/'public_storage.json',{'claim':'EXECUTED','artifacts':[artifacts[p] for p in sorted(artifacts)],'artifact_count':len(artifacts)})
    report={'passed':True,'claim':'EXECUTED','verified_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
            'public_phase_sha256':sha(REPORTS/'public_phase.json'),'events':480,'replay_pairs':480,'host_processes':960,
            'issuer_processes':404,'artifacts_verified':len(artifacts),'all_plans_match':True,'all_storage_hashes_match':True,
            'all_recorded_inputs_binary_hashes_stable':True,'all_replay_bytes_equal':True,'fixture_order_and_state_continuity_match':True,
            'reader_invocations':0,'private_files_read':False,'frozen_sources_match':True}
    save(REPORTS/'public_verification.json',report)
    sealed=[REPORTS/'public_phase.json',REPORTS/'public_verification.json',REPORTS/'public_storage.json',
            REPORTS/'operations.jsonl',REPORTS/'events.jsonl',REPORTS/'replays.jsonl']
    save(REPORTS/'public_seal.json',{'claim':'EXECUTED','public_complete_and_verified':True,
         'sealed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reader_invocations':0,
         'freeze_sha256':sha(ROOT/'freeze.json'),'records':[meta(p) for p in sealed]})
    print(__import__('json').dumps(report),flush=True)


if __name__=='__main__':main()
