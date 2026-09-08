"""New public encrypted chains only; no reader invocation or audit decode."""
import datetime
import json
import os
import platform
import signal
import subprocess
import time
from pathlib import Path
from common import *


def main():
    os.umask(0o077)
    frozen=verify_freeze(); fixture=load(FIXTURE); start=time.perf_counter()
    utc=datetime.datetime.now(datetime.timezone.utc)
    cutoff=min(utc+datetime.timedelta(hours=6),datetime.datetime(2026,9,8,15,tzinfo=datetime.timezone.utc))
    assert cutoff>utc, 'public deadline already passed'
    RUNTIME.mkdir(parents=True,exist_ok=False);REPORTS.mkdir(parents=True,exist_ok=False)
    public=RUNTIME/'public';private=RUNTIME/'private';public.mkdir();private.mkdir(mode=0o700)
    streams={name:(REPORTS/f'{name}.jsonl').open('x') for name in ['operations','events','replays']}
    operation_count=event_count=pair_count=0;initials=[];checkpoints=[]
    save(REPORTS/'started.json',{'started_utc':utc.isoformat(),'cutoff_utc':cutoff.isoformat(),'pid':os.getpid(),
         'freeze_sha256':sha(ROOT/'freeze.json'),'platform':platform.platform(),'host_concurrency':1,
         'runtime_environment':{'RAYON_NUM_THREADS':'1'},'public_keys':{'public_key':meta(PK),'server_key':meta(SK)},
         'client_key_custody':'retained at prior private reader path, not copied/read/hashed in public phase'})

    def progress(current=None,phase='public'):
        row={'completed_events':event_count,'complete_replay_pairs':pair_count,'operations':operation_count,
             'current_operation':current,'phase':phase,'elapsed_seconds':time.perf_counter()-start,
             'updated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'reader_invocations':0,
             'public_phase_closed':False}
        save(REPORTS/'progress.json',row);return row

    def execute(name,executable,args,inputs,output,host=False):
        nonlocal operation_count
        remaining=(cutoff-datetime.datetime.now(datetime.timezone.utc)).total_seconds()
        assert remaining>0,'public deadline reached'
        assert not output.exists(), 'new output path already exists'
        before=[meta(path) for path in inputs];binary_before=meta(executable)
        assert binary_before==frozen['files'][str(executable)]
        argv=[str(executable),*map(str,args)]
        resource=RUNTIME/'last_resource.txt';prefix=['/usr/bin/time','-l','-o',str(resource)]
        env=os.environ.copy();env['RAYON_NUM_THREADS']='1'
        progress(name);began=time.perf_counter()
        process=subprocess.Popen(prefix+argv,stdout=subprocess.PIPE,stderr=subprocess.PIPE,env=env,start_new_session=True)
        timeout=False
        try: stdout,stderr=process.communicate(timeout=min(600,remaining))
        except subprocess.TimeoutExpired:
            timeout=True;os.killpg(process.pid,signal.SIGKILL);stdout,stderr=process.communicate()
        elapsed=time.perf_counter()-began;after=[meta(path) for path in inputs];binary_after=meta(executable)
        row={'index':operation_count,'name':name,'role':'host' if host else 'issuer','command':argv,
             'wrapper_pid':process.pid,'returncode':process.returncode,'timed_out':timeout,'wall_seconds':elapsed,
             'stdout':stdout.decode(),'stderr':stderr.decode(),'resource_report':resource.read_text(),
             'public_inputs_before':before,'public_inputs_after':after,'binary_before':binary_before,'binary_after':binary_after,
             'runtime_environment':{'RAYON_NUM_THREADS':'1'}}
        if process.returncode==0:row['reported']=json.loads(stdout)
        if output.exists():row['output']=meta(output)
        append(streams['operations'],row);operation_count+=1
        assert not timeout and process.returncode==0,f'{name}: public process failed; no retry'
        assert before==after and binary_before==binary_after,f'{name}: public input/binary hash changed'
        if host:
            observed=row['reported']['fft_plan_observation']
            assert observed['actual_plan_debug']==EXPECTED_PLAN and observed['expected_plan_matched'] is True
            assert observed['polynomial_size']==1024 and observed['fourier_size']==512
            assert row['reported']['all_output_bits_encrypted'] is True and row['reported']['client_key_read'] is False
        return row

    def issue(name,kind,text,path):
        request=private/f'{name}.txt';request.write_text(text)
        execute(name,ISSUER,[kind,PK,request,path],[PK],path)

    def pair(event,parents,request):
        nonlocal pair_count
        name=event['event_id'];op=event['kind'].lower();schedule=FORMAL/f'artifacts/{op}.json'
        parent=parents[event['route']];reads=[schedule,SK,parent,request]
        output=public/f'{name}.ct';replay=public/f'{name}.replay.ct'
        left=execute(name+'.primary',HOST,['host',*reads,output],reads,output,True)
        right=execute(name+'.replay',HOST,['host',*reads,replay],reads,replay,True)
        equal=output.read_bytes()==replay.read_bytes()
        row={'event_id':name,'kind':event['kind'],'primary_operation':left['index'],'replay_operation':right['index'],
             'inputs_equal_across_invocations':left['public_inputs_before']==right['public_inputs_before'],
             'complete_output_bytes_equal':equal,'primary':meta(output),'replay':meta(replay),
             'primary_process':left['wrapper_pid'],'replay_process':right['wrapper_pid'],
             'same_observed_plan':left['reported']['fft_plan_observation']==right['reported']['fft_plan_observation']}
        append(streams['replays'],row);pair_count+=1
        assert equal and row['inputs_equal_across_invocations'] and row['same_observed_plan'],f'{name}: replay mismatch; no retry'
        assert left['wrapper_pid']!=right['wrapper_pid']
        envelope_check(output,1 if op=='learn' else 4,32 if op=='learn' else 1)
        return output

    try:
        queries={}
        for event in fixture['events']:
            if event['kind']=='Infer' and event['record_id'] not in queries:
                rid=event['record_id'];path=public/f'query_{rid}.ct'
                issue(f'query_{rid}','query',str(event['bin'])+'\n',path);queries[rid]=path
                envelope_check(path,3,2)
        history=None;parents={}
        for event in fixture['events']:
            if event['history_id']!=history:
                history=event['history_id'];parents={}
                for route in [0,1]:
                    path=public/f'initial_{history}_{route}.ct'
                    issue(f'initial_{history}_{route}','init','',path);envelope_check(path,1,32)
                    parents[route]=path;initials.append({'history_id':history,'route':route,'state':meta(path)})
            before={route:meta(path) for route,path in parents.items()}
            if event['kind']=='Learn':
                request=public/f'{event["event_id"]}.input.ct'
                issue(event['event_id']+'.issue','learn',f'{event["bin"]} {event["u"]}\n',request)
                envelope_check(request,2,10)
            else:request=queries[event['record_id']]
            output=pair(event,parents,request)
            if event['kind']=='Learn':parents[event['route']]=output
            after={route:meta(path) for route,path in parents.items()}
            assert all(before[route]==after[route] for route in [0,1] if event['kind']=='Infer' or route!=event['route'])
            row={k:event[k] for k in ['event_id','event_ordinal','history_id','history_index','kind','learn_step','phase','route','record_id']}
            row.update({'parents_before':before,'parents_after':after,'request':meta(request),'output':meta(output)})
            append(streams['events'],row);event_count+=1
            if event['kind']=='Learn' and event['learn_step'] in [64,128,192]:
                checkpoints.append({'history_id':history,'phase':event['phase'],'states':after})
            print(json.dumps(progress(event['event_id'])),flush=True)
        assert event_count==pair_count==480 and operation_count==1364
        for stream in streams.values():stream.close()
        verify_freeze()
        save(REPORTS/'public_phase.json',{'completed':True,'started_utc':utc.isoformat(),
             'closed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'wall_seconds':time.perf_counter()-start,
             'counts':{'Learn':384,'Infer':96,'replay_pairs':480,'host_invocations':960,'issuer_invocations':404},
             'transcripts':{name:meta(REPORTS/f'{name}.jsonl') for name in streams},'initials':initials,'checkpoints':checkpoints,
             'query_artifacts':{str(rid):meta(path) for rid,path in queries.items()},'reader_invocations':0,
             'freeze_sha256':sha(ROOT/'freeze.json')})
        progress(phase='public_closed');print(json.dumps({'public_phase_closed':True,'events':480}),flush=True)
    except BaseException as error:
        save(REPORTS/'failure.json',{'phase':'public','error':repr(error),'completed_events':event_count,
             'replay_records':pair_count,'operations':operation_count,'reader_invocations':0,
             'elapsed_seconds':time.perf_counter()-start,'private_drain_executed':False})
        raise
    finally:
        for stream in streams.values():
            if not stream.closed:stream.close()


if __name__=='__main__':main()
