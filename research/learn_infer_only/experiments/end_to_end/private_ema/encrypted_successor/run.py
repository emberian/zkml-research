"""Public cryptographic phase only. No reader invocation or plaintext comparison."""
import datetime
import json
import os
import platform
import signal
import subprocess
import time
from common import ROOT,UTILITY,RUNTIME,REPORTS,BIN,load,save,sha,meta,verify_freeze

def main():
    os.umask(0o077)
    freeze=verify_freeze();fixture=load(UTILITY/'materialized_fixture.json')
    started=time.perf_counter();start_utc=datetime.datetime.now(datetime.timezone.utc).isoformat()
    RUNTIME.mkdir(parents=True,exist_ok=False);REPORTS.mkdir(parents=True,exist_ok=False)
    public=RUNTIME/'public';private=RUNTIME/'private';public.mkdir();private.mkdir()
    operations=(REPORTS/'public_operations.jsonl').open('x')
    events=(REPORTS/'events.jsonl').open('x')
    pairs=(REPORTS/'replays.jsonl').open('x')
    opcount=paircount=eventcount=0
    checkpoints=[];initials=[]
    save(REPORTS/'started.json',{'started_utc':start_utc,'pid':os.getpid(),'freeze_sha256':sha(ROOT/'freeze.json'),
         'initial_projection_seconds':load(UTILITY/'encrypted_cost_proposal.json')['projected_wall_seconds'],
         'platform':platform.platform(),'python':platform.python_version(),
         'host_concurrency':1,'thread_environment':{k:os.environ.get(k) for k in ['RAYON_NUM_THREADS','OMP_NUM_THREADS']}})

    def append(stream,record):
        stream.write(json.dumps(record,sort_keys=True)+'\n');stream.flush();os.fsync(stream.fileno())

    def execute(name,binary,*args,host=False):
        nonlocal opcount
        assert time.perf_counter()-started<4*3600,'four-hour run bound'
        executable=BIN/binary
        binary_before=meta(executable)
        assert binary_before==freeze['files'][str(executable)]
        # The host ABI is op, server key, parent, encrypted request, output.
        inputs=[Path(p) for p in args[1:4]] if host else []
        before=[meta(p) for p in inputs]
        cmd=[str(executable),*map(str,args)]
        timefile=RUNTIME/'last_resource.txt'
        measured=['/usr/bin/time','-l','-o',str(timefile),*cmd]
        t=time.perf_counter()
        process=subprocess.Popen(measured,stdout=subprocess.PIPE,stderr=subprocess.PIPE,start_new_session=True)
        timed_out=False
        try:out,err=process.communicate(timeout=240)
        except subprocess.TimeoutExpired:
            timed_out=True;os.killpg(process.pid,signal.SIGKILL);out,err=process.communicate()
        wall=time.perf_counter()-t
        after=[meta(p) for p in inputs]
        binary_after=meta(executable)
        record={'index':opcount,'name':name,'binary':binary,'command':cmd,'wrapper_pid':process.pid,
                'exit_code':process.returncode,'timed_out':timed_out,'subprocess_wall_seconds':wall,
                'stdout':out.decode(),'stderr':err.decode(),'resource_report':timefile.read_text(),
                'public_read_inputs_before':before,'public_read_inputs_after':after,
                'binary_before':binary_before,'binary_after':binary_after}
        if process.returncode==0:record['reported']=json.loads(out)
        append(operations,record);opcount+=1
        assert not timed_out and process.returncode==0,(name,process.returncode)
        assert before==after and binary_before==binary_after,name
        if host:assert record['reported']['client_key_read'] is False
        return record

    def evaluate_pair(event,parents,request):
        nonlocal paircount
        op=event['kind'].lower();tag=event['event_id'];route=event['route']
        parent=parents[route]
        output=public/f'{tag}.ct';replay=public/f'{tag}.replay.ct'
        left=execute(tag+'.primary','host',op,sk,parent,request,output,host=True)
        right=execute(tag+'.replay','host',op,sk,parent,request,replay,host=True)
        equal=output.read_bytes()==replay.read_bytes()
        pair={'event_id':tag,'kind':event['kind'],'route':route,'primary_operation':left['index'],
              'replay_operation':right['index'],'public_read_inputs':left['public_read_inputs_before'],
              'inputs_equal_across_invocations':left['public_read_inputs_before']==right['public_read_inputs_before'],
              'complete_output_bytes_equal':equal,'primary':meta(output),'replay':meta(replay),
              'primary_process':left['wrapper_pid'],'replay_process':right['wrapper_pid']}
        append(pairs,pair);paircount+=1
        assert equal and pair['inputs_equal_across_invocations'] and pair['primary_process']!=pair['replay_process'],tag
        return output

    try:
        execute('setup','setup',public/'keys',private/'reader')
        pk=public/'keys/public_key.bin';sk=public/'keys/server_key.bin'
        save(REPORTS/'public_keys.json',{'public_key':meta(pk),'server_key':meta(sk),
             'client_key_bytes':(private/'reader/client_key.bin').stat().st_size,'client_key_retained':True})
        query_paths={}
        for e in fixture['events']:
            if e['kind']=='Infer' and e['record_id'] not in query_paths:
                rid=e['record_id'];request=private/f'query_{rid}.txt';request.write_text(str(e['bin'])+'\n')
                q=public/f'query_{rid}.ct';execute(f'query_{rid}','issuer','query',pk,request,q);query_paths[rid]=q
        parents={};current_history=None
        for e in fixture['events']:
            if e['history_id']!=current_history:
                current_history=e['history_id'];parents={}
                for route in [0,1]:
                    request=private/f'init_{current_history}_{route}.txt';request.write_text('')
                    ct=public/f'initial_{current_history}_{route}.ct'
                    execute(f'init_{current_history}_{route}','issuer','init',pk,request,ct)
                    parents[route]=ct;initials.append({'history_id':current_history,'route':route,'state':meta(ct)})
            before={r:meta(p) for r,p in parents.items()}
            if e['kind']=='Learn':
                request=private/(e['event_id']+'.txt');request.write_text(f"{e['bin']} {e['u']}\n")
                encrypted=public/(e['event_id']+'.input.ct')
                execute(e['event_id']+'.issue','issuer','learn',pk,request,encrypted)
            else:encrypted=query_paths[e['record_id']]
            output=evaluate_pair(e,parents,encrypted)
            if e['kind']=='Learn':parents[e['route']]=output
            after={r:meta(p) for r,p in parents.items()}
            if e['kind']=='Learn':assert before[1-e['route']]==after[1-e['route']]
            else:assert before==after
            public_event={k:e[k] for k in ['event_id','event_ordinal','history_id','history_index','kind','learn_step','phase','route','record_id']}
            public_event.update({'parents_before':before,'parents_after':after,'encrypted_request':meta(encrypted),'output':meta(output)})
            append(events,public_event);eventcount+=1
            if e['kind']=='Learn' and e['learn_step'] in [64,128,192]:
                checkpoints.append({'history_id':current_history,'phase':e['phase'],'states':after})
            elapsed=time.perf_counter()-started
            progress={'completed_events':eventcount,'complete_replay_pairs':paircount,'operations':opcount,
                      'last_event':e['event_id'],'elapsed_wall_seconds':elapsed,'updated_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
                      'public_phase_closed':False,'reader_invocations':0}
            save(REPORTS/'progress.json',progress)
            if eventcount<=2 or eventcount%16==0:print(json.dumps(progress),flush=True)
        assert eventcount==paircount==480
        operations.close();events.close();pairs.close()
        verify_freeze()
        save(REPORTS/'public_phase.json',{'completed':True,'started_utc':start_utc,
             'closed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'public_wall_seconds':time.perf_counter()-started,'counts':{'Learn':384,'Infer':96,'replay_pairs':480,'host_invocations':960},
             'public_transcripts':{p.name:meta(p) for p in [REPORTS/'public_operations.jsonl',REPORTS/'events.jsonl',REPORTS/'replays.jsonl']},
             'initial_states':initials,'checkpoints':checkpoints,'reader_invocations':0,'sources_unchanged':True,
             'freeze_sha256':sha(ROOT/'freeze.json')})
        print(json.dumps({'public_phase_closed':True,'events':eventcount,'wall_seconds':time.perf_counter()-started}),flush=True)
    except BaseException as error:
        save(REPORTS/'failure.json',{'error':repr(error),'completed_events':eventcount,'replays':paircount,
                                 'operations':opcount,'elapsed_seconds':time.perf_counter()-started,'private_drain_executed':False})
        raise
    finally:
        for stream in [operations,events,pairs]:
            if not stream.closed:stream.close()

from pathlib import Path
if __name__=='__main__':main()
