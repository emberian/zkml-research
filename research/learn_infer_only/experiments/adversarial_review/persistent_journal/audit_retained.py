"""Independent census of frozen run004 logical evidence; never opens its live SQLite files."""
from collections import Counter
import argparse
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parent
SOURCE=ROOT.parents[1]/'durable_integration/persistent_journal'

def load(p):return json.loads(Path(p).read_text())
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def arg(command,name):return command[command.index(name)+1]
def main(run_id='004'):
    RUN=SOURCE/('results/run_'+run_id)
    report=load(RUN/'report.json');fixture=load(ROOT/'run004_fixture.json');commands=report['commands']
    assert report['status']=='passed' and report['inputs_unchanged']
    for name in ['protocol.py','run.py','fixture.json']:
        assert sha(ROOT/('run'+run_id+'_'+name))==report['source_sha256'][str((SOURCE/name).resolve())]
    exported=load(SOURCE/'export_01.json');assert exported['exit_code']==0
    assert json.loads(exported['stdout'])==fixture and all(fixture['checked'].values())
    pids=[c['pid'] for c in commands];assert len(set(pids))==len(pids)==122
    roles=Counter();exits=Counter();nonempty_errors=[]
    for c in commands:
        cmd=c['command'];role=cmd[3] if cmd[2]=='serve' else 'client'
        roles[role]+=1;exits[str(c['exit_code'])]+=1
        for key in ['stdout','stderr']:assert (RUN/c[key]).is_file()
        if (RUN/c['stderr']).stat().st_size:nonempty_errors.append(c['stderr'])
    bypid={c['pid']:c for c in commands}
    crash_rows=[]
    expectations={'before_reservation':(0,0,1),'after_install_before_commit':(0,0,1),
      'after_commit_before_publication':(1,0,1),'after_publication_before_client_ack':(1,1,2)}
    for name,(installed,published,attempts) in expectations.items():
        before=load(RUN/name/'after_actual_process_kill.json');after=load(RUN/name/'after_exact_retry.json')
        marker=load(RUN/name/(name+'.marker.json'));c=bypid[marker['pid']]
        assert marker['stage']==name and marker['signal']=='SIGKILL' and c['exit_code']==-9
        assert c['started_ns']<=marker['time_ns']<=c['finished_ns']
        assert before['authority']['meta']['head']==len(before['authority']['journal'])==installed
        assert len(before['recipient']['deliveries'])==published
        assert after['authority']['meta']['head']==len(after['authority']['journal'])==1
        assert after['authority']['meta']['state_root']==1 and after['authority']['meta']['state_bytes']==[1]
        assert set(after['authority']['meta']['budget'].values())=={9}
        assert len(after['recipient']['deliveries'])==1 and len(after['recipient']['attempts'])==attempts
        assert after['recipient']['deliveries'][0]['packet']==fixture['primary']['intent']['event']
        crash_rows.append({'case':name,'actual_killed_pid':marker['pid'],'exit_code':-9,
          'before_journal':installed,'before_recipient':published,'after_attempts':attempts})
    races=[]
    for row in report['races']:
        workers=[bypid[pid] for pid in row['authority_worker_pids']];clients=[bypid[pid] for pid in row['client_pids']]
        assert len(workers)==2 and workers[0]['pid']!=workers[1]['pid']
        dbpaths=[arg(c['command'],'--database') for c in workers];assert dbpaths[0]==dbpaths[1]
        sockets=[arg(c['command'],'--socket') for c in workers];assert len(set(sockets))==2
        assert {arg(c['command'],'--socket') for c in clients}==set(sockets)
        barriers=[arg(c['command'],'--barrier') for c in clients];assert len(set(barriers))==1
        a=load(RUN/row['case']/'after_two_process_race.json')
        assert a['authority']['meta']['head']==len(a['authority']['journal'])==1
        assert a['authority']['meta']['state_root']==1 and set(a['authority']['meta']['budget'].values())=={9}
        assert len(a['recipient']['deliveries'])==1 and a['authority']['journal'][0]['txid']==row['winner']
        replies=[load(RUN/row['case']/(f'client{i}.json'))['answer'] for i in [1,2]]
        assert sorted(x['status'] for x in replies)==['accepted','rejected']
        races.append({'case':row['case'],'shared_database':dbpaths[0],'distinct_worker_pids':[c['pid'] for c in workers],
           'winner':row['winner'],'loser_reason':row['loser_reason']})
    case=RUN/'retry_and_exact_packet';responses=[load(case/f'client{i}.json')['answer'] for i in range(1,26)]
    assert responses[0]['status']=='accepted'
    assert all(x['status']=='replayed' for x in responses[1:9])
    assert all(x=={'status':'rejected','reason':'transactionConflict'} for x in responses[9:])
    snapshot=load(case/'after_retries_and_mutations.json')
    assert len(snapshot['authority']['journal'])==len(snapshot['recipient']['deliveries'])==len(snapshot['recipient']['attempts'])==1
    host=RUN/'host_restore_only';before=load(host/'before_host_restore.json');restored=load(host/'after_host_restore.json');after=load(host/'after_restore_retry.json')
    assert restored['host']['sequence']==0 and restored['authority']==before['authority']
    assert before['authority']==after['authority'] and before['recipient']==after['recipient']
    rollback=RUN/'authority_rollback_negative_control';one=load(rollback/'first_committed_history.json');two=load(rollback/'second_committed_history.json')
    x=one['authority']['journal'][0];y=two['authority']['journal'][0]
    assert x['nonce']==y['nonce'] and x['txid']!=y['txid'] and x['packet']!=y['packet']
    assert x['packet']['canonical_bytes']==y['packet']['canonical_bytes']
    assert x['installed_state']==y['installed_state']==[1]
    assert two['recipient']['deliveries']==one['recipient']['deliveries']
    assert two['recipient']['attempts'][-1]['outcome']=='conflictingPacket'
    broken=load(RUN/'broken_publish_before_commit/orphan_packet_after_uncommitted_publish.json')
    assert len(broken['authority']['journal'])==0 and len(broken['recipient']['deliveries'])==1
    hook_refusal=None
    if run_id=='005':
        hook_refusal=load(case/'fault_channel_refusal.json')
        assert hook_refusal=={'status':'rejected','reason':'unsupportedRequestFields'}
        refused=load(case/'client_fault_mode_refused.json')
        assert refused['authority']['meta']['head']==len(refused['authority']['journal'])==0
        assert refused['recipient']['deliveries']==refused['recipient']['attempts']==[]
        assert not (case/'untrusted_host/forged_crash_marker.json').exists()
        for command in commands:
            cmd=command['command']
            if cmd[2]=='client':assert '--failpoint' not in cmd and '--crash-marker' not in cmd
        for row in crash_rows:
            cmd=bypid[row['actual_killed_pid']]['command']
            assert arg(cmd,'--test-failpoint')==row['case']
    result={'passed':True,'report_sha256':sha(RUN/'report.json'),'commands':len(commands),'roles':dict(roles),
      'exit_codes':dict(exits),'nonempty_stderr_files':nonempty_errors,'normal_crash_cases':crash_rows,
      'race_count':len(races),'races':races,'mutation_count':16,'concurrent_published_retries':8,
      'rollback_scope':'distinct transaction/event envelopes; identical canonical bytes and installed state',
      'fixture_matches_export_stdout':True,'run_id':run_id,'normal_client_fault_field_refusal':hook_refusal,
      'scope':'independent review of retained logical evidence, not OS/power-loss or cryptographic verification',
      'script_sha256':sha(__file__)}
    output='retained_audit.json' if run_id=='004' else 'retained_audit_run005.json'
    (ROOT/output).write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--run',choices=['004','005'],default='004')
    main(p.parse_args().run)
