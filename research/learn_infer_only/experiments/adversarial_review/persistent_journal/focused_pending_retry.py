"""Benign process check: concurrent exact retries after install, before publication.

Executes the frozen repaired protocol, never the original runner. Output stays
under this review. The SQLite recipient lock is a test scheduling aid, not a
protocol component or an OS-isolation claim.
"""
from concurrent.futures import ThreadPoolExecutor
from contextlib import closing
import copy,hashlib,importlib.util,json,os,shutil,signal,socket,sqlite3,subprocess,sys,tempfile,threading,time,traceback
from pathlib import Path
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parent
PROTOCOL=ROOT/'run005_protocol.py';FIXTURE=ROOT/'run005_fixture.json'
spec=importlib.util.spec_from_file_location('reviewed_protocol',PROTOCOL)
protocol=importlib.util.module_from_spec(spec);spec.loader.exec_module(protocol)
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
save=lambda p,x:Path(p).write_text(json.dumps(x,indent=2)+'\n')

def snapshot(path,role):
    with closing(sqlite3.connect(f'file:{path}?mode=ro',uri=True)) as db:
        db.row_factory=sqlite3.Row
        result={'integrity':db.execute('PRAGMA integrity_check').fetchone()[0]}
        tables=['meta','journal'] if role=='authority' else ['deliveries','attempts']
        for table in tables:
            result[table]=[dict(row) for row in db.execute('SELECT * FROM '+table)]
        for rows in (result[t] for t in tables):
            for row in rows:
                for field in ['state_bytes','budget','nonce','request','packet','installed_state']:
                    if field in row:row[field]=json.loads(row[field])
        return result

def reverse_keys(value):
    if isinstance(value,dict):return {k:reverse_keys(v) for k,v in reversed(list(value.items()))}
    if isinstance(value,list):return [reverse_keys(v) for v in value]
    return value

def main():
    directory=ROOT/'focused_results';directory.mkdir(exist_ok=True)
    out=directory/f"run_{len(list(directory.glob('run_*')))+1:03}";out.mkdir()
    sockets=Path(tempfile.mkdtemp(prefix='mmaj-review-',dir='/tmp'))
    fixture=json.loads(FIXTURE.read_text());adb=out/'authority.sqlite3';rdb=out/'recipient.sqlite3'
    protocol.initialize_authority(adb,fixture);protocol.initialize_recipient(rdb)
    commands=[];processes=[];result={'passed':False,'source_sha256':{'protocol':sha(PROTOCOL),'fixture':sha(FIXTURE),'script':sha(__file__)},'commands':commands}
    def spawn(role,sock,tag,failpoint=None):
        cmd=[sys.executable,str(PROTOCOL),'serve',role,'--socket',str(sock),'--database',str(adb if role=='authority' else rdb)]
        if role=='authority':cmd+=['--recipient',str(sockets/'recipient'),'--fixture',str(FIXTURE)]
        if failpoint:cmd+=['--test-failpoint',failpoint,'--test-crash-marker',str(out/'kill_marker.json')]
        with (out/(tag+'.stdout')).open('w') as stdout,(out/(tag+'.stderr')).open('w') as stderr:
            p=subprocess.Popen(cmd,cwd=ROOT,stdout=stdout,stderr=stderr)
        row={'command':cmd,'pid':p.pid,'started_ns':time.time_ns(),'stdout':tag+'.stdout','stderr':tag+'.stderr'}
        p.record=row;commands.append(row);processes.append(p)
        deadline=time.monotonic()+10
        while not (out/(tag+'.stdout')).read_text().strip():
            if p.poll() is not None:raise RuntimeError(f'{tag} startup exit {p.returncode}')
            if time.monotonic()>deadline:raise TimeoutError(tag)
            time.sleep(.01)
        return p
    def finish(p):
        p.record.update(exit_code=p.wait(timeout=15),finished_ns=time.time_ns())
        return p.returncode
    def both(name):
        state={'authority':snapshot(adb,'authority'),'recipient':snapshot(rdb,'recipient')}
        save(out/(name+'.json'),state);return state
    try:
        recipient=spawn('recipient',sockets/'recipient','recipient')
        first=spawn('authority',sockets/'first','authority_before_kill','after_commit_before_publication')
        try:
            protocol.rpc(sockets/'first',{'request':fixture['primary']})
            raise AssertionError('Expected actual authority process death')
        except (EOFError,ConnectionResetError,BrokenPipeError):pass
        assert finish(first)==-signal.SIGKILL
        marker=json.loads((out/'kill_marker.json').read_text());assert marker['pid']==first.pid
        before=both('installed_unpublished')
        assert before['authority']['meta'][0]['head']==len(before['authority']['journal'])==1
        assert before['authority']['journal'][0]['published']==0
        assert before['recipient']['deliveries']==before['recipient']['attempts']==[]
        worker1=spawn('authority',sockets/'one','authority_worker_one')
        worker2=spawn('authority',sockets/'two','authority_worker_two')
        gate=threading.Barrier(9)
        def retry(index):
            gate.wait(timeout=10);started=time.time_ns()
            answer=protocol.rpc(sockets/('one' if index%2==0 else 'two'),{'request':fixture['primary']})
            return {'index':index,'thread_id':threading.get_ident(),'started_ns':started,'finished_ns':time.time_ns(),'answer':answer}
        # Keep the recipient's write transaction unavailable until all eight
        # client threads start, so pending publications can overlap. This does
        # not instrument or replace either role's actual request handler.
        with closing(sqlite3.connect(rdb,isolation_level=None)) as lock:
            lock.execute('BEGIN IMMEDIATE')
            with ThreadPoolExecutor(max_workers=8) as pool:
                pending=[pool.submit(retry,i) for i in range(8)]
                gate.wait(timeout=10);lock_started=time.time_ns();time.sleep(1)
                lock.execute('COMMIT');lock_released=time.time_ns()
                replies=[p.result(timeout=20) for p in pending]
        save(out/'concurrent_replies.json',replies)
        after=both('after_concurrent_retry')
        meta=after['authority']['meta'][0];journal=after['authority']['journal']
        assert meta['head']==len(journal)==1 and meta['state_bytes']==[1] and set(meta['budget'].values())=={9}
        assert journal[0]['published']==1 and journal[0]['packet']==fixture['primary']['intent']['event']
        attempts=after['recipient']['attempts'];assert len(after['recipient']['deliveries'])==1
        assert len(attempts)>=2 and len(attempts)<=8
        assert sum(x['outcome']=='stored' for x in attempts)==1
        assert all(x['outcome'] in ['stored','duplicateSamePacket'] for x in attempts)
        assert all(r['answer']['status']=='replayed' and r['answer']['packet']==journal[0]['packet'] for r in replies)
        # Canonical JSON identity ignores wire key ordering, as documented.
        reordered=json.dumps({'request':reverse_keys(fixture['primary'])})+'\n'
        with socket.socket(socket.AF_UNIX,socket.SOCK_STREAM) as s:
            s.settimeout(15);s.connect(str(sockets/'one'));s.sendall(reordered.encode())
            with s.makefile('rb') as stream:semantic_reply=json.loads(stream.readline())
        assert semantic_reply['status']=='replayed' and semantic_reply['publication']=='alreadyPublished'
        changed=copy.deepcopy(fixture['primary']);changed['context']['recipient']+=1
        mismatch=protocol.rpc(sockets/'two',{'request':changed})
        stale=protocol.rpc(sockets/'one',{'request':fixture['racing']})
        assert mismatch=={'status':'rejected','reason':'transactionConflict'}
        assert stale=={'status':'rejected','reason':'stalePrefix'}
        assert both('after_exact_and_mismatched_retry')==after
        nonce=fixture['primary']['intent']['nullifiers'][0]
        duplicate=protocol.rpc(sockets/'recipient',{'nonce':nonce,'transaction_id':91,'packet':fixture['primary']['intent']['event']})
        conflict=protocol.rpc(sockets/'recipient',{'nonce':nonce,'transaction_id':92,'packet':fixture['racing']['intent']['event']})
        assert duplicate=={'status':'duplicateSamePacket'} and conflict=={'status':'conflictingPacket'}
        final=both('after_recipient_duplicate_and_conflict')
        assert final['authority']==after['authority'] and final['recipient']['deliveries']==after['recipient']['deliveries']
        assert len(final['recipient']['attempts'])==len(attempts)+2
        result.update(passed=True,authority_worker_pids=[worker1.pid,worker2.pid],shared_authority_database=str(adb),
          concurrent_exact_retry_count=8,logical_installations=1,logical_recipient_deliveries=1,
          concurrent_publication_attempts=len(attempts),recipient_lock_ns=[lock_started,lock_released],
          canonical_wire_reorder_reply=semantic_reply,changed_same_txid_reply=mismatch,different_txid_same_nonce_reply=stale,
          direct_recipient_duplicate_reply=duplicate,direct_recipient_conflict_reply=conflict,
          scope='Actual local role processes with same-user SQLite; eight client threads, one scheduled overlap, no power-loss or physical exactly-once claim')
    except Exception:
        result['error']=traceback.format_exc();raise
    finally:
        for p in processes:
            if p.poll() is None:p.terminate()
            finish(p)
        shutil.rmtree(sockets)
        result['sources_unchanged']=result['source_sha256']=={'protocol':sha(PROTOCOL),'fixture':sha(FIXTURE),'script':sha(__file__)}
        save(out/'report.json',result)
        print(json.dumps(result,indent=2))

if __name__=='__main__':main()
