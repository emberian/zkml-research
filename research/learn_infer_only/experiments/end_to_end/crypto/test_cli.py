"""Real process/file role tests. Private smoke artifacts are ignored and redacted."""
import hashlib,json,os,stat,subprocess,time
from collections import deque
from pathlib import Path
HERE=Path(__file__).resolve().parent
BASE=HERE.parents[2]
BIN=HERE/'target/release/resident-crypto'
FIXTURE=BASE/'experiments/adaptation_utility/encrypted_window/fixture.txt'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def dump(p,v,secret=False):
    p.write_text(json.dumps(v,separators=(',',':'),sort_keys=True))
    if secret:p.chmod(0o600)

def main():
    run=HERE/'runs'/('validation_'+str(time.time_ns()));run.mkdir(parents=True)
    public=run/'public';private=run/'private';public.mkdir();private.mkdir(mode=0o700)
    records=[]
    def call(command,*args,expected=0,redact=False):
        argv=[str(BIN),command,*map(str,args)];start=time.perf_counter_ns()
        p=subprocess.run(argv,cwd=public,capture_output=True,text=True)
        ns=time.perf_counter_ns()-start
        out=json.loads(p.stdout) if p.stdout else None
        error=json.loads(p.stderr) if p.stderr else None
        assert p.returncode==expected,(argv,p.returncode,p.stdout,p.stderr)
        record={'command':command,'argv':argv,'cwd':str(public),'exit_code':p.returncode,'wall_ns':ns}
        if redact:record['result']={'private_reader_result_omitted':True,'success':p.returncode==0}
        else:record['result']=out
        if error:record['error']=error
        if command.startswith('host-') and expected==0:
            assert '--sk' not in argv and '--vector' not in argv
            for j,a in enumerate(argv):
                if a in ['--acc','--fresh','--old','--query']:
                    path=Path(argv[j+1]);assert public in path.parents
        records.append(record);return out
    parameters=call('params')
    assert sha(FIXTURE)=='41978a10b974a3e8b7f30d5f9c66f7d396fdf7df83b723b3f14dc00359cdb4c0'
    lines=FIXTURE.read_text().splitlines();queries={};query_vectors={};results=[]
    adds=expiries=encrypted_queries=empty_queries=0
    for line in lines[1:]:
        x=line.split();tag=x[0]
        if tag=='H':
            history=int(x[1]);pk=public/f'{history}.pk';sk=private/f'{history}.sk';zero=public/f'{history}.zero'
            key=call('keygen','--pk',pk,'--sk',sk,'--zero',zero)
            assert stat.S_IMODE(sk.stat().st_mode)==0o600
            queues=[deque(),deque()];acc=[zero,zero];states=[[0]*577 for _ in range(2)]
        elif tag=='L':
            phase,step,route,rid,y=map(int,x[1:6]);z=list(map(int,x[6:]));adds+=1
            vector=private/f'{history}-{step}.vector.json';dump(vector,z,True)
            fresh=public/f'{history}-{step}.fresh';new=public/f'{history}-{step}.acc'
            call('issuer-encrypt','--pk',pk,'--vector',vector,'--out',fresh)
            args=['--acc',acc[route],'--fresh',fresh]
            queues[route].append((fresh,z));states[route]=[a+b for a,b in zip(states[route],z)]
            if len(queues[route])>32:
                old,oldz=queues[route].popleft();args+=['--old',old];expiries+=1
                states[route]=[a-b for a,b in zip(states[route],oldz)]
            host=call('host-learn',*args,'--out',new)
            recomputed=public/f'{history}-{step}.recomputed'
            authority=call('host-learn',*args,'--out',recomputed)
            assert host['sha256']==authority['sha256']==sha(new)==sha(recomputed)
            acc[route]=new
        elif tag=='P':
            phase,route,count=map(int,x[1:4]);assert count==len(queues[route])
            assert list(map(int,x[4:]))==states[route]
        elif tag=='Q':
            phase,rid,route,want,target=map(int,x[1:6]);q=list(map(int,x[6:]));assert want==sum(a*b for a,b in zip(states[route],q))
            if rid not in queries:
                vec=public/f'query-{rid}.vector.json';query=public/f'query-{rid}.json';dump(vec,q)
                call('encode-query','--vector',vec,'--out',query);queries[rid]=query;query_vectors[rid]=q
            else:assert query_vectors[rid]==q
            out=public/f'{history}-{phase}-{rid}.answer';out2=public/f'{history}-{phase}-{rid}.recomputed-answer'
            host=call('host-infer','--acc',acc[route],'--query',queries[rid],'--out',out)
            authority=call('host-infer','--acc',acc[route],'--query',queries[rid],'--out',out2)
            assert host['sha256']==authority['sha256']==sha(out)==sha(out2)
            reader=call('reader-decrypt','--sk',sk,'--ct',out)
            assert reader['signed_score']==want and reader['coefficient']==576
            is_empty=not queues[route];empty_queries+=is_empty;encrypted_queries+=not is_empty
            results.append({'history':history,'phase':phase,'record':rid,'exact':True,'score':want,'known_empty':is_empty})
        elif tag=='END':pass
        else:raise AssertionError(tag)
    assert (adds,expiries,encrypted_queries,empty_queries)==(384,256,80,16)

    # Fresh unknown synthetic inputs. Never record vectors/state or scalar results.
    pk=public/'private-smoke.pk';sk=private/'private-smoke.sk';zero=public/'private-smoke.zero'
    call('keygen','--pk',pk,'--sk',sk,'--zero',zero)
    q=[(i%5)-2 for i in range(577)];qv=public/'private-smoke-public-query-vector.json';dump(qv,q)
    query=public/'private-smoke-query.json';call('encode-query','--vector',qv,'--out',query)
    queue=deque();state=[0]*577;acc=zero;private_compares=0
    for step in range(1,41):
        vector=private/f'unknown-{step}.json';fresh=public/f'unknown-{step}.fresh';new=public/f'unknown-{step}.acc'
        call('issuer-private-vector','--out',vector);assert stat.S_IMODE(vector.stat().st_mode)==0o600
        z=json.loads(vector.read_text());state=[a+b for a,b in zip(state,z)]
        call('issuer-encrypt','--pk',pk,'--vector',vector,'--out',fresh)
        args=['--acc',acc,'--fresh',fresh];queue.append((fresh,z))
        if len(queue)>32:
            old,oldz=queue.popleft();args+=['--old',old];state=[a-b for a,b in zip(state,oldz)]
        host=call('host-learn',*args,'--out',new)
        check=public/f'unknown-{step}.recomputed';authority=call('host-learn',*args,'--out',check)
        assert host['sha256']==authority['sha256'];acc=new
        if step in [20,40]:
            out=public/f'unknown-{step}.answer';call('host-infer','--acc',acc,'--query',query,'--out',out)
            reader=call('reader-decrypt','--sk',sk,'--ct',out,redact=True)
            assert reader['signed_score']==sum(a*b for a,b in zip(state,q));private_compares+=1
    # New OS coins must change encryption of the same issuer input.
    duplicate=public/'unknown-40-again.fresh';call('issuer-encrypt','--pk',pk,'--vector',vector,'--out',duplicate)
    assert sha(duplicate)!=sha(fresh)

    # Refusal at the role/parser boundary, and permission check on exact retry.
    call('host-learn','--acc',acc,'--fresh',fresh,'--out',public/'rejected','--sk',sk,expected=2)
    call('issuer-encrypt','--pk',pk,'--vector',vector,'--out',public/'rejected','--seed','1',expected=2)
    for name,value in [('bool',[True]+[0]*576),('float',[1.0]+[0]*576),('range',[128]+[0]*576),
                       ('short',[0]*576),('long',[0]*578),('overflow',[2**100]+[0]*576)]:
        v=public/f'bad-{name}.json';dump(v,value)
        call('encode-query','--vector',v,'--out',public/'rejected',expected=2)
    # Deterministic issuer control uses PUBLIC KNOWN input, not unknown ingress:
    # publishing encryption coins would remove the latter's privacy premise.
    ov=public/'oracle-known-vector.json';dump(ov,[i%7-3 for i in range(577)])
    oa=public/'oracle-known-a.ct';ob=public/'oracle-known-b.ct'
    call('oracle-issuer-encrypt','--pk',pk,'--vector',ov,'--out',oa,'--seed','37')
    call('oracle-issuer-encrypt','--pk',pk,'--vector',ov,'--out',ob,'--seed','37')
    assert sha(oa)==sha(ob)
    original=sha(sk);sk.chmod(0o644)
    before=len(records)
    call('keygen','--pk',public/'permission-1.pk','--sk',sk,'--zero',public/'permission-1.zero',expected=2)
    assert 'private regular' in records[-1]['error']['error'] and sha(sk)==original
    sk.chmod(0o600);link=private/'key-symlink';link.symlink_to(sk)
    call('keygen','--pk',public/'permission-2.pk','--sk',link,'--zero',public/'permission-2.zero',expected=2)
    assert 'private regular' in records[-1]['error']['error']
    report={'classification':'executed separate process/file data-flow benchmark R',
        'source_sha256':sha(HERE/'src/main.rs'),'binary_sha256':sha(BIN),'cargo_lock_sha256':sha(HERE/'Cargo.lock'),
        'fixture_sha256':sha(FIXTURE),'parameters':parameters,'run_directory':str(run),
        'fixed_fixture':{'learns':adds,'expiries':expiries,'encrypted_state_readouts':encrypted_queries,
            'known_empty_state_readouts':empty_queries,'query_comparisons':results,'public_recomputation_exact':True},
        'private_ingress':{'new_os_random_contributions':40,'expiries':8,'private_score_comparisons':private_compares,
            'all_exact':True,'private_vectors_states_scores_in_log':False,'same_input_fresh_ct_inequality':True,
            'scope':'synthetic unknown inputs; no utility or operator-isolation claim'},
        'secret_retry_permission_controls':{'public_permissions_refused':True,'symlink_refused':True,
            'private_exact_retry':'covered by Rust save() unit test'},
        'oracle_issuer_existing_pk_bytes_reproduce':True,
        'host_argument_file_audit':{'host_receives_only_public_paths':True,'no_secret_key_or_private_vector_argument':True,
            'scope':'recorded successful host invocations; refusal control intentionally passes forbidden --sk'},
        'commands':records,'residuals':['full secret key in trusted reader','no finalized-envelope check in low-level CLI',
            'metadata keyID does not prove cryptographic key relation','issuer plaintext range/source assertion is not a ZK proof',
            'no operating-system isolation from common machine operator','no post-quantum security bit claim']}
    (HERE/'test_results.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'pass':True,'fixed_learns':adds,'fixed_score_checks':len(results),'private_learns':40,
        'private_score_checks':private_compares,'commands':len(records),'source_sha256':report['source_sha256']},sort_keys=True))

if __name__=='__main__':main()
