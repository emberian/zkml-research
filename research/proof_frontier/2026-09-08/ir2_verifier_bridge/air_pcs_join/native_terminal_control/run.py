#!/usr/bin/env python3
"""One authorized native terminal control; no learner, setup, FHE encoding or private input."""
import hashlib,json,os,pathlib,resource,signal,subprocess,sys,time
if not __debug__:raise RuntimeError('Python -O unsupported')
HERE=pathlib.Path(__file__).resolve().parent
ROOT=pathlib.Path('/Users/ember/dev/zkml-research')
VFHE=ROOT/'research/vfhe_2026_09_08'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(1024*1024),b''):h.update(chunk)
    return h.hexdigest()
def main():
    if len(sys.argv)!=4:raise SystemExit('usage: run.py REPAIRED_TEMPLATE EXPECTED_SHA256 NEW_OUT')
    repaired=pathlib.Path(sys.argv[1]).resolve();out=pathlib.Path(sys.argv[3]).resolve()
    assert sha(repaired)==sys.argv[2]
    out.mkdir(parents=True,exist_ok=False)
    old=VFHE/'query_arithmetic/artifacts/template_ir2.json'
    public=VFHE/'proved_journal/fast_live_successor/results/fast001/class0/case/public_rows.json'
    trace=VFHE/'proved_journal/fast_live_successor/runtime/fast001/queries/new-two-class-query/proof0/generated/trace.leu32'
    binary=VFHE/'query_runtime/target/release/vfhe-native-terminal-control'
    watched=[old,repaired,public,trace,binary,HERE/'src/main.rs',HERE/'Cargo.toml',HERE/'Cargo.lock',HERE/'run.py',VFHE/'proved_operation/backend/src/lib.rs',pathlib.Path('/Users/ember/dev/breadstuffs/circuit/src/descriptor_ir2.rs')]
    pins={str(p):sha(p) for p in watched}
    argv=[str(p)for p in [binary,old,repaired,public,trace,out/'artifacts']]
    begin=time.monotonic();start=time.time()
    with (out/'stdout.json').open('w')as stdout,(out/'stderr.log').open('w')as stderr:
        p=subprocess.Popen(argv,stdout=stdout,stderr=stderr,start_new_session=True,env=dict(os.environ,RAYON_NUM_THREADS='4'))
        try:code=p.wait(timeout=300)
        except BaseException:
            os.killpg(p.pid,signal.SIGKILL);p.wait();raise
    wall=time.monotonic()-begin;r=resource.getrusage(resource.RUSAGE_CHILDREN)
    record={'argv':argv,'start_unix':start,'exit_code':code,'wall_seconds':wall,'user_seconds':r.ru_utime,'system_seconds':r.ru_stime,'max_rss_bytes':r.ru_maxrss if sys.platform=='darwin'else r.ru_maxrss*1024,'explicit_policy':{'RAYON_NUM_THREADS':'4'},'input_and_source_sha256':pins,'posthash_match':all(sha(pathlib.Path(p))==h for p,h in pins.items())}
    (out/'command.json').write_text(json.dumps(record,indent=2)+'\n')
    assert code==0 and record['posthash_match'],'control failed; see retained logs'
    result=json.loads((out/'artifacts/result.json').read_text())
    assert result['old_mutated_statement_native_verified'] and result['old_proof_repaired_statement_rejected']
    print(json.dumps({'passed':True,'wall_seconds':wall,'max_rss_bytes':record['max_rss_bytes'],'result_sha256':sha(out/'artifacts/result.json'),'old_native_proof_verified':True,'old_gate_accepts':result['gate_control']['old_native_main_gates_accept'],'repaired_gate_accepts':result['gate_control']['repaired_native_main_gates_accept'],'old_proof_repaired_statement_rejected':True}))
if __name__=='__main__':main()
