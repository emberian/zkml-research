"""Independently parse issued vectors, audit saved run, exercise score comparator."""
import hashlib, json, math, subprocess
from collections import deque, Counter
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[4]
def sha(p): return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def command(argv):
    r=subprocess.run(argv,text=True,capture_output=True)
    assert r.returncode==0,(argv,r.stderr)
    return r.stdout.strip()
def summary(values):
    values=sorted(values)
    return {'count':len(values),'sum_ns':sum(values),'min_ns':min(values),'max_ns':max(values),
        'median_ns':(values[(len(values)-1)//2]+values[len(values)//2])/2,
        'p95_nearest_rank_ns':values[math.ceil(.95*len(values))-1]}

def main():
    manifest=json.loads((HERE/'fixture_manifest.json').read_text())
    assert sha(HERE/'fixture.txt')==manifest['fixture_sha256']
    assert sha(HERE/'PREREGISTRATION.md')==manifest['preregistration_sha256']
    for p,h in manifest['source_sha256'].items(): assert sha(p)==h,p
    fixture=(HERE/'fixture.txt').read_text().splitlines()
    assert fixture[0]=='Q83_WINDOW_V1 577 32 2'
    expected={};checkpoints={};seen_histories=[];queries=manifest['query_ids']
    for line in fixture[1:]:
        x=line.split();kind=x[0];v=list(map(int,x[1:])) if kind!='END' else []
        if kind=='H':
            history,coin=v;seen_histories.append(history);queues=[deque(),deque()]
            states=[[0]*577 for _ in range(2)];step=0
            assert (history,coin) in [(63000,201),(63001,202)]
        elif kind=='L':
            phase,n,route,rid,y,*z=v;step+=1
            assert n==step and phase==(n-1)//64+1 and len(z)==577
            assert y in [-1,1] and all(abs(a)<=127 for a in z)
            queues[route].append(z)
            states[route]=[a+b for a,b in zip(states[route],z)]
            if len(queues[route])>32:
                old=queues[route].popleft();states[route]=[a-b for a,b in zip(states[route],old)]
        elif kind=='P':
            phase,route,count,*st=v
            assert step==phase*64 and count==len(queues[route]) and st==states[route]
            checkpoints[(history,phase,route)]=(count,st)
        elif kind=='Q':
            phase,rid,route,score,target,*q=v
            assert step==phase*64 and rid in queries and len(q)==577
            assert all(abs(a)<=127 for a in q)
            assert score==sum(a*b for a,b in zip(states[route],q))
            expected[(history,phase,rid)]=(route,score,target,len(queues[route])>0)
        elif kind=='END': assert step==192
        else: raise AssertionError(kind)
    assert seen_histories==[63000,63001] and len(expected)==96 and len(checkpoints)==12
    rows=[json.loads(s) for s in (HERE/'run_01.jsonl').read_text().splitlines()]
    assert (HERE/'run_01.stderr').read_text()==''
    assert rows[-1]=={'kind':'complete','histories':2,'pass':True}
    qr=[r for r in rows if r['kind']=='query'];lr=[r for r in rows if r['kind']=='learn']
    cr=[r for r in rows if r['kind']=='checkpoint'];sr=[r for r in rows if r['kind']=='summary']
    assert len(qr)==96 and len(lr)==384 and len(cr)==12 and len(sr)==2
    assert len({(r['history'],r['phase'],r['record']) for r in qr})==96
    for r in qr:
        route,score,target,encrypted=expected[(r['history'],r['phase'],r['record'])]
        assert (r['route'],r['expected'],r['decrypted_signed'],r['target'],r['encrypted'])==(route,score,score,target,encrypted)
        assert r['exact'] and r['prediction']==(1 if score>=0 else -1)
    for r in cr:
        count,st=checkpoints[(r['history'],r['phase'],r['route'])]
        assert r['queue']==count and r['empty']==(count==0)
        assert r['exact_queue'] and r['all_coefficients_equal']
        assert r['serialized_queue_and_acc_bytes']==(count+1)*85022 if count else r['serialized_queue_and_acc_bytes']==0
    # A false reference must be detected by the actual decrypted-score comparator.
    # This alters only the expected score, never the query, encryption or host state.
    corrupted=fixture.copy()
    for i,s in enumerate(corrupted):
        if s.startswith('Q '):
            x=s.split();x[4]=str(int(x[4])+1);corrupted[i]=' '.join(x);break
    bad=HERE/'comparator_falsifier.txt';bad.write_text('\n'.join(corrupted)+'\n')
    binary=HERE/'target/release/resident-bfv-window-83-probe'
    negative_argv=[str(binary),str(bad)]
    negative=subprocess.run(negative_argv,text=True,capture_output=True)
    (HERE/'comparator_falsifier.jsonl').write_text(negative.stdout)
    (HERE/'comparator_falsifier.stderr').write_text(negative.stderr)
    assert negative.returncode!=0 and 'declared query' in negative.stderr
    encrypted=[r for r in qr if r['encrypted']]
    evictions=[r for r in lr if r['evicted']]
    timings={
        'issuer_encode':summary([r['encode_ns'] for r in lr]),
        'issuer_encrypt':summary([r['encrypt_ns'] for r in lr]),
        'issuer_encode_and_encrypt':summary([r['encode_ns']+r['encrypt_ns'] for r in lr]),
        'input_serialize':summary([r['serialize_ns'] for r in lr]),
        'host_learn_add':summary([r['host_add_ns'] for r in lr]),
        'host_expiry_only_when_evicted':summary([r['host_expiry_ns'] for r in evictions]),
        'host_learn_add_and_expiry':summary([r['host_add_ns']+r['host_expiry_ns'] for r in lr]),
        'public_query_encode':summary([r['encode_ns'] for r in encrypted]),
        'host_query_two_products_and_sub':summary([r['host_ns'] for r in encrypted]),
        'public_query_encode_and_host':summary([r['encode_ns']+r['host_ns'] for r in encrypted]),
        'whole_polynomial_reader':summary([r['reader_ns'] for r in encrypted]),
        'answer_serialize':summary([r['serialize_ns'] for r in encrypted])}
    library=Path('/Users/ember/dev/breadstuffs/vendor/fhe-dregg')
    files=command(['rg','--files',str(library)]).splitlines()
    source_files={str(Path(p).relative_to(library)):sha(p) for p in files
                  if p.endswith('.rs') or Path(p).name in ['Cargo.toml','Cargo.lock']}
    source_tree_digest=hashlib.sha256(json.dumps(source_files,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    commands={
      'fixture':{'argv':['research/learn_infer_only/experiments/adaptation_utility/.venv/bin/python',str(HERE/'build_fixture.py')],
                 'exit_code':0,'log':'build_fixture.log'},
      'build_01':{'command':'CARGO_TARGET_DIR=research/learn_infer_only/experiments/adaptation_utility/encrypted_window/target cargo build --offline --locked --release --manifest-path research/learn_infer_only/experiments/adaptation_utility/encrypted_window/probe/Cargo.toml',
                  'exit_code':101,'log':'build_01.log','reason':'Rust cast comparison needed parentheses; fixed before first execution'},
      'build_02':{'command':'CARGO_TARGET_DIR=research/learn_infer_only/experiments/adaptation_utility/encrypted_window/target cargo build --offline --locked --release --manifest-path research/learn_infer_only/experiments/adaptation_utility/encrypted_window/probe/Cargo.toml',
                  'exit_code':0,'log':'build_02.log'},
      'run_01':{'argv':[str(binary),str(HERE/'fixture.txt')],'exit_code':0,
                'stdout':'run_01.jsonl','stderr':'run_01.stderr'},
      'comparator_falsifier':{'argv':negative_argv,'exit_code':negative.returncode,
                'stdout':'comparator_falsifier.jsonl','stderr':'comparator_falsifier.stderr'}}
    result={'claim_label':'EXECUTED','scope':'actual BFV arithmetic integration, full-key plaintext test reader',
        'exact_primary_comparisons':96,'actual_encrypted_readouts':80,'public_empty_route_zeros':16,
        'exact_nonempty_ciphertext_queue_checks':10,'structural_empty_queue_checks':2,
        'full_polynomial_coefficients_checked_per_nonempty_checkpoint':4096,
        'learn_encryptions':384,'host_learn_additions':384,'host_expiry_subtractions':256,
        'query_ciphertext_plaintext_products':160,'query_ciphertext_subtractions':80,
        'rotations':0,'relinearizations':0,'ciphertext_ciphertext_products':0,'keyswitch_special_primes':0,
        'history_summaries':sr,'timing_ns':timings,
        'timing_scope':'one fixed run, per-event samples on shared Apple M2 Max; no benchmark confidence claim',
        'host_persistent_ciphertexts_peak':66,'host_live_named_ciphertexts_during_update_peak':67,
        'host_persistent_serialized_bytes_peak':5611452,'public_key_serialized_bytes':42547,
        'host_persistent_raw_RNS_bytes':66*2*4096*2*8,
        'serialized_input_bytes_total':sum(r['input_bytes'] for r in sr),
        'serialized_output_bytes_total':sum(r['output_bytes'] for r in sr),
        'memory_scope':'serialized objects/raw RNS payload only; excludes allocator, parameters, NTT tables, keys, oracle, temporary plaintext and model caches',
        'comparator_falsifier':{'detected':True,'exit_code':negative.returncode,'sha256':sha(bad),
            'scope':'expected score changed by +1; exercises comparator, not a malicious-input rejection mechanism'},
        'environment':{'rustc':command(['rustc','-Vv']),'cargo':command(['cargo','-V']),
            'architecture':command(['uname','-m']),'cpu':command(['sysctl','-n','machdep.cpu.brand_string']),
            'breadstuffs_head':command(['git','-C','/Users/ember/dev/breadstuffs','rev-parse','HEAD'])},
        'library_source_files_sha256':source_files,'library_source_manifest_sha256':source_tree_digest,
        'source_sha256':manifest['source_sha256'],'commands':commands,
        'checks':{'independent_python_integer_replay':True,'frozen_inputs_unchanged':True,
                  'original_train_and_predict_compatible':manifest['checks'],'all_primary_pass':True},
        'residuals':['public deterministic key/encryption coins and full secret key retained for test',
            'whole polynomial decryption, no restricted sign release','issuer and cached features are plaintext',
            'no input authenticity, descriptor receipt or continuity integration','two histories are correctness fixtures, not a new utility estimate',
            'no PQ security bits claim','no complete Rust noise-proof refinement']}
    (HERE/'results.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'pass':True,'encrypted_queries':80,'structural_zero_queries':16,
        'comparator_falsifier_exit':negative.returncode,'timing_ns':timings},sort_keys=True))

if __name__=='__main__': main()
