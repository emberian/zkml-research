"""One public-only replay of the already saved final nine-class live query."""
import hashlib,json,os,subprocess,time
from pathlib import Path
HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
def main():
 root=HERE/'models/bfv';out=HERE/'cached_replay_002';out.mkdir()
 records=[json.loads(x) for x in (root/'operations.jsonl').read_text().splitlines()]
 rows=[r for r in records if r.get('cached_public_host') and r['command']=='infer'][-9:]
 assert len(rows)==9 and len({r['arguments']['query'] for r in rows})==1
 binary=HERE/'crypto/target/release/kernel-crypto-cached';start=time.perf_counter()
 with (out/'host.stderr').open('w') as err:
  p=subprocess.Popen([str(binary),'serve','--dir',str(root)],stdin=subprocess.PIPE,stdout=subprocess.PIPE,stderr=err,text=True,bufsize=1,env=dict(os.environ,RAYON_NUM_THREADS='1'))
  try:
   ready=json.loads(p.stdout.readline());assert ready['ready'];ready_seconds=time.perf_counter()-start;results=[]
   for i,r in enumerate(rows):
    args=dict(r['arguments']);old=Path(args['out']);args['out']=str(out/f'{i:03}.ct')
    request={'command':'infer','arguments':args};t=time.perf_counter();p.stdin.write(json.dumps(request)+'\n');p.stdin.flush();answer=json.loads(p.stdout.readline());elapsed=time.perf_counter()-t
    assert answer['ok'];assert Path(args['out']).read_bytes()==old.read_bytes()
    results.append({'request':request,'result':answer['result'],'wall_seconds':elapsed,'previous_output':str(old),'output_bytes_equal':True,'input_hashes':{k:sha(args[k]) for k in ['acc','query']},'output_sha256':sha(old)})
   p.stdin.close();assert p.wait(timeout=10)==0
  finally:
   if p.poll() is None:
    p.terminate()
    try:p.wait(timeout=5)
    except subprocess.TimeoutExpired:p.kill();p.wait()
   p.stdout.close()
 result={'ok':True,'scope':'Public-only same-input replay; no model forward, encryption, teaching or private read. Same complete ciphertext bytes, nine final live query classes.','change':'Cache the fixed public plaintext prime instead of re-running generate_prime once per residue.','ready_seconds':ready_seconds,'nine_class_public_seconds':sum(r['wall_seconds'] for r in results),'wall_seconds':time.perf_counter()-start,'RAYON_NUM_THREADS':'1','binary_sha256':sha(binary),'source_sha256':sha(HERE/'crypto/src/cached.rs'),'baseline_source_sha256':sha(HERE/'crypto/src/main.rs'),'baseline_binary_sha256':sha(HERE/'crypto/target/release/kernel-crypto'),'ready':ready,'results':results}
 (out/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({k:v for k,v in result.items() if k not in ['ready','results']}))
if __name__=='__main__':main()
