"""Trusted issuer frontend: private text -> live vector -> encrypted signed Learn.

The encoder's four-record numerical test is retained in results/run_001. This
wrapper composes that encoder with the existing journal issuer CLI. It does not
submit a host proposal or bypass authority verification/finality.
"""
import argparse,hashlib,json,os,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent;UTILITY=ROOT.parent
BASE=UTILITY.parents[1]/'adaptation_utility';JOURNAL=UTILITY.parent/'journal'
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()

def private_json(path,data):
    fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_TRUNC,0o600)
    with os.fdopen(fd,'w') as f:json.dump(data,f,indent=2);f.write('\n')
    os.chmod(path,0o600)

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for name in ['input','issuer-config','head','private-workdir','out','request-id','nonce','record-id']:
        p.add_argument('--'+name,required=True)
    p.add_argument('--expect-record-id',type=int,help='Optional exact cached-record comparison; omit for a new text')
    args=p.parse_args();data=load(args.input)
    if set(data)!={'text','route','label'} or not isinstance(data['text'],str):raise ValueError('input requires text, route, label only')
    if type(data['route']) is not int or data['route'] not in [0,1]:raise ValueError('route must be integer0 or1')
    if type(data['label']) is not int or data['label'] not in [-1,1]:raise ValueError('label must be integer-1 or+1')
    cfg=load(args.issuer_config)
    if cfg.get('role')!='issuer':raise ValueError('issuer configuration required')
    evidence=load(ROOT/'results/run_001/report.json')
    if not evidence['passed'] or not evidence['sources_unchanged']:raise ValueError('live encoder evidence is not green')
    for path in [UTILITY/'issuer_encode_prepared.py',UTILITY/'encoder_policy.json',UTILITY/'encoder_feasibility.json']:
        if sha(path)!=evidence['source_sha256'][str(path)]:raise ValueError('encoder source/policy differs from tested bytes')
    work=Path(args.private_workdir).resolve();work.mkdir(parents=True,mode=0o700,exist_ok=False);os.chmod(work,0o700)
    private_json(work/'input.json',data);vector=work/'vector.json'
    python=BASE/'.venv/bin/python'
    encoder=[str(python),'-B',str(UTILITY/'issuer_encode_prepared.py'),'--input',str(work/'input.json'),'--output',str(vector)]
    if args.expect_record_id is not None:encoder+=['--expect-record-id',str(args.expect_record_id)]
    issued=[sys.executable,'-B',str(JOURNAL/'roles.py'),'issue','--config',args.issuer_config,'--head',args.head,
      '--route',str(data['route']),'--request-id',args.request_id,'--nonce',args.nonce,'--record-id',args.record_id,
      '--vector',str(vector),'--out',args.out]
    runs=[]
    for name,command in [('live_encoder',encoder),('encrypted_signed_issuer',issued)]:
        start=time.perf_counter_ns();result=subprocess.run(command,capture_output=True,text=True,timeout=180)
        row={'stage':name,'command':command,'exit_code':result.returncode,'wall_ns':time.perf_counter_ns()-start,
             'stdout':result.stdout,'stderr':result.stderr};runs.append(row)
        private_json(work/'processes.json',runs)
        if result.returncode:
            print(json.dumps({'ok':False,'failed_stage':name,'exit_code':result.returncode,'details':'retained in issuer-only work directory'}))
            raise SystemExit(result.returncode)
    report={'ok':True,'dimension':577,'encoder_source_sha256':sha(UTILITY/'issuer_encode_prepared.py'),
      'encoder_policy_sha256':sha(UTILITY/'encoder_policy.json'),'journal_issuer_source_sha256':sha(JOURNAL/'roles.py'),
      'input_sha256':sha(work/'input.json'),'vector_sha256':sha(vector),
      'live_encoder_result':json.loads(runs[0]['stdout']),'issuer_result':json.loads(runs[1]['stdout']),
      'scope':'Trusted issuer only; resulting ciphertext/authorization still require host proposal and authority admission'}
    private_json(work/'report.json',report)
    print(json.dumps({'ok':True,'dimension':577,'issuer_result':report['issuer_result'],
      'encoder_wall_ns':runs[0]['wall_ns'],'issuer_wall_ns':runs[1]['wall_ns'],
      'scope':'Ciphertext and signed Learn produced; not yet submitted or finalized'}))

if __name__=='__main__':main()
