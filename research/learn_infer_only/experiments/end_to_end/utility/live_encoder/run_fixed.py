"""Execute the original prepared encoder on four authorized fixed records."""
from pathlib import Path
import hashlib,json,os,re,subprocess,time
ROOT=Path(__file__).resolve().parent;UTILITY=ROOT.parent
BASE=UTILITY.parents[1]/'adaptation_utility'
load=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
save=lambda p,x:Path(p).write_text(json.dumps(x,indent=2)+'\n')

def private_json(path,value):
    fd=os.open(path,os.O_WRONLY|os.O_CREAT|os.O_TRUNC,0o600)
    with os.fdopen(fd,'w') as f:json.dump(value,f);f.write('\n')
    os.chmod(path,0o600)

def main():
    out=ROOT/'results';out.mkdir(exist_ok=True)
    run=out/f"run_{len(list(out.glob('run_*')))+1:03}";run.mkdir()
    private=UTILITY/'issuer_oracle/live_encoder'/run.name;private.mkdir(parents=True,mode=0o700)
    os.chmod(private,0o700)
    records=load(BASE/'representation_records.json')
    sources=[UTILITY/'issuer_encode_prepared.py',UTILITY/'encoder_policy.json',UTILITY/'encoder_feasibility.json',
      BASE/'representation_features.npz',BASE/'representation_records.json',BASE/'requirements-lock.txt',
      ROOT/'LIVE_PROTOCOL.md',Path(__file__),BASE/'encrypted_window/fixture.txt']
    before={str(p):sha(p) for p in sources};rows=[]
    for rid in [0,64,256,320]:
        r=records[rid];input_path=private/f'input_{rid}.json';vector_path=private/f'vector_{rid}.json'
        private_json(input_path,{'text':r['text'],'route':r['skill'],'label':1})
        command=['/usr/bin/time','-l',str(BASE/'.venv/bin/python'),'-B',str(UTILITY/'issuer_encode_prepared.py'),
          '--input',str(input_path),'--output',str(vector_path),'--expect-record-id',str(rid)]
        started=time.time_ns();p=subprocess.run(command,capture_output=True,text=True,timeout=90)
        finished=time.time_ns();(run/f'record_{rid}.stdout').write_text(p.stdout);(run/f'record_{rid}.stderr').write_text(p.stderr)
        match=re.search(r'(\d+)\s+maximum resident set size',p.stderr)
        times=re.search(r'([0-9.]+)\s+real\s+([0-9.]+)\s+user\s+([0-9.]+)\s+sys',p.stderr)
        row={'record_id':rid,'pool':r['pool'],'route':r['skill'],'command':command,'exit_code':p.returncode,
          'started_ns':started,'finished_ns':finished,'wrapper_wall_seconds':(finished-started)/1e9,
          'stdout_file':f'record_{rid}.stdout','stderr_file':f'record_{rid}.stderr'}
        if match:row['max_rss_bytes_macos']=int(match.group(1))
        if times:row['time_command']={'real_seconds':float(times.group(1)),'user_seconds':float(times.group(2)),'sys_seconds':float(times.group(3))}
        if p.returncode==0:
            row['encoder_result']=json.loads(p.stdout.strip());values=load(vector_path)
            assert len(values)==577 and all(type(v)==int and -127<=v<=127 for v in values)
            assert vector_path.stat().st_mode&0o777==0o600
            row.update(vector_sha256=sha(vector_path),input_sha256=sha(input_path),vector_mode='0600')
        rows.append(row)
        print(json.dumps({k:v for k,v in row.items() if k not in ['command','input_sha256','vector_sha256']},sort_keys=True),flush=True)
    after={str(p):sha(p) for p in sources}
    report={'passed':all(r['exit_code']==0 for r in rows),'records':[0,64,256,320],
      'source_sha256':before,'sources_unchanged':before==after,'commands':rows,
      'scope':'Four live trusted-issuer model executions; plaintext/vector paths excluded from host/authority roles',
      'model_runs':4,'backbone_training':False,'downloads':False,'new_dependencies':False,
      'original_e2e_fixture_unchanged':sha(BASE/'encrypted_window/fixture.txt')=='41978a10b974a3e8b7f30d5f9c66f7d396fdf7df83b723b3f14dc00359cdb4c0'}
    save(run/'report.json',report);print(json.dumps({'complete':True,'passed':report['passed'],'sources_unchanged':report['sources_unchanged']},indent=2))
    assert report['passed'] and report['sources_unchanged']

if __name__=='__main__':main()
