"""Compile the isolated candidate-independent horizon proposal, pin each command."""
import hashlib,json,os,subprocess,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
FORMAL=ROOT/'formal/horizon_composition'
COMPANION=Path('/Users/ember/dev/minidregg')
LEAN='/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean'
def main():
    envlog=json.loads((ROOT/'experiments/results/environment.json').read_text())
    paths=next(x['stdout'].strip() for x in envlog['checks'] if x['command']==['lake','env','printenv','LEAN_PATH'])
    name=sys.argv[1] if len(sys.argv)>1 else 'HorizonComposition'
    if name!='HorizonComposition':
        latest=json.loads(sorted(HERE.glob('compile_HorizonComposition_*.json'))[-1].read_text())
        dependency=FORMAL/'Theory/HorizonComposition.lean'
        assert latest['exit_code']==0 and latest['source_sha256']==hashlib.sha256(dependency.read_bytes()).hexdigest()
    output=FORMAL/'build/Theory'/(name+'.olean');output.parent.mkdir(parents=True,exist_ok=True)
    source=FORMAL/'Theory'/(name+'.lean')
    env=dict(os.environ,LEAN_PATH=str(FORMAL/'build')+':'+paths)
    digest=hashlib.sha256(source.read_bytes()).hexdigest()
    cmd=[LEAN,'-o',str(output),str(source)]
    p=subprocess.run(cmd,cwd=FORMAL,env=env,capture_output=True,text=True)
    assert hashlib.sha256(source.read_bytes()).hexdigest()==digest
    index=len(list(HERE.glob('compile_'+name+'_*.json')))+1
    record=dict(command=cmd,cwd=str(FORMAL),lean_path=env['LEAN_PATH'],source_sha256=digest,
        exit_code=p.returncode,stdout=p.stdout,stderr=p.stderr)
    (HERE/f'compile_{name}_{index:02}.json').write_text(json.dumps(record,indent=2)+'\n')
    print(p.stdout+p.stderr)
    return p.returncode
if __name__=='__main__':raise SystemExit(main())
