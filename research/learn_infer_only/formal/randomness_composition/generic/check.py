#!/usr/bin/env python3
"""Check the generic extension against the preserved combined integration overlay."""
from pathlib import Path
import hashlib,json,os,subprocess,sys,time

HERE=Path(__file__).resolve().parent
RESIDENT=HERE.parents[2]
INTEGRATION=RESIDENT/'experiments/integration'
DEPENDENCY=INTEGRATION/'results/run_002/report.json'
BUILD=HERE/'build'
RESULTS=HERE/'results'
LEAN='/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean'

def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()

def main():
    RESULTS.mkdir(exist_ok=True);BUILD.mkdir(exist_ok=True)
    dependency=json.loads(DEPENDENCY.read_text())
    assert dependency['status']=='passed'
    base=INTEGRATION/'build/run_002/olean'
    for folder,dirs,files in os.walk(base):
        target=BUILD/Path(folder).relative_to(base);target.mkdir(exist_ok=True)
        for filename in files:
            p=target/filename
            if not p.exists() and not p.is_symlink():p.symlink_to(Path(folder)/filename)
    env=dict(os.environ,LEAN_PATH=str(BUILD)+':'+dependency['lean_path'])
    for arg in sys.argv[1:]:
        source=HERE/arg;output=BUILD/Path(arg).with_suffix('.olean')
        output.parent.mkdir(parents=True,exist_ok=True)
        if output.is_symlink():raise RuntimeError('Refuse output through dependency symlink')
        before=digest(source);start=time.monotonic();cmd=[LEAN,'-o',str(output),str(source)]
        result=subprocess.run(cmd,cwd=HERE,env=env,text=True,capture_output=True)
        record=dict(command=cmd,cwd=str(HERE),lean_path=env['LEAN_PATH'],source_sha256_before=before,
                    source_sha256_after=digest(source),source=str(source),exit_code=result.returncode,
                    stdout=result.stdout,stderr=result.stderr,elapsed_seconds=time.monotonic()-start,
                    dependency_report=str(DEPENDENCY),dependency_report_sha256=digest(DEPENDENCY))
        if result.returncode==0:record['olean_sha256']=digest(output)
        n=len(list(RESULTS.glob(source.stem+'_*.json')))+1
        (RESULTS/f'{source.stem}_{n:02}.json').write_text(json.dumps(record,indent=2)+'\n')
        print(source.stem,result.returncode,result.stdout,result.stderr,flush=True)
        if result.returncode:return result.returncode
        assert before==digest(source)
    return 0

if __name__=='__main__':raise SystemExit(main())
