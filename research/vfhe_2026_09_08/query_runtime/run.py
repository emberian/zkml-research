#!/usr/bin/env python3
"""Generate and independently verify one complete class-query arithmetic proof.
No secret-key argument, no private reader, no retry. The service owns authorization
and checks its accepted parent again before any subsequent private receive.
"""
import argparse, datetime, hashlib, json, os, pathlib, resource, shlex, subprocess, sys, time
HERE=pathlib.Path(__file__).resolve().parent

def sha(path):
    h=hashlib.sha256()
    with pathlib.Path(path).open('rb') as f:
        for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
    return h.hexdigest()
def utc():return datetime.datetime.now(datetime.timezone.utc).isoformat()
def write(path,value):path.write_text(json.dumps(value,indent=2)+'\n')
def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ['acc','query','output','new_run']:ap.add_argument(name,type=pathlib.Path)
    a=ap.parse_args(); job=a.new_run.resolve();job.mkdir(parents=True,exist_ok=False)
    cfg=json.loads((HERE/'PIPELINE.json').read_text()); started=time.monotonic();steps=[]
    env=os.environ.copy();env['RAYON_NUM_THREADS']=str(cfg['rayon_threads'])
    def step(name,argv,cwd,timeout):
        record={'name':name,'argv':[str(x)for x in argv],'cwd':str(cwd),'started_utc':utc()}
        begin=time.monotonic();code=None
        try:
            with (job/(name+'.stdout')).open('xb')as out,(job/(name+'.stderr')).open('xb')as err:
                # Inherit the caller's process group. The surrounding gate owns
                # cancellation/quiescence for this entire public pipeline.
                completed=subprocess.run(record['argv'],cwd=cwd,env=env,stdout=out,stderr=err,timeout=timeout)
                code=completed.returncode
        finally:
            record.update(returncode=code,elapsed_seconds=time.monotonic()-begin,finished_utc=utc())
            steps.append(record);write(job/(name+'.command.json'),record)
        if code!=0:raise RuntimeError(f'{name} failed with exit {code}; see retained stderr; no retry')
        return record
    try:
        for path,pin in cfg['source_pins'].items():
            if sha(path)!=pin:raise RuntimeError(f'pinned source/artifact changed: {path}')
        inputs={'acc':a.acc.resolve(),'query':a.query.resolve(),'output':a.output.resolve()}
        input_pins={name:sha(path)for name,path in inputs.items()}
        case=job/'case'; generated=job/'generated';proof=job/'proof'
        step('export',[cfg['native'],'export',inputs['acc'],inputs['query'],inputs['output'],case],HERE,60)
        operation=json.loads((case/'operation.json').read_text())
        for name,key in [('acc','acc_sha256'),('query','query_sha256'),('output','out_sha256')]:
            if operation[key]!=input_pins[name]:raise RuntimeError(f'input changed while exporting: {name}')
        # Constant command syntax; only quoted fixed package paths are embedded.
        # User paths travel as positional arguments, never shell source.
        script=('exec env LEAN_PATH='+shlex.quote(cfg['arithmetic_root']+'/build')+':"$LEAN_PATH" lean --root='+shlex.quote(cfg['arithmetic_root'])+' --run '+shlex.quote(cfg['emitter'])+' "$1" "$2"')
        step('emit',['lake','env','bash','-c',script,'query-emit',generated,case/'public_rows.json'],cfg['lean_cwd'],900)
        if sha(generated/'template_ir2.json')!=cfg['template_sha256']:raise RuntimeError('generated template differs from approved arithmetic statement')
        emission=json.loads((generated/'emission.json').read_text())
        if emission['rows']!=cfg['rows']or emission['trace_width']!=cfg['trace_width']:raise RuntimeError('wrong generated trace dimensions')
        step('prove',[cfg['native'],'prove',cfg['template'],case,generated/'trace.leu32',proof],HERE,300)
        step('verify',[cfg['native'],'verify',cfg['template'],case,proof/'proof.bin'],HERE,60)
        proof_result=json.loads((proof/'proof.json').read_text());verification=json.loads((job/'verify.stdout').read_text())
        if not(proof_result['verified']and verification['verified']):raise RuntimeError('proof was not verified')
        for name,path in inputs.items():
            if sha(path)!=input_pins[name]:raise RuntimeError(f'input changed during pipeline: {name}')
        if sha(cfg['native'])!=cfg['source_pins'][cfg['native']]or sha(cfg['template'])!=cfg['template_sha256']:raise RuntimeError('native verifier/template changed during pipeline')
        result={'schema':'vfhe-whole-query-result-v1','verified':True,'case':str(case),'public_rows':str(case/'public_rows.json'),'proof':str(proof/'proof.bin'),'template':cfg['template'],'template_sha256':cfg['template_sha256'],'proof_sha256':sha(proof/'proof.bin'),'input_sha256':input_pins,'native':cfg['native'],'native_sha256':cfg['source_pins'][cfg['native']],'source_pins':cfg['source_pins'],'pipeline_source_sha256':sha(__file__),'pipeline_config_sha256':sha(HERE/'PIPELINE.json'),'operation':operation,'emission':emission,'proof_result':proof_result,'fresh_verification':verification,'steps':steps,'elapsed_seconds':time.monotonic()-started,'max_children_rss_bytes':resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss,'finished_utc':utc(),'private_files_read':0,'scope':'One complete class ciphertext query result; both signed products and final subtraction. Query parsing/NTT encoding and metadata/recipient/accepted-head checks remain TCB. This process does not authorize or perform private receive.'}
        write(job/'result.json',result);print(json.dumps(result));return 0
    except Exception as e:
        result={'schema':'vfhe-whole-query-result-v1','verified':False,'error':str(e),'steps':steps,'elapsed_seconds':time.monotonic()-started,'finished_utc':utc(),'no_retry':True}
        write(job/'result.json',result);print(json.dumps(result));return 1
if __name__=='__main__':sys.exit(main())
