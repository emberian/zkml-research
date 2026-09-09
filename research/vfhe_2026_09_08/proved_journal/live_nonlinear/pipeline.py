#!/usr/bin/env python3
"""Caller-selected update and complete kernel proofs under one approved profile.
No saved case/proof is selected by configuration. All phase proofs are fresh.
"""
from pathlib import Path
import json
import os
import sys
import time
from common import ROOT, check_pins, command, now, save, sha

ENV = dict(os.environ, RAYON_NUM_THREADS='4', PYTHONDONTWRITEBYTECODE='1')
COUNT = {'update': 8, 'infer': 88, 'extension': 4, 'tensor': 18, 'rescale': 6}
ARITY = {'update': 97, 'infer': 97, 'extension': 84, 'tensor': 56, 'rescale': 88}


def read(path):
    return json.loads(Path(path).read_text())


def config():
    c = read(ROOT / 'PIPELINE.json')
    assert c['schema'] == 'live-nonlinear-approved-profile-v1'
    check_pins(c['pins'])
    return c


def profile(c, kind, i):
    key = 'mac' if kind in ('infer', 'update') else kind
    pi = (i % 8) // 2 if kind == 'infer' else i // 2 if kind in ('tensor', 'update') else 0
    return c['profiles'][key][pi]


def invoke(c, kind, action, i, case, proof_or_trace, out=None):
    p = profile(c, kind, i)
    native = c['native'][kind]
    if kind == 'infer':
        a = [native, action, c['linear_plan'], i, p['template'], case, proof_or_trace]
    elif kind in ('extension', 'tensor'):
        a = [native, action, kind, i, p['template'], case, proof_or_trace]
    else:
        a = [native, action, p['template'], case, i, proof_or_trace]
    return a + ([out] if out is not None else [])


def expected_chunks(kind, case):
    op = read(case / 'operation.json')
    rows = op['chunks']
    if kind in ('extension', 'tensor'):
        rows = [r for r in rows if r['kind'] == kind]
    assert len(rows) == COUNT[kind]
    for i, r in enumerate(rows):
        assert r.get('index', r.get('chunk')) == i and r['rows'] == 4096
        assert r.get('first_row', r.get('first_global_row')) == 4096*i
        assert r.get('end_row_exclusive', r.get('end_global_row_exclusive')) == 4096*(i+1)
        path = case / r.get('path', r.get('public_rows', ''))
        assert sha(path) == r['sha256']
        public = read(path)
        assert len(public) == 4096 and all(len(x) == ARITY[kind] and x[0] == i*4096+j for j,x in enumerate(public))
        yield i, r, path


def record_binding(kind, case, record):
    op = read(case / 'operation.json')
    if kind == 'rescale':
        assert record['source_trace_sha256'] == op['source_trace_sha256']
        assert record['output_ciphertext_sha256'] == op['output_ciphertext_sha256']
    else:
        assert record['binding'] == op['binding']


def check_record(c, kind, i, case, record, proof):
    assert record['verified'] is True and record['rows'] == 4096
    assert record.get('index', record.get('chunk')) == i
    assert record.get('first_row', record.get('first_global_row')) == i*4096
    assert record.get('end_row_exclusive', record.get('end_global_row_exclusive')) == (i+1)*4096
    assert record['proof_sha256'] == sha(proof)
    if 'template_sha256' in record:
        assert record['template_sha256'] == profile(c, kind, i)['template_sha256']
    if kind == 'infer':
        assert record['stage'] == i//8 and record['prime_index'] == (i%8)//2
    if kind in ('extension', 'tensor'):
        assert record['kind'] == kind
    record_binding(kind, case, record)


def generate(kind, case, out):
    c = config()
    case, out = Path(case).resolve(), Path(out).resolve()
    frozen = {str(p): sha(p) for p in case.rglob('*') if p.is_file()}
    chunks = list(expected_chunks(kind, case))
    out.mkdir()
    work = ROOT / 'work' / __import__('hashlib').sha256(str(out).encode()).hexdigest()[:24]
    work.mkdir(parents=True)
    save(out/'inputs.json', {'kind':kind, 'profile_sha256':sha(ROOT/'PIPELINE.json'),'case_pins':frozen,'started_utc':now()})
    started=time.monotonic(); result=[]
    try:
        for i, row, public in chunks:
            name=f'chunk{i:03}'; p=profile(c,kind,i); witness=work/name
            save(out/'progress.json', {'phase':'emit','kind':kind,'index':i,'completed':len(result),'utc':now()})
            emit=command(out,name+'-emit',[p['executor'],p['plan'],p['template'],public,witness],900,ENV)
            trace=witness/'trace.leu32'
            assert sha(witness/'template_ir2.json')==p['template_sha256']
            assert trace.stat().st_size==4096*p['width']*4
            raw_sha,raw_bytes=sha(trace),trace.stat().st_size
            save(out/'progress.json', {'phase':'prove','kind':kind,'index':i,'completed':len(result),'utc':now()})
            proving=command(out,name+'-prove',invoke(c,kind,'prove',i,case,trace,out/name),1800,ENV)
            proof=out/name/'proof.bin'; report=read(out/name/'proof.json')
            check_record(c,kind,i,case,report,proof)
            assert report['public_rows_sha256']==row['sha256']
            packed=trace.with_suffix('.leu32.zst')
            compression=command(out,name+'-compress',[c['zstd'],'-T1','-3','--no-progress',trace,'-o',packed],300,ENV)
            transport={'raw_bytes':raw_bytes,'raw_sha256':raw_sha,'path':str(packed),'bytes':packed.stat().st_size,'sha256':sha(packed)}
            trace.unlink()
            item={'kind':kind,'index':i,'proof':report,'costs':{'emit':emit,'prove':proving,'compress':compression},'witness_transport':transport}
            save(out/name/'result.json',item); result.append(item)
            print(json.dumps({'phase':kind,'chunk':i,'proof_self_verified':True}),flush=True)
        check_pins(frozen); config()
        record={'proofs_generated':True,'fresh_consumer_verified':False,'kind':kind,'chunks':result,'elapsed_seconds':time.monotonic()-started,'finished_utc':now()}
        save(out/'result.json',record)
        save(out/'progress.json',{'phase':'complete','completed':len(result),'utc':now()})
        return record
    except BaseException as e:
        save(out/'failure.json',{'error':repr(e),'completed':len(result),'retried':False,'utc':now()}); raise


def verify_phase(c, kind, case, proofs, out):
    accepted=[]
    for i in range(COUNT[kind]):
        label=f'{kind}{i:03}'; proof=proofs/f'chunk{i:03}'/'proof.bin'
        cost=command(out,label,invoke(c,kind,'verify',i,case,proof),300,ENV)
        record=read(out/(label+'.stdout'))
        check_record(c,kind,i,case,record,proof)
        accepted.append({'kind':kind,'index':i,'verification':record,'proof_bytes':proof.stat().st_size,'costs':cost})
        save(out/'progress.json',{'phase':kind,'completed_phase':i+1,'utc':now()})
    return accepted


def produce_update(source, out):
    out=Path(out).resolve(); out.mkdir(); c=config()
    command(out,'import',[c['native']['update'],'export',Path(source).resolve(),out/'case'],60,ENV)
    generate('update',out/'case',out/'proofs')
    result={'proofs_generated':True,'case':str(out/'case'),'proofs':str(out/'proofs'),'binding':read(out/'case/operation.json')['binding'],'fresh_proofs':8,'private_files_read':0}
    save(out/'result.json',result); return result


def verify_update(expected, produced, out):
    c=config(); produced=Path(produced).resolve(); out=Path(out).resolve(); out.mkdir(); start=time.monotonic()
    case=produced/'case'; binding=read(case/'operation.json')['binding']
    assert binding==expected
    frozen={str(p):sha(p) for p in case.rglob('*') if p.is_file()}
    checks=verify_phase(c,'update',case,produced/'proofs',out)
    check_pins(frozen); config()
    result={'verified':True,'operation':'acc+fresh-old','binding':binding,'proofs_verified':8,'verifications':checks,'elapsed_seconds':time.monotonic()-start,'private_files_read':0,'finished_utc':now()}
    save(out/'result.json',result); return result


def produce_infer(model, query, key, capture, out):
    c=config(); out=Path(out).resolve(); out.mkdir(); capture=Path(capture).resolve()
    model,query,key=(Path(x).resolve() for x in (model,query,key))
    start=time.monotonic()
    command(out,'import-infer',[c['native']['infer'],'import',c['linear_plan'],model,query,key,capture/'basic.dot.ct',capture/'basic-000.ct',out/'infer_case'],120,ENV)
    command(out,'import-square',[c['native']['extension'],'import',capture,out/'square_case'],120,ENV)
    command(out,'import-rescale',[c['native']['rescale'],'import',capture,out/'rescale_case'],120,ENV)
    infer=read(out/'infer_case/operation.json')['binding']; square=read(out/'square_case/operation.json')['binding']; rescale=read(out/'rescale_case/operation.json')
    assert infer['model_ciphertext_sha256']==sha(model) and infer['query_sha256']==sha(query) and infer['evaluation_key_sha256']==sha(key)
    assert infer['dot_ciphertext_sha256']==square['input_ciphertext_sha256']
    assert infer['kernel_ciphertext_sha256']==square['output_ciphertext_sha256']==rescale['output_ciphertext_sha256']
    assert square['source_trace_sha256']==rescale['source_trace_sha256']
    for kind in ('infer','extension','tensor','rescale'):
        case=out/('infer_case' if kind=='infer' else 'rescale_case' if kind=='rescale' else 'square_case')
        generate(kind,case,out/kind)
    result={'proofs_generated':True,'fresh_consumer_verified':False,'binding':infer,'fresh_proofs':116,'reused_proofs':0,'elapsed_seconds':time.monotonic()-start,'private_files_read':0,'finished_utc':now()}
    save(out/'result.json',result); return result


def verify_infer(expected, produced, out):
    c=config(); produced=Path(produced).resolve(); out=Path(out).resolve(); out.mkdir(); start=time.monotonic()
    ic,sc,rc=(produced/name for name in ('infer_case','square_case','rescale_case'))
    binding=read(ic/'operation.json')['binding']
    assert all(binding[k]==v for k,v in expected.items())
    assert set(expected)=={'model_ciphertext_sha256','query_sha256','evaluation_key_sha256','kernel_ciphertext_sha256'}
    assert binding['linear_plan_sha256']==c['linear_plan_sha256']
    square=read(sc/'operation.json')['binding']; rescale=read(rc/'operation.json')
    assert square['input_ciphertext_sha256']==binding['dot_ciphertext_sha256']
    assert square['output_ciphertext_sha256']==binding['kernel_ciphertext_sha256']==rescale['output_ciphertext_sha256']
    assert square['source_trace_sha256']==rescale['source_trace_sha256']
    frozen={str(p):sha(p) for case in (ic,sc,rc) for p in case.rglob('*') if p.is_file()}
    checks=[]
    for kind in ('infer','extension','tensor','rescale'):
        checks.extend(verify_phase(c,kind,ic if kind=='infer' else rc if kind=='rescale' else sc,produced/kind,out))
    check_pins(frozen); config()
    result={'complete_infer_verified':True,'statement':'Caller-approved model/query/evaluation-key digests yield the caller-selected kernel ciphertext under the fixed-profile parser/NTT/controller TCB.','binding':binding,'square_binding':square,'proofs_verified':len(checks),'fresh_proofs':116,'reused_proofs':0,'verifications':checks,'proof_bytes':sum(x['proof_bytes'] for x in checks),'elapsed_seconds':time.monotonic()-start,'private_files_read':0,'finished_utc':now()}
    assert len(checks)==116
    save(out/'result.json',result); save(out/'progress.json',{'phase':'complete','completed':116,'utc':now()}); return result


if __name__=='__main__':
    action,*a=sys.argv[1:]
    if action=='produce-update' and len(a)==2: r=produce_update(*a)
    elif action=='verify-update' and len(a)==3: r=verify_update(read(a[0]),*a[1:])
    elif action=='produce-infer' and len(a)==5: r=produce_infer(*a)
    elif action=='verify-infer' and len(a)==3: r=verify_infer(read(a[0]),*a[1:])
    else: raise SystemExit('produce-update SOURCE NEW | verify-update EXPECTED PRODUCED NEW | produce-infer MODEL QUERY KEY CAPTURE NEW | verify-infer EXPECTED PRODUCED NEW')
    print(json.dumps(r,indent=2))
