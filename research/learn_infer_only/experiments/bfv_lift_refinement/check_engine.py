#!/usr/bin/env python3
"""Compare retained live Rust coefficients against an independent bigint oracle."""
import gzip,hashlib,json,sys,time
from math import prod
from pathlib import Path
from fhe_scaler_model import ScalerModel,ideal_center,ideal_scale

ROOT=Path(__file__).resolve().parent

def crt_rows(obj):
    base=obj['moduli'];q=prod(base);rows=obj['rows']
    weights=[q//p*pow(q//p,-1,p) for p in base]
    values=[sum(r[i]*g for r,g in zip(rows,weights))%q for i in range(len(rows[0]))]
    assert all(all(v%p==r[i] for i,v in enumerate(values)) for p,r in zip(base,rows))
    return values

def direct_conv(a,b):
    n=len(a);out=[0]*n
    for i,x in enumerate(a):
        for j,y in enumerate(b):out[(i+j)%n]+=(1 if i+j<n else -1)*x*y
    return out

def packed_conv(a,b):
    n=len(a);bound=n*max(map(abs,a))*max(map(abs,b));bits=max(2,(2*bound+1).bit_length())
    def pack(xs):
        acc=0
        for x in reversed(xs):acc=(acc<<bits)+x
        return acc
    value=pack(a)*pack(b);mask=(1<<bits)-1;half=1<<(bits-1);coeff=[]
    for _ in range(2*n-1):
        digit=value&mask
        if digit>=half:digit-=1<<bits
        assert abs(digit)<=bound
        coeff.append(digit);value=(value-digit)>>bits
    assert value==0
    out=[coeff[k]-(coeff[k+n] if k+n<len(coeff) else 0) for k in range(n)]
    if n<=64:assert out==direct_conv(a,b)
    return out

def tensor(a,b):
    c0=packed_conv(a[0],b[0]);left=packed_conv(a[0],b[1]);right=packed_conv(a[1],b[0]);c2=packed_conv(a[1],b[1])
    return [c0,[x+y for x,y in zip(left,right)],c2]

def full_case(rec):
    base=rec['base'];extbase=rec['extended_base'];q=prod(base);p=prod(extbase);n=rec['N'];t=rec['t']
    ext=ScalerModel(base,extbase,1,1);down=ScalerModel(extbase,base,t,q)
    canonical={side:[crt_rows(poly) for poly in rec[side]] for side in ('a','b')}
    lifted={};extension_checks=0;extension_center_diffs=[]
    for side in ('a','b'):
        lifted[side]=[]
        for j,values in enumerate(canonical[side]):
            out=rec[side+'_extended'][j];one=[]
            for k,x in enumerate(values):
                expected,details=ext.scale([x%qi for qi in base]);actual=[row[k] for row in out['rows']]
                assert expected==actual,('extension source model mismatch',side,j,k)
                one.append(details['selected_lift']);extension_checks+=1
                if details['selected_lift']!=ideal_center(x,q):extension_center_diffs.append([side,j,k])
            lifted[side].append(one)
    raw=tensor(lifted['a'],lifted['b']);unsigned=tensor(canonical['a'],canonical['b'])
    product_checks=0;output_checks=0;rounded_diffs=[];unsigned_diffs=0
    for c,values in enumerate(raw):
        for k,z in enumerate(values):
            expectedprod=[z%pi for pi in extbase];actualprod=[r[k] for r in rec['product_extended'][c]['rows']]
            assert expectedprod==actualprod,('lifted integer convolution mismatch',c,k)
            assert 2*abs(z)<p,('extended product wrap',c,k)
            product_checks+=1
            expected,details=down.scale(expectedprod);actual=[r[k] for r in rec['output'][c]['rows']]
            assert expected==actual,('downscale source model mismatch',c,k)
            assert details['selected_lift']==z,('downscale selected lift differs from full integer convolution',c,k)
            output_checks+=1
            ideal=(t*z+q//2)//q
            assert details['integer']-ideal in (0,1),('source arithmetic envelope failed',c,k)
            if details['integer']%q!=ideal%q:rounded_diffs.append(dict(c=c,k=k,z=str(z),source_y=str(details['integer']),ideal_y=str(ideal)))
            unsigned_ideal=(t*unsigned[c][k]+q//2)//q
            if unsigned_ideal%q!=details['integer']%q:unsigned_diffs+=1
    return dict(label=rec['label'],seed=rec['seed'],N=n,t=t,Q=str(q),P=str(p),
        extension_coefficient_checks=extension_checks,integer_convolution_checks=product_checks,full_output_coefficient_checks=output_checks,
        extension_center_disagreements=extension_center_diffs,source_vs_nearest_disagreements=rounded_diffs,
        first_tranche_unsigned_reference_disagreements=unsigned_diffs,
        output_rows_sha256=hashlib.sha256(json.dumps(rec['output'],sort_keys=True).encode()).hexdigest())

def boundary_case(rec):
    base=rec['base'];extbase=rec['extended_base'];q=prod(base);p=prod(extbase);t=rec['t'];out=[]
    for name,frombase,tobase,n,d in [('extension',base,extbase,1,1),('downscale',extbase,base,t,q)]:
        model=ScalerModel(frombase,tobase,n,d);diffs=[]
        for item in rec[name]:
            expected,details=model.scale(item['input']);assert expected==item['output'],('scalar model mismatch',name,item['x'])
            x=int(item['x']);ideal=ideal_scale(x,prod(frombase),n,d)
            if expected!=[ideal%p for p in tobase]:
                diffs.append(dict(x=item['x'],actual_y=str(details['integer']),ideal_y=str(ideal),
                    actual_selected_lift=str(details['selected_lift']),ideal_selected_lift=str(ideal_center(x,prod(frombase))),
                    actual_residues=item['output'],v=str(details['v']),w=str(details['w'])))
        out.append(dict(stage=name,cases=len(rec[name]),nearest_reference_disagreements=len(diffs),first_disagreements=diffs[:8]))
    return dict(Q=str(q),t=t,stages=out)

def main():
    start=time.monotonic();path=Path(sys.argv[1]) if len(sys.argv)>1 else ROOT/'engine_probe/full-coefficients.jsonl.gz'
    payload=gzip.decompress(path.read_bytes()) if path.suffix=='.gz' else path.read_bytes()
    records=[json.loads(line) for line in payload.decode().splitlines()]
    full=[full_case(r) for r in records if r['kind']=='full_unrelinearized_tensor']
    boundary=[boundary_case(r) for r in records if r['kind']=='scalar_boundary_cases']
    result=dict(label='EXECUTED real full-coefficient comparisons; source model, not universal implementation theorem',
        command=[sys.executable,str(Path(__file__).resolve())],full_cases=full,boundary_cases=boundary,
        source_model_sha256=hashlib.sha256((ROOT/'fhe_scaler_model.py').read_bytes()).hexdigest(),
        checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),rust_output_uncompressed_sha256=hashlib.sha256(payload).hexdigest(),retained_fixture_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
        elapsed_seconds=time.monotonic()-start)
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
