#!/usr/bin/env python3
"""Independent arithmetic and emitted JSON check; no Lean IO or HE rerun."""
from pathlib import Path
import hashlib
import gzip
import json
import re
import sys
from bfv_scalar_review import scalar, vector, literal_correction

HERE=Path(__file__).resolve().parent
RESEARCH=HERE.parents[1]
FORMAL=RESEARCH/'formal/bfv_lift_refinement/source_certificate/Compiler'
EXP=RESEARCH/'experiments/bfv_lift_refinement/source_certificate'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def retained(path):
    return path if path.exists() else path.with_suffix(path.suffix+'.gz')


def read_json(path):
    return json.loads(gzip.decompress(path.read_bytes()) if path.suffix=='.gz' else path.read_bytes())


def main():
    engine=RESEARCH/'formal/bfv_lift_refinement/engine_refinement/Compiler/FheRnsScaleDecomposition.lean'
    descriptor_path=retained(EXP/'optimized-descriptor.json')
    inputs=[Path(__file__),HERE/'bfv_scalar_review.py',engine,EXP/'layout.json',
            descriptor_path,EXP/'check-results.json']+[
            FORMAL/('FheSourceCertificate'+suffix+'.lean') for suffix in
            ['', 'Layout', 'Emit', 'Optimized', 'Verifier', 'Witness']]
    hashes={str(p):digest(p) for p in inputs}
    text=engine.read_text()
    q,gamma=[scalar('deployed'+s,text) for s in ['Q','Gamma']]
    bases,omegas,tg,tf,captured=[vector(s,text) for s in
        ['deployedBase','deployedOmega','deployedThetaG','deployedThetaF','capturedResidues']]
    rows=json.loads((EXP/'layout.json').read_text())['rows']
    matrix=(FORMAL/'FheSourceCertificateLayout.lean').read_text()
    # Parse the actual Lean literals independently of the generator/layout JSON.
    for side in ['left','right']:
        block=matrix.split('def '+side+'Constant')[1].split('\ndef ')[0]
        constants={int(i):int(v) for i,v in re.findall(r'\| (\d+) => (\d+)',block)}
        block=matrix.split('def '+side+'Matrix')[1].split('\ndef ')[0]
        cells={(int(i),int(j)):int(v) for i,j,v in re.findall(r'\| (\d+),(\d+) => (\d+)',block)}
        for i,row in enumerate(rows):
            assert row[side+'_constant']==constants[i]
            assert row[side]==[cells.get((i,j),0) for j in range(21)]
    assert len(rows)==12

    def values(r):
        gs=sum(ri*gi for ri,gi in zip(r,tg))
        fs=sum(ri*fi for ri,fi in zip(r,tf))
        # Literal source shifts and sign branch, rather than the loose envelope.
        v=(((gs%(1<<256))>>125)%(1<<128)+1)//2
        w=literal_correction(fs)
        y=sum(ri*oi for ri,oi in zip(r,omegas))-v*gamma+w
        remg=(2*gs+(1<<126))%(1<<127)
        remf=(2*fs+(1<<127))%(1<<128)
        output=y%q
        x=r+[max(0,b-1-ri) for ri,b in zip(r,bases)]+[
            v,remg,(1<<127)-1-remg,w+(1<<65),remf,(1<<128)-1-remf,
            output,q-1-output,y//q+(1<<120)]
        assert all(0<=xi<(1<<132) for xi in x)
        return x

    def balanced(x):
        return [row['left_constant']+sum(a*b for a,b in zip(row['left'],x)) ==
                row['right_constant']+sum(a*b for a,b in zip(row['right'],x)) for row in rows]

    d=read_json(descriptor_path)
    prime=d['p']
    assert (prime,d['nVars'],d['nPublic'],d['nWires'],len(d['gates']),len(d['zeros']))==(
        2013265921,30294,0,183105,132675,36498)

    def variables(x):
        a=[0]*d['nVars']
        digits=[(xi>>(6*j))&63 for xi in x for j in range(22)]
        def install(start,bits,vals):
            for i,value in enumerate(vals):
                a[start+i]=value%prime
                for j in range(bits):
                    a[start+len(vals)+bits*i+j]=(value>>j)&1
        install(0,6,digits)
        for k,row in enumerate(rows):
            start=3234+2255*k
            coefficients={side:[c<<(6*j) for c in row[side] for j in range(22)] for side in ['left','right']}
            total=row['left_constant']+sum(c*ds for c,ds in zip(coefficients['left'],digits))
            install(start,6,[(total>>(6*i))&63 for i in range(57)])
            for side,offset in [('left',399),('right',1327)]:
                carries=[0]
                for i in range(57):
                    mass=((row[side+'_constant']>>(6*i))&63)+carries[-1]
                    mass+=sum(((c>>(6*i))&63)*ds for c,ds in zip(coefficients[side],digits))
                    carries.append(mass//64)
                install(start+offset,15,carries)
        return a

    def evaluate(a):
        a=a+[0]*(d['nWires']-len(a))
        def read(w): return w['c'] if 'c' in w else a[w['w']]
        for gate in d['gates']:
            assert gate['out']>=d['nVars']
            lhs,rhs=read(gate['a']),read(gate['b'])
            assert gate['op'] in ['add','mul']
            a[gate['out']]=(lhs+rhs if gate['op']=='add' else lhs*rhs)%prime
        return all(read(z)==0 for z in d['zeros'])

    cap=values(captured)
    assert all(balanced(cap)) and cap[18]==172481 and evaluate(variables(cap))
    wrong=cap.copy();wrong[18]-=1;wrong[19]+=1
    assert not evaluate(variables(wrong))
    shifted=wrong.copy();shifted[15]-=1;shifted[16]+=(1<<128)
    failures=[i for i,ok in enumerate(balanced(shifted)) if not ok]
    assert failures==[9] and not evaluate(variables(shifted))
    # Without the correction remainder complement row, a coherent wrong-neighbor
    # certificate survives all eleven other exact integer balances.
    noncanonical=values([bases[0]]+captured[1:])
    assert [i for i,ok in enumerate(balanced(noncanonical)) if not ok]==[0]
    assert not evaluate(variables(noncanonical))
    bad_digit=variables(cap);bad_digit[0]=64
    assert not evaluate(bad_digit)
    outputs=[]
    for r in [[0]*6,[b-1 for b in bases],[(123456789*(i+1))%b for i,b in enumerate(bases)]]:
        x=values(r)
        assert all(balanced(x)) and evaluate(variables(x))
        outputs.append(x[18])
    result=dict(label='EXECUTED independent source-literal, balance and emitted-JSON arithmetic review',
        command=[sys.executable,str(Path(__file__).resolve())],inputs=hashes,
        inputs_unchanged=all(digest(Path(p))==h for p,h in hashes.items()),
        lean_matrix_matches_json=True,optimized_gates=len(d['gates']),zeros=len(d['zeros']),
        captured_output=cap[18],captured_accepted=True,wrong_nearest_refused=True,
        correction_shift_refused=True,correction_shift_only_failed_balance=failures,
        noncanonical_input_refused=True,digit64_refused=True,additional_canonical_outputs=outputs,
        external_public_count=d['nPublic'],
        scope='Canonical integer output modQ; target-limb array/provenance are not inputs to this descriptor. JSON evaluation is independent executed evidence, not a new kernel theorem.')
    version=1+len(list(HERE.glob('bfv_certificate_review_*.json')))
    (HERE/f'bfv_certificate_review_{version:02}.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k!='inputs'},indent=2))


if __name__=='__main__': main()
