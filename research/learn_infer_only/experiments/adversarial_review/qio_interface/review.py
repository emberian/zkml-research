#!/usr/bin/env python3
"""Independent exact finite premise controls and pinned local-source access.
No cryptographic implementation or machine-checked asymptotic theorem.
"""
from __future__ import annotations
from datetime import datetime,timezone
from fractions import Fraction as F
from itertools import product
import hashlib,json,subprocess,sys
from pathlib import Path

HERE=Path(__file__).resolve().parent
RESIDENT=HERE.parents[2]
TARGET=RESIDENT/'experiments/pq_composition/qio_interface/QIO_INTERFACE.md'
MIRROR=Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')
EXPECTED='2cc1d2dc58d8cde8e6a3c3badba602357f9de2d11e008b6d421177eea3dd01d3'

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def z(a=0,b=0):return F(a),F(b)
def add(a,b):return a[0]+b[0],a[1]+b[1]
def mul(a,b):return a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]
def scale(a,c):return a[0]*c,a[1]*c
def matrix(bloch):
    x,y,zz=map(F,bloch)
    return ((z((1+zz)/2),z(x/2,-y/2)),(z(x/2,y/2),z((1-zz)/2)))
def trace_product(a,b):
    ans=z()
    for i,j in product(range(2),repeat=2):ans=add(ans,mul(a[i][j],b[j][i]))
    assert ans[1]==0
    return ans[0]
def mix(a,b,p):return tuple(tuple(add(scale(a[i][j],p),scale(b[i][j],1-p)) for j in range(2)) for i in range(2))

def quantum_controls():
    # Six pure Pauli eigenstates plus the maximally mixed state. The +/-Y
    # states and X/Y effects retain exact imaginary off-diagonal entries.
    blochs=[(0,0,0),(1,0,0),(-1,0,0),(0,1,0),(0,-1,0),(0,0,1),(0,0,-1)]
    states=[matrix(r) for r in blochs]
    effects=states
    mixtures=0
    for e0,e1,r0,r1,p in product(effects,effects,states,states,[F(i,4) for i in range(5)]):
        rho=mix(r0,r1,p)
        d0=trace_product(e0,r0)-trace_product(e1,r0)
        d1=trace_product(e0,r1)-trace_product(e1,r1)
        dm=trace_product(e0,rho)-trace_product(e1,rho)
        assert dm==p*d0+(1-p)*d1
        assert abs(dm)<=max(abs(d0),abs(d1))
        mixtures+=1
    # cq prefix with branch-specific states, measurements, masses, signs and
    # good masks; branch measurement choice models hardwiring the whole W.
    choices=[]
    for i,(rho,e0,e1) in enumerate(product(states,effects,effects)):
        d=trace_product(e0,rho)-trace_product(e1,rho)
        choices.append(d)
    branch_gaps=sorted(set(choices))
    assert min(branch_gaps)==-1 and max(branch_gaps)==1
    qualified=0;rare=None
    masses=[F(0),F(1,2**32),F(1,4),F(1,2),F(3,4),F(1)]
    for p,d0,d1,mask in product(masses,branch_gaps,branch_gaps,[(0,0),(0,1),(1,0),(1,1)]):
        eps=max([abs(d) for d,g in zip((d0,d1),mask) if g]+[F(0)])
        mass=p*mask[0]+(1-p)*mask[1]
        gap=abs(p*mask[0]*d0+(1-p)*mask[1]*d1)
        assert gap<=mass*eps
        full=abs(p*d0+(1-p)*d1)
        assert full<=mass*eps+(1-mass)
        qualified+=1
        if p==F(1,2**32) and d0==1 and mask==(1,0):rare=dict(good_mass=str(mass),qualified_gap=str(gap),bound=str(mass*eps))
    # Perfect cancellation in one mixed experiment cannot supply a qualified
    # bound. This is not a separation of complete iO definitions.
    cancellation=dict(total_gap=str(abs(F(1,2)-F(1,2))),qualified_gap=str(F(1,2)))
    # Fresh-coin independence is essential: X=r XOR b is uniform by itself,
    # but supplying retained R=r reveals b. Not a cryptographic construction.
    correlated=[]
    for b in (0,1):
        prob=sum(F(1,2) for r in (0,1) if ((r^b)^r)==1)
        correlated.append(str(prob))
    assert correlated==['0','1']
    return dict(exact_density_matrix_mixtures=mixtures,cq_qualified_cases=qualified,
                branch_gap_values=[str(x) for x in branch_gaps],rare_good_event=rare,
                cancellation=cancellation,fresh_coin_independence_falsifier=correlated,
                model='Exact 2x2 rational complex density matrices and POVM effects, including X/Y coherences; not a quantum iO implementation.')

def main():
    assert sha(TARGET)==EXPECTED
    (HERE/'extracts').mkdir(exist_ok=True)
    source_rows=[]
    for paper,expected,pages in [('2023/265','18dce0afa750386cdf530c6ce4f4cc6aa6be29703e9782ee1e152e527e0afeb9',[19,20,21,22]),
                                ('2025/2215','5ffbaabd34120b58c46b3c6763d6e665be7a535118566c709ad007ea0fa99866',[3,10,16])]:
        pdf=MIRROR/(paper+'.pdf');assert sha(pdf)==expected
        out=HERE/'extracts'/(paper.replace('/','-')+'.txt')
        cmd=['pdftotext','-layout',str(pdf),str(out)]
        r=subprocess.run(cmd,text=True,capture_output=True);assert r.returncode==0
        source_rows.append(dict(pdf=str(pdf),sha256=sha(pdf),read_pdf_pages=pages,command=cmd,
                                exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr,extract_sha256=sha(out)))
    text=(HERE/'extracts/2023-265.txt').read_text().split('\f')
    assert 'A non-uniform quantum polynomial-time' in text[18]
    assert 'For all sequences of functionally equivalent circuits' in text[19]
    assert 'This advice depends only on the circuit family, not on the sampled circuits' in text[20]
    result=dict(classification='Independent bounded source/proof review plus exact finite premise controls',
                timestamp_utc=datetime.now(timezone.utc).isoformat(),command=[sys.executable,str(Path(__file__).resolve())],
                target=dict(path=str(TARGET),sha256=sha(TARGET)),sources=source_rows,controls=quantum_controls(),
                quantifier_control=dict(moving_witness=[int(k==lam) for lam in range(1,17) for k in [lam]],
                    scope='All-sequences diagonalization, not an efficient witness-selector algorithm'),
                queries=dict(web=0,SQL=0,schema=0,Kagi=0,Scry=0,network_PDF_downloads=0),
                script_sha256=sha(Path(__file__)))
    assert sha(TARGET)==EXPECTED
    (HERE/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
