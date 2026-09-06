#!/usr/bin/env python3
"""Independent scalar arithmetic/source-table review; no Rust or HE rerun."""
import ast
from datetime import datetime, timezone
import hashlib
import json
from math import prod
from pathlib import Path
import random
import re
import sys

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parents[1]
SOURCE = RESEARCH/'formal/bfv_lift_refinement/engine_refinement/Compiler/FheRnsScaleDecomposition.lean'
ENGINE = RESEARCH/'experiments/bfv_lift_refinement'


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def nearest(x, d):
    return (2*x+d)//(2*d)


def ceildiv(x, d):
    return -((-x)//d)


def scalar(name, text):
    return int(re.search(r'def '+name+r' : ℤ := (\d+)', text)[1])


def vector(name, text):
    return ast.literal_eval('['+re.search(r'def '+name+r' : Fin 6 → ℤ := !\[([^\]]+)\]', text)[1]+']')


def literal_correction(total):
    mask256=(1<<256)-1
    word=total & mask256
    negative=(word >> 191)>0
    cast=((mask256 ^ word if negative else word)>>126) & ((1<<128)-1)
    # The source's negative branch uses ordinary u128 + 1.
    if negative:
        assert cast+1 < (1<<128), 'outside modeled nonoverflow domain'
    value=(cast+1)//2
    return -value if negative else value


def main():
    started=datetime.now(timezone.utc).isoformat()
    inputs=[SOURCE, ENGINE/'engine-run.json', ENGINE/'captured-rounding-witness.json', Path(__file__)]
    hashes={str(p):digest(p) for p in inputs}
    text=SOURCE.read_text()
    q,p,t,gamma=[scalar('deployed'+s,text) for s in ['Q','P','T','Gamma']]
    base,g,omega,theta_f,theta_g=[vector('deployed'+s,text) for s in ['Base','Garner','Omega','ThetaF','ThetaG']]
    captured=vector('capturedResidues',text)
    shift=min(127,min(191-(qi*len(base)-1).bit_length() for qi in base))
    assert shift==126 and p==prod(base)
    assert g==[(p//qi)*pow(p//qi,-1,qi) for qi in base]
    assert omega==[nearest(t*gi,q) for gi in g]
    assert gamma==nearest(t*p,q) and t*p==q*gamma
    assert theta_f==[ceildiv((1<<127)*(t*gi-q*oi),q) for gi,oi in zip(g,omega)]
    assert theta_g==[nearest((1<<shift)*gi,p) for gi in g]
    assert all(0<=r<qi for r,qi in zip(captured,base))
    cases=[]
    for bits in range(64):
        cases.append([qi-1 if (bits>>i)&1 else 0 for i,qi in enumerate(base)])
    rng=random.Random(202609060843)
    cases += [[rng.randrange(qi) for qi in base] for _ in range(1000)]
    cases.append(captured)
    discrepancies=[]
    for r in cases:
        garner_sum=sum(ri*gi for ri,gi in zip(r,theta_g))
        correction_sum=sum(ri*fi for ri,fi in zip(r,theta_f))
        assert 0<=garner_sum<(1<<191) and abs(correction_sum)<(1<<191)
        # Follow the source's wrap, right shift, truncation, then div_ceil.
        word=garner_sum% (1<<256)
        cast=(word>>(shift-1))% (1<<128)
        v=(cast+1)//2
        w=literal_correction(correction_sum)
        assert v==nearest(garner_sum,1<<shift)
        assert w==nearest(correction_sum,1<<127)
        k=sum(ri*oi for ri,oi in zip(r,omega))-v*gamma
        z=sum(ri*gi for ri,gi in zip(r,g))-v*p
        exact_c=sum(ri*(t*gi-q*oi) for ri,gi,oi in zip(r,g,omega))
        assert t*z==q*k+exact_c
        error=q*correction_sum-(1<<127)*exact_c
        assert 0<=error<=(q-1)*sum(r)<q*(1<<127)
        y=k+w
        reference=nearest(t*z,q)
        assert y-reference in [0,1]
        if y!=reference:
            discrepancies.append(dict(residues=r,selected_lift=z,source=y,nearest=reference))
    assert discrepancies[-1]['source']==172481 and discrepancies[-1]['nearest']==172480
    assert discrepancies[-1]['selected_lift']==108454153028594899284870262370752
    witness=json.loads((ENGINE/'captured-rounding-witness.json').read_text())
    assert witness['rests']==captured and witness['actual_y']==172481 and witness['ideal_y']==172480
    manifest=json.loads((ENGINE/'engine-run.json').read_text())
    source_match={s['path']:digest(Path(s['path']))==s['sha256'] for s in manifest['sources']}
    assert all(source_match.values())
    result=dict(label='EXECUTED independent scalar arithmetic review; no universal Rust implementation claim',
        command=[sys.executable,str(Path(__file__).resolve())],started_utc=started,
        inputs=hashes,inputs_unchanged=all(digest(Path(p))==h for p,h in hashes.items()),
        canonical_vectors_checked=len(cases),constructor_tables_recomputed=True,
        literal_word_branch_checks=len(cases),shift=shift,discrepancies=discrepancies,
        current_engine_sources_match_retained_manifest=source_match,
        same_row_envelope_accepts_wrong_source_residue=172480,
        exact_source_residue=172481,
        domain='all reviewed cases have 0 <= r_i < q_i; no decryption correctness or fresh-ciphertext failure probability claim')
    output=HERE/'bfv_scalar_review.json'
    output.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['canonical_vectors_checked','constructor_tables_recomputed','inputs_unchanged','discrepancies']},indent=2))


if __name__=='__main__':
    main()
