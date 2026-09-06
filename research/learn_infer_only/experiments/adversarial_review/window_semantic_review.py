#!/usr/bin/env python3
"""Independent integer/source-provenance review; no encryption benchmark rerun."""
from pathlib import Path
import hashlib
import json
import random
import sys

HERE=Path(__file__).resolve().parent
RESEARCH=HERE.parents[1]
SERDE=RESEARCH/'experiments/durable_integration/bfv_window'


def digest(path): return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    validation_path=RESEARCH/'experiments/he_closure_costs/window_formal/validation.json'
    serde_path=SERDE/'serde_check_02.json'
    validation=json.loads(validation_path.read_text())
    serde=json.loads(serde_path.read_text())
    assert serde['exit_code']==0 and serde['inputs_unchanged']
    serde_sources={p:digest(Path(p))==sha for p,sha in serde['source_sha256'].items()}
    assert all(serde_sources.values())
    code=(SERDE/'serde_probe/src/main.rs').read_text()
    assert 'assert_eq!(seeded.len(),expanded.len());' in code
    assert 'assert_eq!(restored.len(),expanded.len());' in code
    assert 'let full_zero=&fresh-&fresh;' in code
    assert '(ct+full_zero).to_bytes()' in code
    modules={m['module']:digest(RESEARCH/'formal/he_closure_costs'/(m['module']+'.lean'))==m['source_sha256']
             for m in validation['modules']}
    dependencies={d['path']:digest(Path(d['path']))==d['sha256'] for d in validation['dependencies']}
    assert all(modules.values()) and all(dependencies.values())
    inputs=[Path(__file__),validation_path,serde_path]+[Path(p) for p in serde_sources]+[
        RESEARCH/'formal/he_closure_costs'/(m['module']+'.lean') for m in validation['modules']]+[
        RESEARCH/'formal/durable_integration/bfv_window/Theory/CiphertextWindow.lean',
        RESEARCH/'formal/durable_integration/bfv_window/Assurance/CiphertextWindowCell.lean',
        RESEARCH/'formal/durable_integration/bfv_window/Assurance/CiphertextWindowWitness.lean',
        Path('/Users/ember/dev/breadstuffs/vendor/fhe-dregg/src/bfv/plaintext.rs'),
        Path('/Users/ember/dev/breadstuffs/vendor/fhe-dregg/src/bfv/parameters.rs')]
    hashes={str(p):digest(p) for p in inputs}
    q=2199023190017*4398046486529;t=4294828033;n=4096;s=20;w=128;width=577;b=127
    E=2*n*s*s+s;L=width*b;score_bound=w*L*b;margin=2*t*w*L*(E+1)
    assert (q,E,L,score_bound,margin)==(9671406214650060397780993,3276820,73279,1191223424,264008552994527828978432)
    assert margin<q and 2*score_bound<t and 2*(width-1)<n
    def rounded(phase): return (2*t*phase+q)//(2*q)
    def centered(value):
        residue=value%t
        return residue if 2*residue<t else residue-t
    inverse=pow(-t,-1,q)
    messages=list(range(-127,128))+[t-1,t,t+1,-t,-t-1]
    for m in messages:
        actual_encoding=((m%t)*(q%t)%t)*inverse%q
        assert actual_encoding==(q*m//t)%q
    rng=random.Random(20260906)
    cases=[]
    # Dense signed extreme rows exercise the actual full W, width and score budget.
    for m in [-b,b]:
        for query in [-b,b]:
            for error in [-E,E]:
                phase=w*width*query*(q*m//t+error)
                score=w*width*query*m
                cases.append((phase,score,w*width*abs(query)*t*(E+1)))
    for _ in range(100):
        queries=[rng.randint(-b,b) for _ in range(8)]
        phase=score=0
        size=rng.randrange(1,33)
        for _ in range(size):
            for query in queries:
                m=rng.randint(-b,b);error=rng.randint(-E,E)
                phase+=query*(q*m//t+error)
                score+=query*m
        cases.append((phase,score,size*sum(map(abs,queries))*t*(E+1)))
    for phase,score,bound in cases:
        assert abs(t*phase-q*score)<=bound and 2*bound<q
        for wrap in [-3,0,4]:
            assert centered(rounded(phase+q*wrap))==score
    # This exact floor-encoding discrepancy survives even when fresh error is zero.
    assert 2*(17//3)-(17*2//3)==-1
    failure=q//(2*t)+1
    assert rounded(0)==rounded(1)==0 and centered(rounded(-failure))==-1
    assert all(digest(Path(p))==sha for p,sha in hashes.items())
    result=dict(label='EXECUTED independent integer arithmetic and final saved-serde provenance review',
        command=[sys.executable,str(Path(__file__).resolve())],inputs=hashes,inputs_unchanged=True,
        serde_saved_run_matches_current_sources=serde_sources,
        refreshed_HE_modules_match=modules,refreshed_HE_dependencies_match=dependencies,
        serialization_comparisons_check_lengths=True,source_floor_encoding_congruences=len(messages),
        Q=q,E=E,L=L,score_bound=score_bound,margin_lhs=margin,
        signed_integer_cases=len(cases),wraps_per_case=3,wrong_expiry_failure_step=failure,
        wrong_expiry_output=-1,zero_error_floor_carry_counterexample=-1,
        scope='Source arithmetic and retained normalized serializer fixtures; no Rust group/NTT/phase/scaler theorem, no HE rerun.')
    (HERE/'window_semantic_review.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ['inputs','serde_saved_run_matches_current_sources','refreshed_HE_dependencies_match']},indent=2))


if __name__=='__main__': main()
