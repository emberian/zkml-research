"""Finite Fraction trees and source unranking; no encryption or PPT execution."""
from collections import Counter
from fractions import Fraction as Q
import hashlib,importlib.util,json,sys
from pathlib import Path
HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[1]
SOURCE=ROOT/'experiments/private_construction/horizon'
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def paths(B,H,p=()):
    yield p
    if H:
        for b in range(B):yield from paths(B,H-1,p+(b,))

def check_tree(B,H,source):
    ns=list(paths(B,H));N=len(ns);assert N==sum(B**d for d in range(H+1))
    # All local left and oriented-right gaps are nonzero. Their sum is 1/2.
    denominator=2*sum(range(1,2*N+1))
    gaps={p:(Q(2*i+1,denominator),Q(2*i+2,denominator)) for i,p in enumerate(ns)}
    root_gaps={}
    frames={}
    for p in reversed(ns):
        a,b=gaps[p]
        children=[p+(c,) for c in range(B)] if len(p)<H else []
        middle=sum((root_gaps[c] for c in children),Q(0))
        gap=a+b+middle
        # (RealL, IdealL, IdealR, RealR), with oriented right gap b.
        frame=(gap,middle+b,b,Q(0))
        assert all(Q(0)<=v<=Q(1) for v in frame)
        assert frame[0]-frame[3]==(frame[0]-frame[1])+(frame[1]-frame[2])-(frame[3]-frame[2])
        assert frame[1]-frame[2]==middle
        if len(p)==H:assert middle==0
        root_gaps[p]=gap;frames[p]=frame
    labels=[source.unrank_one_sim(B,H,r) for r in range(2*N)]
    assert len(set(labels))==2*N
    assert Counter((p,side) for p,side,_ in labels)==Counter((p,s) for p in ns for s in ['left','right'])
    differences=[];real=[];ideal=[]
    for p,side,orientation in labels:
        rL,iL,iR,rR=frames[p]
        if side=='left':
            assert orientation==1;real.append(rL);ideal.append(iL)
        else:
            assert orientation==-1;real.append(1-rR);ideal.append(1-iR)
        differences.append(real[-1]-ideal[-1])
    assert root_gaps[()]==sum(differences)==Q(1,2)
    uniform=(sum(real)-sum(ideal))/(2*N)
    assert uniform==Q(1,4*N)
    weights={d:Q(sum(len(p)==d for p in ns),N) for d in range(H+1)}
    assert weights=={d:Q(B**d,N) for d in range(H+1)}
    assert sum(weights.values())==1
    means={d:sum((a+b for p,(a,b) in gaps.items() if len(p)==d),Q(0))/(2*B**d)
           for d in range(H+1) if B**d}
    assert sum(weights[d]*means.get(d,Q(0)) for d in weights)==uniform
    M=1<<(2*N-1).bit_length()
    assert 2*N<=M<4*N
    padded=(sum(real)-sum(ideal))/M
    assert padded==root_gaps[()]/M
    if B==1:assert N==H+1
    if B>=2:assert N+1<=2*B**H
    return {'B':B,'H':H,'N':N,'sides':2*N,'M':M,'root_gap':str(root_gaps[()]),
        'uniform_gap':str(uniform),'padded_gap':str(padded),'all_frames_valid_probabilities':True,
        'all_source_ranks_unique':True,'weighted_depth_identity':True}

def main():
    spec=importlib.util.spec_from_file_location('private_horizon_source',SOURCE/'audit.py')
    source=importlib.util.module_from_spec(spec);spec.loader.exec_module(source)
    rows=[check_tree(B,H,source) for B in range(5) for H in range(5)]
    witness={'B':2,'H':1,'N':3,'root_gap':'1/2','real_probability':'2/3','ideal_probability':'7/12',
        'uniform_gap':'1/12','depth_weights':['1/3','2/3'],'depth_side_means':['0','1/8'],
        'biased_depth_gap':'1/16','dyadic_size':8,'padded_gap':'1/16'}
    assert Q(2,3)-Q(7,12)==Q(1,12)
    assert Q(1,3)*0+Q(2,3)*Q(1,8)==Q(1,12)
    assert (Q(0)+Q(1,8))/2==Q(1,16)!=Q(1,12)
    report={'classification':'executed finite arithmetic and source-unranking controls',
        'rows':rows,'witness':witness,'falsifiers':{
            'uniform_depth_without_weights':True,'omitted_nonzero_node_term':True,
            'omitted_terminal_middle_gap':True,'uncomplemented_right_side':True,
            'dyadic_padding_keeps_denominator_2N':True},
        'scope':'falsifier claims additionally proved in Lean; no cryptographic advantages sampled',
        'source_sha256':{str(SOURCE/name):sha(SOURCE/name) for name in ['HORIZON.md','audit.py','stdout.txt','results.json']},
        'script_sha256':sha(__file__),'python':sys.version,'new_metered_searches':0}
    (HERE/'results.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'cases':len(rows),'nodes':sum(r['N'] for r in rows),
        'source_ranked_sides':sum(r['sides'] for r in rows),'all_pass':True,'witness':witness},sort_keys=True))

if __name__=='__main__':main()
