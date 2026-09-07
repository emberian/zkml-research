#!/usr/bin/env python3
"""Exact finite coefficient accounting for pointwise-correctness propagation."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent


def main():
    cases=0
    for n in range(17):
        nodes=(1 << (n+1))-1
        depths=sum(d*(1 << d) for d in range(n+1))
        for s in range(1,33):
            for lh in range(1,33):
                # Coefficients ordered X-correctness, B-correctness, PRF-gap,
                # composition-PRG-gap and tree-PRG-gap.
                weak=(1,s,s,0,0)
                outer=(0,lh,0,0,0)
                inner_tape=(0,0,0,1,0)
                fresh=tuple(sum(row[j] for row in (weak,outer,inner_tape)) for j in range(5))
                assert fresh==(1,lh+s,s,1,0)
                tree=tuple(nodes*fresh[j]+(depths if j==4 else 0) for j in range(5))
                assert tree==(nodes,nodes*(lh+s),nodes*s,nodes,depths)
                bound=max(s,lh)
                assert tree[1] <= 2*bound*nodes
                assert tree[2] <= bound*nodes
                assert tree[3]+tree[4] == n*(1 << (n+1))+1
                cases+=1
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    assert sha(HERE/'BOOTSTRAP_LIFT.md')=='ec9f721f2402d31a49a9fd4ee14f978b4cf7474429600710347dc555fe0d9792'
    result={'label':'EXECUTED','scope':__doc__,'coefficient_cases':cases,
            'frozen_bootstrap_sha256':sha(HERE/'BOOTSTRAP_LIFT.md'),
            'supplement_sha256':sha(HERE/'POINTWISE_CORRECTNESS.md'),
            'script_sha256':sha(Path(__file__)),'additional_network_queries':0}
    (HERE/'pointwise_controls.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
