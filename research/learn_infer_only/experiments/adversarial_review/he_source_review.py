#!/usr/bin/env python3
"""Read-only estimator source/config audit; never runs attack estimators."""
import ast
from datetime import datetime, timezone
from fractions import Fraction
import hashlib
import json
from math import ceil, comb, log2
from pathlib import Path
import sys

HERE=Path(__file__).resolve().parent
EST=HERE.parents[1]/'experiments/he_closure_costs/estimator'
PIN=EST/'runtime/pinned-estimator/estimator'


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    paths=[PIN/f for f in ['nd.py','lwe.py','lwe_dual.py','reduction.py']]
    paths += [EST/'run_estimates.py',EST/'environment-final-provenance.json',Path(__file__)]
    hashes={str(p):digest(p) for p in paths}
    tree=ast.parse((PIN/'lwe.py').read_text())
    aliases=[n for n in ast.walk(tree) if isinstance(n,ast.ImportFrom) and n.module=='lwe_dual']
    assert any(a.name=='matzov' and a.asname=='dual_hybrid' for n in aliases for a in n.names)
    dual=ast.parse((PIN/'lwe_dual.py').read_text())
    cls=next(n for n in dual.body if isinstance(n,ast.ClassDef) and n.name=='MATZOV')
    cost=next(n for n in cls.body if isinstance(n,ast.FunctionDef) and n.name=='cost')
    call=next(n for n in cls.body if isinstance(n,ast.FunctionDef) and n.name=='__call__')
    assignments=[n for n in ast.walk(cost) if isinstance(n,ast.Assign)
                 and any(isinstance(t,ast.Name) and t.id=='m' for t in n.targets)]
    assert any(isinstance(n.value,ast.Attribute) and isinstance(n.value.value,ast.Name)
               and n.value.value.id=='params' and n.value.attr=='n' for n in assignments)
    calls=[n for n in ast.walk(call) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute)
           and isinstance(n.func.value,ast.Name) and n.func.value.id=='self' and n.func.attr=='cost']
    assert calls and all('m' not in [k.arg for k in c.keywords] for c in calls)
    # Exact ideal-bit CBD20 arithmetic, independent of Sage's moment approximation.
    pmf={x:Fraction(comb(40,20+x),1<<40) for x in range(-20,21)}
    assert sum(pmf.values())==1
    assert sum(x*p for x,p in pmf.items())==0
    variance=sum(x*x*p for x,p in pmf.items())
    assert variance==10
    mass=Fraction(0); support99=0
    for probability in sorted(pmf.values(),reverse=True):
        mass+=probability;support99+=1
        if mass>=Fraction(99,100):break
    provenance=json.loads((EST/'environment-final-provenance.json').read_text())
    source_hash_match={row['name']:digest(PIN/row['name'])==row['sha256'] for row in provenance['source_files']}
    assert all(source_hash_match.values())
    result={
        'label':'EXECUTED source/config and exact finite distribution audit; no attack rerun or security theorem',
        'command':[sys.executable,str(Path(__file__).resolve())],
        'started_utc':datetime.now(timezone.utc).isoformat(),
        'inputs':hashes,
        'inputs_unchanged':all(digest(Path(p))==h for p,h in hashes.items()),
        'pinned_source_hashes_match':source_hash_match,
        'dual_hybrid_alias':'lwe_dual.matzov',
        'MATZOV_cost_definition_line':cost.lineno,
        'MATZOV_call_definition_line':call.lineno,
        'cost_calls_without_m':[c.lineno for c in calls],
        'sample_scope':'MATZOV dual_hybrid fixes lattice sample m to n; params.m affects beta cap, not m optimization',
        'CBD20_exact':{'variance':str(variance),'bounds':[-20,20],
            'entropy_bits_per_coefficient':-sum(float(p)*log2(float(p)) for p in pmf.values()),
            'one_dimensional_optimal_support_for_99_percent':support99,
            'one_dimensional_support_size_helper_at_99_percent':ceil(Fraction(99,100)*41),
            'meaning':'finite PMF comparison, not a corrected attack estimate'},
    }
    (HERE/'he_source_review.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:result[k] for k in ['inputs_unchanged','sample_scope','CBD20_exact']},indent=2))


if __name__=='__main__':main()
