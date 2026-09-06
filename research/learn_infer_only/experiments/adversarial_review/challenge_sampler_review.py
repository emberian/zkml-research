#!/usr/bin/env python3
"""Exact distribution of six base-p digits of a uniform 256-bit digest.

This is a finite sampler audit, not a claim that cSHAKE is a random oracle.
"""
from fractions import Fraction
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import math
import sys

HERE=Path(__file__).resolve().parent
SOURCES=[Path('/Users/ember/dev/minidregg/Compiler/CommittedTerminalFiatShamir.lean'),
         Path('/Users/ember/dev/minidregg/Compiler/Sp800185Cshake256Core.lean')]


def main():
    p=2013265921
    target=p**6
    domain=2**256
    quotient,remainder=divmod(domain,target)
    assert 0<remainder<target
    high=Fraction(quotient+1,domain)
    low=Fraction(quotient,domain)
    uniform=Fraction(1,target)
    tv=Fraction(remainder*(target-remainder),target*domain)
    rho=high/uniform
    excess=rho-1
    assert excess==Fraction(target-remainder,domain)
    assert high>uniform>low
    assert remainder*high+(target-remainder)*low==1
    # Exhaustive independently checked small analogue of the same formulas.
    small_counts=[0]*25
    for v in range(256): small_counts[v%25]+=1
    assert small_counts==[11]*6+[10]*19
    small_tv=sum(abs(Fraction(count,256)-Fraction(1,25)) for count in small_counts)/2
    assert small_tv==Fraction(6*19,25*256)
    # Every event satisfies max-atom domination (enumerated small event masks
    # restricted to first ten outputs to keep the audit explicitly bounded).
    event_checks=0
    for mask in range(1<<10):
        event=[i for i in range(10) if (mask>>i)&1]
        actual=sum(Fraction(small_counts[i],256) for i in event)
        bound=Fraction(25*11,256)*Fraction(len(event),25)
        assert actual<=bound
        event_checks+=1
    result=dict(label='EXECUTED exact finite sampler audit; uniform-byte input is hypothetical',
       command=[sys.executable,str(Path(__file__).resolve())],
       started_utc=datetime.now(timezone.utc).isoformat(),
       sources={str(s):hashlib.sha256(s.read_bytes()).hexdigest() for s in SOURCES},
       p=p,field_cardinality=target,digest_domain=domain,
       quotient=quotient,remainder=remainder,
       max_atom=str(high),uniform_atom=str(uniform),min_atom=str(low),
       total_variation=str(tv),total_variation_log2=math.log2(tv.numerator)-math.log2(tv.denominator),
       max_density_ratio=str(rho),max_density_excess=str(excess),
       max_density_excess_log2=math.log2(excess.numerator)-math.log2(excess.denominator),
       small_analogue=dict(domain=256,target=25,histogram=small_counts,tv=str(small_tv),event_checks=event_checks),
       derived_bounds={
         'fixed_event':'Pr_D[E] <= rho * Pr_uniform[E]',
         'joint_n_draws':'Pr_D^n[E] <= rho^n * Pr_uniform^n[E]',
         'generic_FS_game_transport':'n=t+14; multiply the uniform-game bound by rho^(t+14)',
         'possible_tighter_route':'Redo per-fresh-challenge bad-event argument using max atom; not proved in Lean here'},
       scope='Exact uniform-field equality is false even with an ideal uniform256-bit hash. Actual cSHAKE cryptanalysis/ROM realization remains separate.')
    (HERE/'challenge_sampler_review.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
