#!/usr/bin/env python3
"""Finite bit-valued cache coupling audit; no encryption/hash implementation."""
from __future__ import annotations
from collections import Counter
from datetime import datetime, timezone
from fractions import Fraction
import hashlib,itertools,json,sys
from pathlib import Path

HERE=Path(__file__).resolve().parent

def lookup(log,q,fresh):
    return next((a for old,a in log if old==q),fresh)

def local_run(ask,coins):
    log=[]
    for fresh in coins:
        q=ask([a for _,a in log]);log.append((q,lookup(log,q,fresh)))
    return log

def first_ask(h):
    return 0 if len(h)<2 else 1+h[0]

def second_ask(first,h):
    return 0 if len(h)<2 else 1+((first[0]+first[-1])%2)

def shared_run(c0,c1,tagged=True):
    log=[];first=[];second=[]
    for coin in c0:
        raw=first_ask(first);q=(0,raw) if tagged else raw
        a=lookup(log,q,coin);log.append((q,a));first.append(a)
    for coin in c1:
        raw=second_ask(first,second);q=(1,raw) if tagged else raw
        a=lookup(log,q,coin);log.append((q,a));second.append(a)
    return log,first,second

def main():
    counts=Counter();fibres={};failure=None
    for raw in itertools.product((0,1),repeat=6):
        c0,c1=raw[:3],raw[3:]
        a=local_run(first_ask,c0);h0=[v for _,v in a]
        b=local_run(lambda h:second_ask(h0,h),c1)
        expected=[((0,q),v) for q,v in a]+[((1,q),v) for q,v in b]
        actual,g0,g1=shared_run(c0,c1)
        assert actual==expected
        assert len(actual)==6 and g0==h0
        for tag,local in [(0,a),(1,b)]:
            for q in range(3):
                assert lookup(actual,(tag,q),0)==lookup(local,q,0)
                counts['answer_transports']+=1
        p=bool(g0[0]);q=g1[0]==g0[0]
        counts['samples']+=1;counts['left_event']+=p;counts['right_event']+=q
        counts['union_event']+=p or q
        fibres.setdefault(c0,Counter())['right']+=q
        fibres[c0]['total']+=1
        broken,b0,b1=shared_run(c0,c1,False)
        projected=[(key,v) for (_,key),v in expected]
        if broken!=projected:
            counts['omitted_tag_pathwise_failures']+=1
            failure=failure or dict(raw_coins=raw,tagged=actual,untagged=broken)
        counts['omitted_tag_right_event']+=b1[0]==b0[0]
        counts['omitted_tag_union_event']+=bool(b0[0]) or b1[0]==b0[0]
    assert counts['samples']==64
    assert counts['union_event']==48
    assert counts['omitted_tag_union_event']==64
    assert all(Fraction(f['right'],f['total'])==Fraction(1,2) for f in fibres.values())
    report=dict(label='EXECUTED finite symbolic cache audit',timestamp_utc=datetime.now(timezone.utc).isoformat(),
        command=[sys.executable,str(Path(__file__).resolve())],source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        counts=dict(counts),phase0_queries=3,phase1_queries=3,global_queries=6,
        right_conditional_probability_every_first_coin_vector='1/2',
        tagged_union_probability='3/4',omitted_tag_union_probability='1',
        first_falsifier=failure,claims_excluded=['encryption','hash sampling','full-field security estimate','arbitrary interleaving proof'],
        source_scope='Exhaustive 64 raw positional coin vectors; repeated queries consume a position but reuse the first answer.',
        metered_search_queries=0)
    (HERE/'report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(dict(samples=counts['samples'],answer_transports=counts['answer_transports'],
        tagged_union='3/4',omitted_tag_union='1',falsifier_count=counts['omitted_tag_pathwise_failures'])))

if __name__=='__main__':main()
