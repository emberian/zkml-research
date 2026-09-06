#!/usr/bin/env python3
"""Small independent closure/range audit; no DDH-security implementation proof."""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import importlib.util
import json
import sys

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'private_construction/additive_ipfe.py'
SOURCE_HASH=hashlib.sha256(SOURCE.read_bytes()).hexdigest()
spec=importlib.util.spec_from_file_location('reviewed_ipfe',SOURCE)
m=importlib.util.module_from_spec(spec)
spec.loader.exec_module(m)


def main():
    started=datetime.now(timezone.utc).isoformat()
    mpk,msk=m.setup()
    sky=m.keyder(msk,m.Y)
    x=(1,4,6)
    u=(3,1,2)
    r,t=17,23
    encrypted=m.encrypt(mpk,x,r)
    fresh=m.encrypt(mpk,u,t)
    result=m.combine(encrypted,fresh)
    target=tuple(a+b for a,b in zip(x,u))
    assert result==m.encrypt(mpk,target,r+t)
    projected=m.project_group(result,sky)
    assert projected==pow(m.G,sum(a*b for a,b in zip(target,m.Y)),m.P)
    alt=(2,3,11)
    assert sum(a*b for a,b in zip(x,m.Y))==sum(a*b for a,b in zip(alt,m.Y))
    # Decode-range failures do not hide the underlying projected group value.
    table=m.decode_table()
    known=[]
    rejected=[]
    for value in (65,66):
        ct=m.encrypt(mpk,(value,0,0))
        group=m.project_group(ct,sky)
        assert group==pow(m.G,value,m.P)
        known.append(group)
        try: m.decode(group,table)
        except ValueError: rejected.append(value)
    assert rejected==[65,66] and known[0]!=known[1]
    result=dict(label='EXECUTED independent algebra and decode-boundary falsifier',
                command=[sys.executable,str(Path(__file__).resolve())],
                started_utc=started,source=str(SOURCE),sha256=SOURCE_HASH,
                source_unchanged=SOURCE_HASH==hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                ciphertext_update_equals_summed_coins_encryption=True,
                projection_equals_direct_group_encoding=True,
                beyond_decode_interval=dict(inputs=rejected,both_integer_decoders_refuse=True,
                    projected_group_values_distinct=True,guess_comparison_recovers_each=True),
                scope='No counterexample to equal-projection pair. Decode failure alone is not a projection-hiding interface.')
    (HERE/'ipfe_independent_review.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__': main()
