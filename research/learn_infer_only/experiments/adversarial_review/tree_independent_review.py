#!/usr/bin/env python3
"""Independent finite-word audit of the bounded response-tree prototype."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import importlib.util
import itertools
import json
import sys

HERE=Path(__file__).resolve().parent
SOURCE=HERE.parent/'private_construction/bounded_tree.py'
SOURCE_HASH=hashlib.sha256(SOURCE.read_bytes()).hexdigest()
STARTED_UTC=datetime.now(timezone.utc).isoformat()
spec=importlib.util.spec_from_file_location('reviewed_tree',SOURCE)
m=importlib.util.module_from_spec(spec)
sys.modules[spec.name]=m
spec.loader.exec_module(m)


def ref(initial, commands):
    s=initial
    out=[]
    for c in commands:
        if c==0:
            s=(s+1)%256
            out.append(255)
        elif c==1:
            s=(s*2)%256
            out.append(255)
        elif c==2:
            out.append(1 if s>=128 else 0)
        else: raise ValueError(c)
    return out


def decode_public_history(node):
    path=[]
    while node:
        path.append((node-1)%3)
        node=(node-1)//3
    return list(reversed(path))


def main():
    if '--partition-only' in sys.argv:
        partition=[0]*256
        counts=[1]
        for _ in range(8):
            seen={}
            updated=[]
            for s in range(256):
                signature=((255,partition[(s+1)%256]),(255,partition[(2*s)%256]),(s>>7,partition[s]))
                if signature not in seen: seen[signature]=len(seen)
                updated.append(seen[signature])
            partition=updated
            counts.append(len(seen))
        output={'command':[sys.executable,str(Path(__file__).resolve()),'--partition-only'],
                'review_script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                'started_utc':STARTED_UTC,'classes_by_horizon_0_to_8':counts}
        (HERE/'tree_horizon_partition.json').write_text(json.dumps(output,indent=2)+'\n')
        print(json.dumps(output,indent=2))
        return
    coins=b'independent-review-coupling-not-secret'
    h=5
    # Full trace words, independently enumerated: every shorter path is a prefix.
    paths=list(itertools.product(range(3),repeat=h))
    signatures={}
    for s in range(256):
        signature=tuple(tuple(ref(s,p)) for p in paths)
        signatures.setdefault(signature,[]).append(s)
    checks=0
    metadata_checks=0
    encrypted_group=[]
    for group in signatures.values():
        artifact=m.compile_tree(group[0],h,coins)
        for path in paths:
            assert m.run_path(artifact,list(path))==ref(group[0],path)
            checks+=1
        for s in group[1:]:
            assert m.wire(artifact)==m.wire(m.compile_tree(s,h,coins))
        if 0 in group: encrypted_group=group
    # Public node numbers expose the complete path, with zero AEAD calls.
    a=m.compile_tree(0,h,coins)
    for path in paths:
        node=0
        for command in path:
            node=3*node+command+1
        assert decode_public_history(node)==list(path)
        metadata_checks+=1
    assert 0 in encrypted_group and 1 in encrypted_group
    # Eight command slots suffice to recover each initial byte with copied root.
    # Ask high bit after k doublings, using a fresh branch for each k.
    recovery_queries=0
    for s in range(256):
        artifact=m.compile_tree(s,8,coins)
        bits=[]
        for k in range(8):
            query=[1]*k+[2]
            bits.append(m.run_path(artifact,query)[-1])
            recovery_queries+=len(query)
        recovered=sum(bit<<(7-i) for i,bit in enumerate(bits))
        assert recovered==s
    # Independent horizon partition recurrence; each signature includes the
    # immediate output and the previous-depth class for every command.
    partition=[0]*256
    horizon_classes=[1]
    for depth in range(1,9):
        seen={}
        updated=[]
        for initial in range(256):
            signature=((255,partition[(initial+1)%256]),
                       (255,partition[(initial*2)%256]),
                       (initial>>7,partition[initial]))
            if signature not in seen: seen[signature]=len(seen)
            updated.append(seen[signature])
        partition=updated
        horizon_classes.append(len(seen))
    assert horizon_classes[8]==256
    data=dict(label='EXECUTED independent finite-path/metadata audit; no new cryptographic theorem',
              command=[sys.executable,str(Path(__file__).resolve())],
              started_utc=STARTED_UTC,
              reviewed_source=str(SOURCE),sha256=SOURCE_HASH,
              source_unchanged=SOURCE_HASH==hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
              classes_by_horizon_0_to_8=horizon_classes,
              horizon=h,paths_per_class=len(paths),classes=len(signatures),
              checked_trace_paths=checks,zero_class=encrypted_group,
              metadata_only_full_histories_recovered=metadata_checks,
              metadata_attack_ae_decryptions=0,
              at_horizon_8_full_state_recovery=dict(states=256,
                  total_transition_queries=recovery_queries,
                  per_state_transition_queries=recovery_queries//256,
                  per_state_infer_observations=8,
                  condition='Root restores permitted; learn double k=0..7 then infer'))
    (HERE/f'tree_independent_review_{1+len(list(HERE.glob("tree_independent_review_*.json"))):02}.json').write_text(json.dumps(data,indent=2)+'\n')
    print(json.dumps(data,indent=2))

if __name__=='__main__': main()
