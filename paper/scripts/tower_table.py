#!/usr/bin/env python3
"""tower_table.py -- the deliverable: verified {native-limb} x c1 x c2 towers
with depth-2 and lattice-security columns. Combines koalabear_limb.py's number
theory + noise ledger with lattice_estimate.py's VALIDATED estimator."""
from math import log2
import importlib.util, sys, io, contextlib

def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    m = importlib.util.module_from_spec(spec)
    buf = io.StringIO()
    try:
        with contextlib.redirect_stdout(buf):
            spec.loader.exec_module(m)
    except SystemExit:
        pass
    return m

LE = load("le", "lattice_estimate.py")
DET = [2,3,5,7,11,13,17,19,23,29,31,37]
def mr(n,a):
    d,r=n-1,0
    while d%2==0: d//=2; r+=1
    x=pow(a,d,n)
    if x in (1,n-1): return True
    for _ in range(r-1):
        x=x*x%n
        if x==n-1: return True
    return False
def isp(n):
    if n<2: return False
    for p in DET:
        if n==p: return True
        if n%p==0: return False
    return all(mr(n,a) for a in DET)

T=1032193; N=4096; SIG=10**0.5
KB=2**31-2**24+1; BB=2**31-2**27+1
LOG2_T=log2(T); MULG=1+log2(N)+LOG2_T
FOLD=[0xffffee001,0xffffc4001,0x1ffffe0001]
SQ_DEP=log2(sum(FOLD)); LQ_DEP=sum(log2(x) for x in FOLD); RELIN_DEP=46.1
cliff=lambda lq: lq-1-LOG2_T
margin=lambda lq,sq: cliff(lq)-((RELIN_DEP+(sq-SQ_DEP))+MULG)

sol=[(a,b,2**a-2**b+1) for a in range(14,63) for b in range(13,a)
     if T<2**a-2**b+1<2**62 and isp(2**a-2**b+1)]

cache={}
def sec(lq):
    k=round(lq,2)
    if k not in cache:
        beta,m,d=LE.primal_usvp(N,lq,SIG)
        cache[k]=(beta,0.292*beta,0.29613*beta+20.387)
    return cache[k]

for NAME,P in (("KoalaBear",KB),("BabyBear",BB)):
    LP=log2(P); rows=[]
    for i in range(len(sol)):
        a1,b1,c1=sol[i]
        if c1==P: continue
        for j in range(i+1,len(sol)):
            a2,b2,c2=sol[j]
            if c2==P: continue
            lq=LP+log2(c1)+log2(c2)
            if not (105.0<=lq<=112.0): continue
            mg=margin(lq,log2(P+c1+c2))
            if mg>0: rows.append((mg,lq,(a1,b1),(a2,b2),max(a1,a2)))
    rows.sort(key=lambda r:(-r[0],r[1]))
    # keep the widest-margin tower per distinct (a1,a2) bit shape
    seen=set(); top=[]
    for r in rows:
        key=(r[2][0],r[3][0])
        if key in seen: continue
        seen.add(key); top.append(r)
    print(f"\n{'='*104}\n{NAME} native limb -- towers supporting the MEASURED depth 2 "
          f"({len(rows)} of {sum(1 for i in range(len(sol)) for j in range(i+1,len(sol)) if 105.0<=LP+log2(sol[i][2])+log2(sol[j][2])<=112.0)} in band)\n{'='*104}")
    print(f"{'companions':<34} {'log2 Q':>7} {'cliff':>7} {'d2 margin':>10} "
          f"{'k(max limb)':>11} {'beta':>6} {'coreSVP':>8} {'MATZOV':>8}")
    print("-"*104)
    for mg,lq,s1,s2,amax in top[:14]:
        beta,csvp,mz=sec(lq)
        k = -(-amax//14)
        print(f"2^{s1[0]}-2^{s1[1]}+1 x 2^{s2[0]}-2^{s2[1]}+1{'':<10}"[:34]
              +f" {lq:7.2f} {cliff(lq):7.2f} {mg:+10.2f} {k:11d} "
              f"{beta:6d} {csvp:8.1f} {mz:8.1f}")
    b,c,m=sec(LQ_DEP)
    print("-"*104)
    print(f"{'DEPLOYED 3x{36,36,37} (all emulated)':<34} {LQ_DEP:7.2f} "
          f"{cliff(LQ_DEP):7.2f} {margin(LQ_DEP,SQ_DEP):+10.2f} {3:11d} "
          f"{b:6d} {c:8.1f} {m:8.1f}")
