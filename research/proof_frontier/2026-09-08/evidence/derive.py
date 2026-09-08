from fractions import Fraction
from itertools import combinations, product
from math import log2
import random

p = 2013265921
n = 2**20
d = 2**19
old = Fraction(n-d, 3*n)
new = Fraction(n-d, 2*n)
print('production-shaped point: p=',p,'n=',n,'d=',d,'|F|=',p**4)
print('old radius ceiling=',old,'fullUD conservative ceiling=',new)
print('delta=1/5 old admissible:', Fraction(1,5)<old, 'fullUD admissible:', Fraction(1,5)<new)
print('same challenge error n/p^4=', Fraction(n,p**4))
print('same challenge error bits=', format(log2(p**4/n),'.9f'))
print('n^C / |F| < 1 requires C <', format(log2(p**4)/log2(n),'.9f'))
for target in (55,100,120,128):
    print('n^C / |F| < 2^-'+str(target)+' requires C <',format((log2(p**4)-target)/log2(n),'.9f'))

# Falsifier for deleting 2e+d<=n from the intended core. This samples
# candidate pairs, then exhaustively verifies every field scalar and codeword.
p,n,d,e=7,6,2,3
code=[tuple((a+b*x)%p for x in range(n)) for a,b in product(range(p),repeat=2)]
rng=random.Random(20260908)
for trial in range(100000):
    f0=tuple(rng.randrange(p) for _ in range(n))
    f1=tuple(rng.randrange(p) for _ in range(n))
    common=max(sum(f0[i]==u[i] and f1[i]==v[i] for i in range(n)) for u,v in product(code,repeat=2))
    if common >= n-e: continue
    witnesses=[]
    for z in range(p):
        w=tuple((f0[i]+z*f1[i])%p for i in range(n))
        best=max(code,key=lambda c:sum(x==y for x,y in zip(w,c)))
        agreement=sum(x==y for x,y in zip(w,best))
        if agreement<n-e: break
        witnesses.append((z,agreement,best))
    if len(witnesses)==p:
        print('radius falsifier trial=',trial,'p,n,d,e=',(p,n,d,e),'2e+d=',2*e+d)
        print('f0=',f0,'f1=',f1,'common_agreement_max=',common)
        print('fold witnesses (z, agreements, codeword)=',witnesses)
        break
else:
    raise RuntimeError('No witness found within fixed candidate budget')
