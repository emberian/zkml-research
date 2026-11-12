#!/usr/bin/env python3
"""Certified rational enclosures for useful exact-real bf16 counterexamples.
Only integer/Fraction operations decide the codes; no exp/tanh/libm calls.
For x>0, Taylor lower S_N and geometric tail upper at ratio x/(N+2)
enclose exp(x), because all subsequent term ratios are <= that ratio.
"""
from fractions import Fraction as Q
import struct

def exp_interval(x,N=100):
    x=Q(x);term=Q(1);s=term
    for k in range(1,N+1):
        term*=x/k;s+=term
    nxt=term*x/(N+1);ratio=x/(N+2)
    assert 0<ratio<1
    return s,s+nxt/(1-ratio)

def bfvalue(code):
    return Q.from_float(struct.unpack('<f',struct.pack('<I',code<<16))[0])

def rounded_code(x):
    assert 0<=x<=1
    low,high=0,0x3f80
    while low<high:
        mid=(low+high+1)//2
        if bfvalue(mid)<=x:low=mid
        else:high=mid-1
    if bfvalue(low)==x:return low
    a,b=bfvalue(low),bfvalue(low+1)
    if x-a<b-x:return low
    if x-a>b-x:return low+1
    return low if low%2==0 else low+1

def pin(interval):
    lo,hi=interval;assert lo<=hi
    a,b=rounded_code(lo),rounded_code(hi)
    assert a==b,(hex(a),hex(b))
    return a

def sigmoid(x):
    a,b=exp_interval(x)
    y=(a/(1+a),b/(1+b))
    # E/(1+E)^2 decreases for E>=1.
    d=(b/(1+b)**2,a/(1+a)**2)
    return pin(y),pin(d)

def tanh(x):
    a,b=exp_interval(2*x)
    y=((a-1)/(a+1),(b-1)/(b+1))
    d=(4*b/(1+b)**2,4*a/(1+a)**2)
    return pin(y),pin(d)

for name,f,x,z in [('sigmoid',sigmoid,7,8),('tanh',tanh,4,5)]:
    y0,d0=f(x);y1,d1=f(z)
    assert y0==y1 and d0!=d1
    print(name,'inputs',x,z,'common exact-real/single-round bf16 output',hex(y0),
          'distinct derivative codes',hex(d0),hex(d1))
print('Each endpoint interval rounds to one code using exact rational comparisons.')
print('Thus output-keyed derivatives fail under the claimed exact-real semantics too; no full census claimed.')
