#!/usr/bin/env python3
"""Light, stdlib-only counterexamples to the 2026-11-05 counts models.
Run from zkml-research root. Reads original source; writes no original files.
"""
from fractions import Fraction
import math
import runpy
import subprocess
import struct

space = runpy.run_path('notes/construction-search/space.py')
# Functions created by runpy share their execution globals, not necessarily the returned dict.
sg = space['evaluate'].__globals__
space['_calibrate_witgen']()
dark = runpy.run_path('notes/dark-learning-scripts/tradeoff_space.py')
act = runpy.run_path('notes/dark-learning-scripts/backward_table_virtualization.py')
# Pin the historical source: the companion lane has now applied our repair.
mma = {'__name__': 'historical_mma'}
exec(compile(subprocess.check_output(['git', '-C', '/Users/ember/dev/degg-research', 'show',
    '15db9784e2043bb170431203f3c63d88625933e2:experiments/mma-field-mapping/mma_limbs.py'],
    text=True), '<historical-mma>', 'exec'), mma)

print('SPACE ENUMERATION')
print('compatible points:', len(space['enumerate_space']()))
print('\nSPACE AUDIT TENSOR ELIGIBILITY')
p = space['evaluate'](**space['NAMED']['U1'])
full = space['evaluate'](**space['NAMED']['U1-per-request'])
print('original U1 crypto/proxy:', p['crypto_s'], p['proxy_s'])
print('per-request mults / audit mults:', full['mults'], p['mults'])
# Exact textual correction under audit: both sides of tensor eligible fraction carry p.
from pathlib import Path
src = Path('notes/construction-search/space.py').read_text()
old = '(tc_cell * commit + S["virt"] * PIOP[piop]["virt_mult"]) / max(mults, 1)'
new = '(p * (tc_cell * commit + S["virt"] * PIOP[piop]["virt_mult"])) / max(mults, 1)'
assert src.count(old) == 1
fixed = {'__name__': 'audit_fixed_space'}
exec(compile(src.replace(old,new), '<audit-fixed-space>', 'exec'), fixed)
fixed['_calibrate_witgen']()
pf = fixed['evaluate'](**fixed['NAMED']['U1'])
print('corrected U1 crypto/proxy:', pf['crypto_s'], pf['proxy_s'])
print('corrected/original:', pf['proxy_s']/p['proxy_s'])
print('per-request unchanged:', full == fixed['evaluate'](**fixed['NAMED']['U1-per-request']))
print('SASH/U1 old and corrected:', space['evaluate'](**space['NAMED']['SASH-anchor'])['proxy_s']/p['proxy_s'], fixed['evaluate'](**fixed['NAMED']['SASH-anchor'])['proxy_s']/pf['proxy_s'])

print('\nBF16 ROUNDING PATH COUNTEREXAMPLE')
x = 1 + 2**-8 + 2**-30
lo = Fraction(1)
hi = Fraction(129,128)
xf = Fraction.from_float(x)
assert hi-xf < xf-lo
oldcode = act['float_to_bf16'](x)
print('x = 1 + 2^-8 + 2^-30:', x)
print('direct nearest bf16 code by exact rational distances: 0x3f81')
print('existing float64 -> float32 -> bf16 code:', hex(oldcode))
assert oldcode == 0x3f80
print('\nACTIVATION CANCELLATION CONTROLS')
for name,x,stable in [
 ('sigmoid derivative',40.0,lambda x: math.exp(-x)/(1+math.exp(-x))**2),
 ('tanh derivative',20.0,lambda x: 4*math.exp(-2*x)/(1+math.exp(-2*x))**2),
 ('GELU value',-10.0,lambda x: x*.5*math.erfc(-x/math.sqrt(2)))]:
 f = act['FUNCS']['sigmoid'][1] if name.startswith('sigmoid') else act['FUNCS']['tanh'][1] if name.startswith('tanh') else act['gelu']
 actual, control = f(x), stable(x)
 print(name, 'input',x,'current',actual,hex(act['float_to_bf16'](actual)), 'algebraically equivalent stable evaluation',control,hex(act['float_to_bf16'](control)))
 assert actual == 0 and act['float_to_bf16'](control) not in (0,0x8000)
print('Stable controls expose mismatch; they are not a certified exact-real census.')

print('\nDARK SIGNED-RANGE CONTROL')
cap = (dark['T']-1)//2
print('full signed 4x8-bit magnitudes 8,128:',cap//(8*128))
print('symmetric magnitudes 7,127:',cap//(7*127))
print('full signed 4x4-bit magnitudes 8,8:',cap//(8*8))
print('symmetric magnitudes 7,7 (current script):',dark['k_wrap']())
assert cap//(8*128)==504 and cap//(7*127)==580
print('current claimed-control LHS (with unexplained +137):',cap//(7*127+137),'asserts only <=604')

print('\nMMA REPRESENTATION CONTROL')
ds = mma['SCHEMES'][2][2]
L = mma['limbs'](67,13,True)
repr2={a+13*b for a in ds for b in ds}
print('generic p=67 base13 signed helper says limbs:',L,'but 65 representable:',65 in repr2)
assert L==2 and 65 not in repr2
# For actual primes, least-absolute residue representatives give a constructive encoder.
reps={r:min((v for v in ds if v%13==r),key=abs) for r in range(13)}
print('least-absolute representatives:',reps,'max magnitude:',max(map(abs,reps.values())))
for name,p in mma['PRIMES']:
 L=mma['limbs'](p,13,True)
 upper=p-1
 for _ in range(L-1): upper=(upper+8)//13
 print(name,'L=',L,'upper bound on last quotient=',upper,'all terminal values representable=',all(v in ds for v in range(upper+1)))
 assert all(v in ds for v in range(upper+1))
 for x in (0,1,5,65,p//2,p-1):
  q=x; digits=[]
  for _ in range(L):
   v=reps[q%13]; digits.append(v); q=(q-v)//13
  assert q==0 and sum(v*13**i for i,v in enumerate(digits))==x
print('For that explicit encoder max digit product is 64; conservative <2^24 bound:',(2**24-1)//64)

print('\nDARK RANGE-INVARIANT COUNTEREXAMPLE')
row=dark['price']('RNS-202@8192',False,'fhe+mpc-boundary','dark','backprop-full',1,.01,4096,32)
w0,delta,x=7,-7,7
w1=w0-delta*x
before=4096*w0*7;after=4096*w1*7
print('row gates:',row['gates'],'W0=',w0,'W1=',w1,'initial dot=',before,'next dot=',after,'centered cap=',cap)
assert all(row['gates'].values()) and before<=cap<after
print('A cap on accumulated state modulo t is not the fixed 4-bit operand invariant used by matvec_tiles.')

print('\nOMITTED ENVELOPE COMPUTATION')
for custody in ['fhe+mpc-boundary','mpc-only']:
 mod='RNS-202@8192' if custody.startswith('fhe') else 'RNS3-109@4096'
 row=dark['price'](mod,False,custody,'public','lowrank',16,.01,4096,32)
 N,_,limbs,*_=dark['MODULI'][mod]
 o=dark['step_ops']('lowrank','public',16,4096,32,N)
 if custody.startswith('fhe'):
  envct=2*math.ceil(o['env']/N)
  extra=envct*10*N*math.log2(N)*len(limbs)
  print(custody,'env_ctct',envct,'host increment',extra,'fraction',extra/row['host_work'])
 else:
  extra=o['env']*(1+dark['C_PRE'])
  traffic=2*dark['NPARTY']*o['env']
  print(custody,'env square triples',o['env'],'host increment',extra,'fraction',extra/row['host_work'],'online increment',traffic,'fraction',traffic/row['online_elems'])
