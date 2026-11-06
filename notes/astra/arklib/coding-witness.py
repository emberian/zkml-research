#!/usr/bin/env python3
"""Exact rational side conditions for source-audited ArkLib MCA witnesses.
Not a Lean/kernel check; no finite-code exhaustive enumeration is claimed.
"""
from fractions import Fraction as Q
from math import isqrt
q, n, k = 1_000_003, 16, 5
prime = q > 1 and all(q % d for d in range(2, isqrt(q)+1))
assert prime
rho = Q(k-1,n)
sqrt_rho = Q(1,2)
assert sqrt_rho**2 == rho
ud = Q(n-k,2*n)
one_third = Q(n-k,3*n)
delta_ud = Q(5,16)
delta_j = Q(3,8)
eta = 1-sqrt_rho-delta_j
ratio = sqrt_rho/eta
m = max(-(-ratio.numerator//ratio.denominator),3)
shift = m + Q(1,2)
comparison_numerator = ((2*shift**5+3*shift*delta_j*rho)/(3*sqrt_rho**3)*n+shift/sqrt_rho)
bound = comparison_numerator/q
assert one_third < delta_ud <= ud
assert ud < delta_j < 1-sqrt_rho
assert Q(k,n) < (1-delta_j)**2  # also below Selvage rounded Johnson radius
assert 0 < bound < 1
print(f'q={q}, trial-division prime={prime}; n={n}; dimension k={k}; domain i |-> i mod q')
print(f'UDR={ud}, local one-third limit={one_third}, witness delta_ud={delta_ud}, ArkLib epsilon={Q(n,q)}')
print(f'Johnson rho_minus={rho}, sqrt={sqrt_rho}, delta={delta_j}, eta={eta}, m={m}')
print(f'Johnson printed comparison numerator={comparison_numerator}; epsilon={bound} = {float(bound):.12g} < 1')
print(f'Nonzero bad-event witness: f0=0, f1=X^{k}; exact probability 1/q={Q(1,q)} by root counting')
# BCIKS CA witnesses, in its cheap UDR branch. Curves have k_curve multiplier.
print(f'BCIKS line/space delta=1/4, epsilon={Q(n,q)}; quadratic curve epsilon={Q(2*n,q)}')
# Original suggested toy cannot falsify nontriviality using the printed Johnson bound.
# n=16,k=4 => rho=3/16<1; m>=3; delta>=0, so comparison_numerator/q > (2*(7/2)^5/3)*16/17.
old_lower = 2*Q(7,2)**5*16/Q(3*17)
assert old_lower > 1
print(f'Old ZMod17,n16,k4 printed Johnson epsilon > {old_lower} > 1 for every allowed delta')
