"""Exact finite dynamics of the already frozen learner; no tuning or crypto."""
import hashlib
import json
from fractions import Fraction
from pathlib import Path

ROOT=Path(__file__).resolve().parent
step=lambda s,u:(7*s+u)//8
sign=lambda s:1 if s>=0 else -1
def orbit(s,u):
    out=[s]
    while step(out[-1],u)!=out[-1]:
        out.append(step(out[-1],u))
        assert len(out)<=241
    return out

reachable={0}
while True:
    grown=reachable|{step(s,u) for s in reachable for u in [-120,120]}
    if grown==reachable:break
    reachable=grown
assert all(-120<=step(s,u)<=120 for s in range(-120,121) for u in [-120,120])
constant=[]
for u in [-120,120]:
    trajectories=[orbit(s,u) for s in range(-120,121)]
    first_correct=[]
    for s in range(-120,121):
        z=s;n=0
        while sign(z)!=sign(u):z=step(z,u);n+=1
        first_correct.append(n)
    constant.append({'u':u,'fixed_points_in_invariant_range':[s for s in range(-120,121) if step(s,u)==s],
                     'zero_start_orbit':orbit(0,u),'zero_start_fixed_point':orbit(0,u)[-1],
                     'max_selected_steps_until_correct_sign_all_range_states':max(first_correct),
                     'max_steps_until_fixed_point_all_range_states':max(len(t)-1 for t in trajectories),
                     'max_steps_until_fixed_point_reachable_states':max(len(orbit(s,u))-1 for s in reachable)})
rounding=[]
for s in range(-120,121):
    for u in [-120,120]:
        q=Fraction(7*s+u,8);residual=Fraction(step(s,u))-q
        assert Fraction(-7,8)<=residual<=0
        rounding.append(residual)
# The finite domain also verifies monotonicity, which supports endpoint witnesses.
for u in [-120,120]:
    assert all(step(s,u)<=step(s+1,u) for s in range(-120,120))
out={'scope':'exact finite arithmetic of fixed law, no new utility/model/crypto experiment',
     'range_states':241,'state_label_cases':482,'reachable_states_from_zero':sorted(reachable),
     'reachable_count':len(reachable),'constant_label_dynamics':constant,
     'rounding_residual_min':str(min(rounding)),'rounding_residual_max':str(max(rounding)),
     'positive_worst_endpoint_orbit':orbit(-120,120)[:7],
     'negative_worst_endpoint_orbit':orbit(120,-120)[:7],
     'scope_falsifier_for_arbitrary_range_exact_forgetting':{'u':120,'states':[113,120],
              'same_successor_states':[step(113,120),step(120,120)],
              '120_reachable_from_zero':120 in reachable},
     'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()}
(ROOT/'fixed_law.json').write_text(json.dumps(out,indent=2,sort_keys=True)+'\n')
print({k:v for k,v in out.items() if k not in ['reachable_states_from_zero','constant_label_dynamics']})
print(constant)
