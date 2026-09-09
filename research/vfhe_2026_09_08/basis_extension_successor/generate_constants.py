"""Extract and check public constructor constants; authors no matrix equations."""
from pathlib import Path
import hashlib,json,math,re
p=Path(__file__).resolve().parent
native=p.parent/'full_bfv_multiply_successor/results/case001/native_extension_constants.json'
capture=json.loads(native.read_text());debug=capture['native_RnsScaler_constructor_debug']
def array(name):
    start=debug.index('    '+name+': [')+len('    '+name+': ')
    level=0
    for i in range(start,len(debug)):
        if debug[i]=='[':level+=1
        elif debug[i]==']':
            level-=1
            if level==0:return json.loads(re.sub(r',\s*]',']',debug[start:i+1]))
    raise ValueError(name)
base=capture['base'];extended=capture['extended_base'];Q=math.prod(base)
G=[Q//q*pow(Q//q,-1,q) for q in base]
theta=[lo+(hi<<64) for lo,hi in zip(array('theta_garner_lo'),array('theta_garner_hi'))]
shift=int(re.search(r'theta_garner_shift: (\d+)',debug)[1])
assert shift==127 and theta==[((g<<shift)+Q//2)//Q for g in G]
assert array('gamma')==[Q%q for q in extended]
assert array('omega')==[[g%q for g in G] for q in extended]
assert array('theta_omega_lo')==[0]*4 and array('theta_omega_hi')==[0]*4
assert 'theta_gamma_lo: 0,' in debug and 'theta_gamma_hi: 0,' in debug and 'is_one: true,' in debug
data=dict(base=base,target=extended[4:],gamma=Q,omega=G,theta=theta,denominator=1<<127,
    quotient_offset=1<<194,native_gamma=array('gamma')[4:],native_omega=array('omega')[4:],
    constructor_sha256=hashlib.sha256(native.read_bytes()).hexdigest(),all_native_constants_match=True)
(p/'results/constants.json').write_text(json.dumps(data,indent=2)+'\n')
vec=lambda xs:'!['+','.join(map(str,xs))+']'
src='''import Compiler.ExactBasisExtension
import Compiler.ProfiledAutoCapacity
import Mathlib.Algebra.BigOperators.ModEq

namespace Minidregg.Compiler.ActualBasisExtension
open Minidregg.Compiler Minidregg.Compiler.NativeKernelPlan
open Minidregg.Compiler.SignedMatrix Minidregg.Compiler.ExactBasisExtension
open scoped BigOperators
set_option autoImplicit false
set_option maxRecDepth 30000
set_option maxHeartbeats 2000000

def params : Params 4 5 where
'''
for f,k in [('source','base'),('target','target'),('gamma','gamma'),('omega','omega'),('theta','theta'),('denominator','denominator'),('quotientOffset','quotient_offset')]:
    value=data[k];src+='  '+f+' := '+(vec(value) if isinstance(value,list) else str(value))+'\n'
src+='''
def profile : Layout := ⟨30,22,20,9,0,0⟩
def rows (i : Fin profile.rows) : Row profile.groups :=
  (forms params).get ⟨i.val,by change i.val<20;exact i.isLt⟩

'''
src+='def nativeGamma : Fin 5 → Int := '+vec(data['native_gamma'])+'\n'
src+='def nativeOmega : Fin 5 → Fin 4 → Int := !['+','.join(vec(v) for v in data['native_omega'])+']\n\nend Minidregg.Compiler.ActualBasisExtension\n'
(p/'Compiler/ActualBasisExtension.lean').write_text(src)
print(json.dumps({'native_constants_match':True,'source_moduli':4,'new_moduli':5,'shift':shift}))
