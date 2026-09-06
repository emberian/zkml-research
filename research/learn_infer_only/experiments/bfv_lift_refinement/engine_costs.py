#!/usr/bin/env python3
"""Exact naive range/arity bill for the pinned source arithmetic; no emitted circuit claim."""
import hashlib,json,sys
from math import prod
from pathlib import Path
from fhe_scaler_model import ScalerModel
ROOT=Path(__file__).resolve().parent
base=[68719403009,68719230977,137438822401]
extbase=base+[4611686018427322369,4611686018427289601,4611686018427215873]
q=prod(base);t=1032193;s=ScalerModel(extbase,base,t,q);N=4096

def interval(weights):
 return sum((p-1)*min(0,w) for p,w in zip(extbase,weights)),sum((p-1)*max(0,w) for p,w in zip(extbase,weights))
def family(name,lo,hi):
 width=(hi-lo).bit_length();return dict(name=name,minimum=str(lo),maximum=str(hi),offset_bits=width,radix64_digits=(width+5)//6,naive_bit_checks_over_3N=width*3*N)
glo,ghi=interval(s.tgarner);flo,fhi=interval(s.tomega);slo,shi=interval(s.omega)
vmax=(ghi+(1<<(s.shift-1)))//(1<<s.shift)
wmin=(flo+(1<<126))//(1<<127);wmax=(fhi+(1<<126))//(1<<127)
ranges=[family('Garner fixed accumulator Tg',glo,ghi),family('signed fixed correction T',flo,fhi),family('selected index v',0,vmax),family('signed rounded correction w',wmin,wmax),family('integer projection sum S',slo,shi)]
result=dict(label='DERIVED exact naive source-arithmetic arity/range bill, computed here; no emitted circuit, latency, or lower-bound claim',command=[sys.executable,str(Path(__file__).resolve())],source_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),N=N,Q=str(q),P=str(prod(extbase)),Q_bits=q.bit_length(),P_bits=prod(extbase).bit_length(),t=t,input_limb_bits=[(p-1).bit_length() for p in extbase],ranges=ranges,
 source_downscale_arities=dict(output_coefficients=3*N,garner_constant_products_per_coefficient=6,correction_constant_products_per_coefficient=6,nonzero_correction_constant_products_per_coefficient=3,projected_modular_constant_products_per_coefficient=6*3,garner_products_total=6*3*N,correction_loop_products_total=6*3*N,nonzero_correction_products_total=3*3*N,projected_modular_products_total=18*3*N),
 source_extension_arities=dict(input_coefficients=4*N,garner_constant_products_per_coefficient=3,new_output_limbs_per_coefficient=3,projected_modular_constant_products_per_coefficient=9,garner_products_total=3*4*N,projected_modular_products_total=9*4*N),
 fixed_approximation_error=dict(description='Normalized positive error from ceil projections is at most sum of residues with nonzero residual divided by 2^127. This tiny nonzero error still crosses exact rounding boundaries.',strict_numerator_bound=sum(base),denominator=str(1<<127)),
 residuals=['Ranges above use only independent canonical limb bounds and need not be simultaneously tight.', 'Choosing which intermediates to witness is a compiler decision; do not add all figures to the first-reference certificate as a mandatory cost.', 'Integer reconstruction, carry propagation, exact endpoint comparison, convolution/NTT relations, transcript binding and proof overhead are not included.', 'Constants multiply witnesses; they are not arbitrary witness-by-witness products. A scalar field equation still needs a no-wrap or limb argument.'])
print(json.dumps(result,indent=2))
