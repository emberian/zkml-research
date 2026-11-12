#!/usr/bin/env python3
"""Generate narrow repairs; source trees are never modified."""
from pathlib import Path
import difflib
patch=[]
def repair(path,edits):
 old=Path(path).read_text();new=old
 for a,b in edits:
  assert new.count(a)==1,(path,a)
  new=new.replace(a,b)
 compile(new,path,'exec')
 patch.extend(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
 return new
space=repair('notes/construction-search/space.py',[
 ('tc_share = min(1.0, (tc_cell * commit + S["virt"] * PIOP[piop]["virt_mult"]) / max(mults, 1))',
  '# Eligible work and total work must use the same audit amortization.\n        tc_share = min(1.0, p * (tc_cell * commit + S["virt"] * PIOP[piop]["virt_mult"]) / max(mults, 1))'),
 ('pq = field != "lattice-Rq" or True','pq = None  # Unknown: requires a scheme, parameter set, and adversary model; field choice cannot certify PQ.')])
dark=repair('notes/dark-learning-scripts/tradeoff_space.py',[
 ('W_BITS, A_BITS = 4, 4        # integer recipe: signed 4-bit weights-or-factors and activations (F1) [MODEL]',
  'W_BITS, A_BITS = 4, 4        # [MODEL] symmetric signed recipe, excludes -2^(bits-1); not the full signed range'),
 ('host = o["ctct"] * W_CTCT + o["ctpt"] * W_CTPT + act * KAPPA * C_PRE',
  'host = (o["ctct"] + env_ctct) * W_CTCT + o["ctpt"] * W_CTPT + act * KAPPA * C_PRE'),
 ('host = (o["ctct"] + 15 * boots * (1 + KAPPA)) * W_CTCT + o["ctpt"] * W_CTPT',
  'host = (o["ctct"] + env_ctct + 15 * boots * (1 + KAPPA)) * W_CTCT + o["ctpt"] * W_CTPT'),
 ('host = lin + (triples + act * KAPPA) * C_PRE\n        online = 2 * NPARTY * (triples + act * KAPPA)',
  '# Mandatory envelope squares consume triples and communication even when step proofs are sampled.\n        host = lin + o["env"] + (triples + o["env"] + act * KAPPA) * C_PRE\n        online = 2 * NPARTY * (triples + o["env"] + act * KAPPA)'),
 ('assert ((T - 1) // 2) // (7 * 127 + 137) <= 504 + 100',
  'assert ((T - 1) // 2) // (8 * 128) == 504  # deployed full signed 4 x 8-bit bound\n    assert ((T - 1) // 2) // (7 * 127) == 580  # distinct symmetric-range recipe used here')])
act=repair('notes/dark-learning-scripts/backward_table_virtualization.py',[
 ('Pure Python, no deps. Semantics: exact real function of the bf16 input, rounded once to bf16\n(round-to-nearest-even), which is the "exact 2^16 table" semantics the project uses for forward tables.\nNaN/inf inputs excluded. Prints counts, not timings.',
  'Pure Python, no deps. Semantics: binary64/libm approximations at bf16 inputs, converted through\nbinary32 then bf16. Cancellation and double rounding occur; these counts are NOT a certified\nexact-real, single-rounding table census. NaN/inf inputs excluded. Prints counts, not timings.'),
 ('print("spec\'s derivative at those codes; the repair is to key the backward lookup on the INPUT code (the forward")',
  'print("implemented derivative at those codes; the repair is to key the backward lookup on the INPUT code (the forward")')])
Path('notes/astra/counts-model-repairs.patch').write_text(''.join(patch))
# Execute the corrected models in memory; keep outputs beside the patch.
from contextlib import redirect_stdout
import io,sys
for name,src in [('space',space),('tradeoff',dark),('activation',act)]:
 ns={'__name__':'audit_patched_'+name};exec(compile(src,'<patched-'+name+'>','exec'),ns)
 buf=io.StringIO()
 with redirect_stdout(buf):
  if name=='space':
   ns['_calibrate_witgen']()
   for point in ('U1','U1-per-request','SASH-anchor'):
    print(point,ns['evaluate'](**ns['NAMED'][point]))
  else:
   oldargs=sys.argv;sys.argv=[name]
   try: ns['main']()
   finally: sys.argv=oldargs
 Path('notes/astra/counts/patched-'+name+'.stdout.txt').write_text(buf.getvalue())
print('Generated syntactically checked patch and ran three repaired scripts in memory.')
