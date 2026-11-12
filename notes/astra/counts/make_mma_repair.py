#!/usr/bin/env python3
from pathlib import Path
import difflib,io,subprocess
from contextlib import redirect_stdout
path=Path('/Users/ember/dev/degg-research/experiments/mma-field-mapping/mma_limbs.py')
# Reproduce the patch against its historical base after upstream application.
old=subprocess.check_output(['git','-C','/Users/ember/dev/degg-research','show',
    '15db9784e2043bb170431203f3c63d88625933e2:experiments/mma-field-mapping/mma_limbs.py'],text=True)
a='''def limbs(p, base, signed):
    # signed (balanced) digits need one extra limb of headroom in the worst case
    # balanced digits cover [-(b^L-1)/2, (b^L-1)/2], so they need b^L > 2p
    return math.ceil(math.log(2 * p + 1, base)) if signed else math.ceil(math.log(p, base))
'''
b='''def representatives(base, digitset):
    # Fix an encoder, not just a complete residue set.  Each quotient stays nonnegative.
    reps = {r: min((d for d in digitset if d % base == r and d <= r), key=abs)
            for r in range(base)}
    assert reps[0] == 0
    return reps

def limbs(p, base, digitset):
    """Certified upper count for this explicit quotient/remainder encoder on 0 <= x < p.
    If 0 <= q <= M and r is the chosen digit then
    0 <= (q-r)//base <= (M-min(reps))//base.  Stop when every possible final quotient
    is itself a digit.  The old balanced-interval formula was false for this gapped set.
    """
    assert p >= 2 and base >= 2
    reps = representatives(base, digitset)
    terminal = 0
    while terminal + 1 in digitset:
        terminal += 1
    bound, count = p - 1, 1
    while bound > terminal:
        nxt = (bound - min(reps.values())) // base
        if nxt >= bound:
            raise ValueError("digit set has no decreasing nonnegative quotient bound")
        bound, count = nxt, count + 1
    return count

def encode(x, base, digitset, count):
    reps = representatives(base, digitset)
    out = []
    for _ in range(count - 1):
        digit = reps[x % base]
        out.append(digit)
        x = (x - digit) // base
    assert x in digitset
    out.append(x)
    return out
'''
assert old.count(a)==1
new=old.replace(a,b).replace('L = limbs(p, base, signed)','L = limbs(p, base, ds)').replace('maxd = max(abs(d) for d in ds)', 'terminal = 0\n            while terminal + 1 in ds:\n                terminal += 1\n            maxd = max(terminal, max(abs(d) for d in representatives(base, ds).values()))')
new=new.replace('            P = L * L','            for x in (0, 1, p // 2, p - 1):\n                enc = encode(x, base, ds, L)\n                assert sum(d * base**i for i, d in enumerate(enc)) == x\n            P = L * L')
new=new.replace('    int8P = {}','    assert limbs(67, 13, SCHEMES[2][2]) == 3  # 65 had no two-digit representation\n    for x in range(67):\n        enc = encode(x, 13, SCHEMES[2][2], 3)\n        assert sum(d * 13**i for i, d in enumerate(enc)) == x\n    int8P = {}')
ns={'__name__':'repaired_mma'};exec(compile(new,str(path),'exec'),ns)
out=io.StringIO()
with redirect_stdout(out): ns['main']()
Path('notes/astra/counts/patched-mma.stdout.txt').write_text(out.getvalue())
rel='experiments/mma-field-mapping/mma_limbs.py'
Path('notes/astra/mma-representation.patch').write_text(''.join(difflib.unified_diff(old.splitlines(True),new.splitlines(True),fromfile='a/'+rel,tofile='b/'+rel)))
print('Generated mma-representation.patch; executed encoder controls and repaired table.')
