#!/usr/bin/env python3
"""Read-only frozen-source audit and independent, finite field arithmetic checks.

This does not build Lean or run any cryptographic implementation. The existing
integration census is reused as an instrument, not as an independent parser.
"""
from pathlib import Path
import hashlib
import importlib.util
import itertools
import json
import re
import subprocess
import sys
from fractions import Fraction

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
FORMAL = REPO / 'research/proof_frontier/2026-09-08/formal'
FULL = FORMAL / 'full_ud'
MAIN = Path('/Users/ember/dev/minidregg')

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def save(name, value):
    (HERE / name).write_text(json.dumps(value, indent=2) + '\n')

spec = importlib.util.spec_from_file_location('integration_census',
    REPO / 'research/learn_infer_only/experiments/integration/check_all_formal.py')
census_tool = importlib.util.module_from_spec(spec)
spec.loader.exec_module(census_tool)
manifest = json.loads((FULL / 'manifest.json').read_text())
expected_patch = '1e7a4c2292766f8b02a80879ef288915d610b67b5c070d8892db8661a8146cb2'
assert sha(FULL / 'full-ud.patch') == expected_patch
sources = {}
for item in manifest['modules']:
    name = item['path']
    if item['owned']:
        p = FULL / 'src' / name
    elif name == 'Theory/PolynomialMatrixKernel.lean':
        p = FORMAL / 'polynomial_kernel/all_pins_successor/PolynomialMatrixKernel.lean'
    else:
        p = FORMAL / 'polynomial_gluing/universe_successor' / Path(name).name
    assert sha(p) == item['sha256'], name
    sources[name[:-5].replace('/', '.')] = p

censuses = {}
for module, p in sources.items():
    censuses[module] = dict(path=str(p), sha256=sha(p),
                           **census_tool.census(p.read_text(), module))
save('census.json', censuses)

# Check the actual additions in the patch against source bytes without applying
# anything or relying on the original lane's patch-check script.
patched = {}
for section in (FULL / 'full-ud.patch').read_text().split('diff --git ')[1:]:
    lines = section.splitlines(keepends=True)
    assert 'new file mode 100644\n' in lines
    assert '--- /dev/null\n' in lines
    target = next(x.strip()[6:] for x in lines if x.startswith('+++ b/'))
    start = next(i for i, x in enumerate(lines) if x.startswith('@@'))
    assert all(x.startswith('+') for x in lines[start+1:])
    content = ''.join(x[1:] for x in lines[start+1:]).encode()
    assert content == (FULL / 'src' / target).read_bytes(), target
    patched[target] = hashlib.sha256(content).hexdigest()
assert len(patched) == manifest['owned_modules'] == 10

# Record the complete project import closure separately from theorem proof
# dependencies. Imported unrelated declarations do not receive closure credit.
closure = {}
def visit(module):
    if module in closure or module.startswith(('Mathlib.', 'Lean.', 'Std.', 'Batteries.')):
        return
    p = sources.get(module, MAIN / (module.replace('.', '/') + '.lean'))
    if not p.exists():
        raise FileNotFoundError((module, p))
    imports = census_tool.imports(p.read_text())
    closure[module] = dict(path=str(p), sha256=sha(p), imports=imports,
                          frozen_proposal=module in sources)
    for dep in imports:
        visit(dep)
for module in sources:
    visit(module)
save('import_closure.json', closure)

# Stored exact-byte Lean checks are evidence from the producer, not new builds.
checks = []
for i in range(1, 15):
    p = FULL / 'logs' / f'freeze-{i:02}.json'
    item = json.loads(p.read_text())
    target = item['command'][-1][:-5].replace('/', '.')
    assert item['exit_code'] == 0 and item['source_unchanged']
    assert item['source_sha256'] == sha(sources[target])
    log = FULL / 'logs' / f'freeze-{i:02}.log'
    assert not re.search(r'\berror:', log.read_text())
    checks.append(dict(record_sha256=sha(p), log_sha256=sha(log),
                       module=target, exit_code=item['exit_code']))

def word(p, dom, coefficients):
    return tuple(sum(a * pow(x, k, p) for k, a in enumerate(coefficients)) % p for x in dom)

def dist(a, b):
    return sum(x != y for x, y in zip(a, b))

def interpolate_word(p, dom, values, subset):
    def at(x):
        result = 0
        for i in subset:
            num = den = 1
            for j in subset:
                if i != j:
                    num = num * (x-dom[j]) % p
                    den = den * (dom[i]-dom[j]) % p
            result += values[i] * num * pow(den, -1, p)
        return result % p
    return tuple(at(x) for x in dom)

def nearest(p, dom, values, d):
    # Every maximum-agreement degree<d codeword has >=d agreements (Lagrange),
    # and is determined by some such d-subset, so this finite list is complete
    # for the minimum-distance calculation, though not the full codebook.
    candidates = {interpolate_word(p, dom, values, s)
                  for s in itertools.combinations(range(len(dom)), d)}
    return min(dist(values, w) for w in candidates)

# The frozen radius falsifier, independently enumerating all affine codewords.
p = 7
dom = tuple(range(6))
f0, f1 = (3,0,4,1,3,3), (6,4,1,1,6,3)
code = [word(p, dom, (a,b)) for a,b in itertools.product(range(p), repeat=2)]
fold_minima = [min(dist(tuple((x+z*y)%p for x,y in zip(f0,f1)), w) for w in code)
               for z in range(p)]
joint_maximum = max(sum(f0[i] == a[i] and f1[i] == b[i] for i in range(6))
                    for a,b in itertools.product(code, repeat=2))
assert all(d <= 3 for d in fold_minima) and joint_maximum == 2
falsifier = dict(p=p, n=6, d=2, e=3, folds=7, codewords=49,
    codeword_pairs=2401, fold_minima=fold_minima, joint_maximum=joint_maximum,
    required_common=3, degree_positive=True, good_card_gt_n=True,
    radius_premise=False)

# A nonzero-error augmentation of the supplied all-codeword premise witness.
# All slopes have at most two errors on the same positions, and the common
# agreement size is exactly six. A one-error version fires at delta=1/5.
noisy = []
for e in (1,2):
    p, dom = 11, tuple(range(8))
    a = tuple((x + (1 if i < e else 0)) % p for i,x in enumerate(dom))
    b = tuple((1 + (2 if i < e else 0)) % p for i in range(8))
    folds = [tuple((x+z*y)%p for x,y in zip(a,b)) for z in range(p)]
    minima = [nearest(p, dom, f, 4) for f in folds]
    joint = max(sum(a[i] == wa[i] and b[i] == wb[i] for i in range(8))
        for subset in itertools.combinations(range(8), 4)
        for wa,wb in [(interpolate_word(p, dom, a, subset),
                       interpolate_word(p, dom, b, subset))])
    assert max(minima) == e and joint == 8-e
    assert 2*e+4 <= 8 and len(minima) > 8
    noisy.append(dict(p=p,n=8,d=4,e=e,f0=a,f1=b,fold_minima=minima,
        min_dist_f0=nearest(p, dom, a, 4), min_dist_f1=nearest(p, dom, b, 4),
        joint_maximum=joint, integer_premises=True,
        probability_delta_one_fifth=str(Fraction(sum(Fraction(v,8)<=Fraction(1,5) for v in minima),11))))

# An actual two-round, positive-tail, rate-half tower. Pure prime-field
# arithmetic uses precisely the existing fold equations (including 2*x).
p = 97
root = next(x for x in range(1,p) if pow(x,8,p)==1 and pow(x,4,p)!=1)
levels = [tuple(sorted({pow(root,i,p) for i in range(8)}))]
levels += [tuple(sorted({x*x%p for x in levels[0]}))]
levels += [tuple(sorted({x*x%p for x in levels[1]}))]
assert [len(x) for x in levels] == [8,4,2]
for big, small in zip(levels, levels[1:]):
    assert all(x and (-x)%p in big for x in big)
    assert set(x*x%p for x in big)==set(small)
    assert all(sum(x*x%p==y for x in big)==2 for y in small)
def fold(big, small, values, alpha):
    table = dict(zip(big,values))
    result = []
    for y in small:
        x = next(x for x in big if x*x%p == y)
        u,v = table[x],table[-x%p]
        result.append(((u+v)*pow(2,-1,p)+alpha*(u-v)*pow(2*x,-1,p))%p)
    return tuple(result)
c = next(c for c in range(1,p)
         if nearest(p,levels[0],word(p,levels[0],(0,0,0,0,1,c)),4) == 4)
top = word(p, levels[0], (0,0,0,0,1,c))
assert Fraction(nearest(p,levels[0],top,4),8) > Fraction(2,5)
accepted = []
bad_first = []
tail_counts = []
for alpha in range(p):
    mid = fold(levels[0],levels[1],top,alpha)
    md = nearest(p,levels[1],mid,2)
    if Fraction(md,4) <= Fraction(1,5):
        bad_first.append(alpha)
    count = 0
    for beta in range(p):
        last = fold(levels[1],levels[2],mid,beta)
        accept = len(set(last)) == 1
        if accept:
            accepted.append((alpha,beta))
            count += 1
    if Fraction(md,4) > Fraction(1,5):
        assert count <= len(levels[2])
        tail_counts.append(count)
assert len(bad_first) == 1 and len(accepted) == p
bound = 2*8*p
assert len(accepted) <= bound < p**2
tower = dict(p=p, root_order_8=root, levels=levels, degrees=[4,2,1],
    m=2, delta='2/5', tail_delta='1/5', tail_rate='1/2',
    source_coefficients=[0,0,0,0,1,c], source_word=top,
    min_source_distance=4, source_relative_distance='1/2',
    first_bad_challenges=bad_first, far_tail_words=len(tail_counts),
    tail_bad_counts=sorted(set(tail_counts)), challenge_tuples=p**2,
    accepted_count=len(accepted), accepted_first_challenges=sorted({a for a,b in accepted}),
    acceptance_numerator_bound=bound, uniform_acceptance_probability=str(Fraction(len(accepted),p**2)),
    uniform_probability_bound=str(Fraction(bound,p**2)),
    new_band=Fraction(1,5)<Fraction(1,4), old_band=Fraction(1,5)<Fraction(1,6))
save('finite_checks.json', dict(falsifier=falsifier,noisy_witnesses=noisy,tower=tower,
    status='PASS; independent exact integer/finite-field execution, not new Lean proof'))

result = dict(status='PASS', patch_sha256=expected_patch, source_modules=len(sources),
    owned_modules=10, owned_theorems=sum(censuses[m]['theorem_count'] for m in sources if '/full_ud/' in str(sources[m])),
    all_theorems=sum(x['theorem_count'] for x in censuses.values()),
    all_pins=sum(x['pin_count'] for x in censuses.values()),
    project_import_closure_modules=len(closure), exact_patch_files=patched,
    stored_lean_checks=checks, new_lean_builds=0, external_queries=0,
    instrumentation_sha256=sha(Path(census_tool.__file__)), review_script_sha256=sha(Path(__file__)),
    finite_checks_sha256=sha(HERE/'finite_checks.json'))
save('verification.json', result)
print(json.dumps({k:v for k,v in result.items() if k not in ('exact_patch_files','stored_lean_checks')}, indent=2))
