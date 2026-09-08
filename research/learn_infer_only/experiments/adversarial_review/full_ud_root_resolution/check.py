#!/usr/bin/env python3
"""Read-only package audit plus bounded public finite semantic checks.

No Lean build, cryptographic backend, Rust execution, private inputs or network.
"""
from pathlib import Path
from itertools import product
from fractions import Fraction
import hashlib
import json
import re

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[4]
PACKAGE = REPO/'research/proof_frontier/2026-09-08/formal/full_ud_commitment_timing'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
manifest = json.loads((PACKAGE/'manifest.json').read_text())
patch = PACKAGE/'full-ud-commitment-timing.patch'
assert sha(patch) == manifest['patch_sha256'] == '449608f151061051d3c2567d86d6b505c86ecf03906f990ffb7a5238995e4756'
names = json.loads((PACKAGE/'declaration-names.json').read_text())

# All files in this patch are new modules. Reconstruct exact added bytes without
# applying the patch or touching any checkout.
reconstructed = {}
current = None
for line in patch.read_text().splitlines(keepends=True):
    if line.startswith('diff --git '):
        current = None
    elif line.startswith('+++ b/'):
        current = line[len('+++ b/'):].strip()
        assert current not in reconstructed
        reconstructed[current] = ''
    elif current is not None and line.startswith('+'):
        reconstructed[current] += line[1:]
    elif current is not None and line.startswith('-'):
        raise AssertionError('Expected additive patch only')

census = []
for item in manifest['modules']:
    source = PACKAGE/'src'/item['path']
    content = source.read_text()
    assert sha(source) == item['sha256'] == item['check']['source_sha256']
    assert reconstructed[item['path']].encode() == source.read_bytes()
    uncommented = re.sub(r'/\-.*?\-/', '', content, flags=re.S)
    uncommented = re.sub(r'--[^\n]*', '', uncommented)
    declarations = re.findall(r'^\s*(?:private\s+)?(?:theorem|lemma)\s+([^\s(:]+)', uncommented, flags=re.M)
    guards = re.findall(r'#guard_msgs[^\n]*#print axioms\s+([^\s]+)', uncommented)
    expected = names[source.stem]
    assert len(set(guards)) == len(guards)
    assert sorted(guards) == sorted(expected)
    assert sorted(x.rsplit('.',1)[-1] for x in guards) == sorted(declarations)
    assert len(declarations) == item['theorem_count'] == item['pin_count']
    assert not re.search(r'\b(?:sorry|axiom|native_decide|admit)\b', uncommented)
    assert len(re.findall(r'#print axioms',uncommented)) == len(guards)
    assert item['check']['exit_code'] == 0 and item['check']['source_unchanged']
    log = Path(item['check']['log'])
    assert log.read_bytes() == b''
    for axiom_list in re.findall(r'depends on axioms: \[([^]]*)\]',content):
        assert set(x.strip() for x in axiom_list.split(',')) <= {'propext','Classical.choice','Quot.sound'}
    census.append({'path':item['path'],'sha256':sha(source),'declarations':len(declarations),
                   'exact_guarded_pins':len(guards),'saved_final_check_exit':0,'saved_log_bytes':0,
                   'patch_reconstructs_exact_source':True})
assert len(reconstructed) == len(census) == 5
assert sum(x['declarations'] for x in census) == 36

source_evidence = json.loads((PACKAGE/'source-evidence.json').read_text())
source_pins = []
for path, item in source_evidence['sources'].items():
    p = Path(path)
    assert sha(p) == item['sha256']
    source_pins.append({'path':str(p),'sha256':sha(p),'access':'named public source read at cited regions'})

dependency_pins = []
for item in manifest['dependencies']:
    p = Path(manifest['checkout'])/item['path']
    assert sha(p) == item['sha256']
    dependency_pins.append({'path':str(p),'sha256':sha(p),'access':'read-only source hash; mathematical dependencies audited previously'})
assert len(dependency_pins) == 16

# Exhaust every possible accepted-value relation on one extra root, two
# positions, two values. Such a root can be added to an ideal complete scheme.
# Check every permitted canonical choice, not a chosen deterministic tie rule.
subsets = [tuple(v for v in (0,1) if mask & (1 << v)) for mask in range(4)]
relations = resolver_choices = accepted_checks = 0
for relation in product(subsets, repeat=2):
    relations += 1
    bad = any(len(s) > 1 for s in relation)
    for word in product(*(s if s else (0,) for s in relation)):
        resolver_choices += 1
        for i, s in enumerate(relation):
            for v in s:
                accepted_checks += 1
                assert v == word[i] or bad
                if not bad:
                    assert v == word[i]
        for i, s in enumerate(relation):
            if not s:
                assert word[i] == 0
assert relations == 16 and resolver_choices == 25

# F5 binary multiplicative tower, same domain/section as the Lean witness.
p = 5
big = (1,2,3,4)
small = (1,4)
sections = (1,2)
def fold(w, a):
    def value(x): return w[big.index(x)]
    return tuple(((value(x)+value(-x%p))*pow(2,-1,p) +
                  a*(value(x)-value(-x%p))*pow(2*x,-1,p)) % p for x in sections)
assert all(x*x%p == small[i] for i,x in enumerate(sections))
xword = big
for a in range(p):
    assert fold(xword,a) == (a,a)
assert fold(xword,0) != fold(xword,1)
# Every challenge/query batch of lengths 0,1,2 accepts the tagged off-image
# X root and transparent challenge-valued final root.
accepted_witnesses = 0
for a in range(p):
    for count in (0,1,2):
        for queries in product(range(2),repeat=count):
            terminal = (a,a)
            assert all(fold(xword,a)[i] == terminal[i] for i in queries)
            accepted_witnesses += 1
assert accepted_witnesses == 35

# Source witness is a codeword. Independently show farness and raw acceptance
# can coexist in a small off-image strategy (not a 19-round BabyBear witness).
x2word = tuple(x*x%p for x in big)
code = [tuple((a+b*x)%p for x in big) for a,b in product(range(p),repeat=2)]
distance = min(Fraction(sum(x!=y for x,y in zip(x2word,w)),len(big)) for w in code)
assert distance == Fraction(1,2) > Fraction(2,5)
far_accepts = 0
query_dependent_accepts = 0
for a in range(p):
    terminal_value = small[a%2]  # chosen from prefix before the query
    terminal = (terminal_value,terminal_value)
    assert fold(x2word,a) == small
    for query in range(2):
        far_accepts += fold(x2word,a)[query] == terminal[query]
        # Invalid timing falsifier: choosing terminal AFTER the query wins all.
        cheating_terminal = (small[query],small[query])
        query_dependent_accepts += fold(x2word,a)[query] == cheating_terminal[query]
assert far_accepts == 5 and query_dependent_accepts == 10

# Semantic double opening can exist outside a single observed opening trace.
permissive_root_relation = {(0,0,'seen'), (0,1,'unseen')}
observed_trace = [(0,0,'seen')]
assert all(x in permissive_root_relation for x in observed_trace)
assert len({x[1] for x in observed_trace}) == 1
semantic_double_opening = any(i==j and v!=u for i,v,o in permissive_root_relation for j,u,o2 in permissive_root_relation)
assert semantic_double_opening

result = {'status':'PASS; source/census and finite semantics only',
          'patch_sha256':sha(patch),'script_sha256':sha(Path(__file__)),
          'modules':census,'source_pins':source_pins,'dependency_pins':dependency_pins,
          'resolver_relations':relations,'all_permitted_resolver_choices':resolver_choices,
          'accepted_value_checks':accepted_checks,
          'F5_source_witness_challenge_batches':accepted_witnesses,
          'F5_far_initial_word_distance':str(distance),
          'F5_far_prefix_selected_terminal_acceptance':str(Fraction(far_accepts,10)),
          'query_dependent_terminal_falsifier_acceptance':str(Fraction(query_dependent_accepts,10)),
          'semantic_double_opening_without_observed_conflict':semantic_double_opening,
          'lean_runs':0,'crypto_runs':0,'private_files_read':0,'web_queries':0,
          'scope':'No efficient extractor, collision advantage or runtime/Fiat-Shamir equivalence is established.'}
(HERE/'results.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
