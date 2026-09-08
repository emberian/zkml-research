"""Exhaust finite function tables and verifier relations; no cryptographic hashes."""
from itertools import product
from fractions import Fraction
from pathlib import Path
import json

HERE = Path(__file__).resolve().parent
out = {'scope': 'Finite mathematical controls only; no cryptographic hash or attack execution.'}
counterexamples = []
for n in [2, 3]:
    total = bad_at_zero = bad_at_either = observed_conflicts = 0
    for leaf in product(range(n), repeat=2):
        for entries in product(range(n), repeat=n*n):
            node = lambda a,b: entries[a*n+b]
            root = node(leaf[0], leaf[0])
            total += 1
            bad_zero = any(node(leaf[1], sibling) == root for sibling in range(n))
            bad_one = any(node(sibling, leaf[1]) == root for sibling in range(n))
            bad_at_zero += bad_zero
            bad_at_either += bad_zero or bad_one
            # The supplied transcript always has one opening (v0, sibling=leaf(v0)).
            assert node(leaf[0], leaf[0]) == root
    exact_zero = 1 - Fraction(n-1, n)**(n+1)
    exact_either = 1 - Fraction(n-1, n)**(2*n)
    assert Fraction(bad_at_zero,total) == exact_zero
    assert Fraction(bad_at_either,total) == exact_either
    counterexamples.append({'digest_cardinality': n, 'function_tables': total,
                           'fixed_index_zero_bad_tables': bad_at_zero,
                           'fixed_index_zero_bad_probability': str(exact_zero),
                           'semantic_DoubleOpening_tables': bad_at_either,
                           'semantic_DoubleOpening_probability': str(exact_either),
                           'observed_conflicting_pairs': observed_conflicts})
out['semantic_counterexamples'] = counterexamples

inputs = [('L',0), ('L',1)] + [('N',a,b) for a,b in product(range(2),repeat=2)]
prefix_checked = mismatch_cases = bad_trace_cases = 0
for responses in product(range(2), repeat=len(inputs)):
    table = dict(zip(inputs,responses))
    for length in range(3):
        for prefix in product(inputs,repeat=length):
            cache = {}
            for x in prefix: cache.setdefault(x,table[x])
            for root in range(2):
                def extracted(index):
                    pairs = [x for x,y in cache.items() if x[0]=='N' and y==root]
                    if not pairs: return 0
                    target = pairs[0][1+index]
                    leaves = [x for x,y in cache.items() if x[0]=='L' and y==target]
                    return leaves[0][1] if leaves else 0
                for index,value,sibling in product(range(2),repeat=3):
                    leaf_digest = table[('L',value)]
                    node_input = ('N',leaf_digest,sibling) if index==0 else ('N',sibling,leaf_digest)
                    if table[node_input] != root: continue
                    full = list(prefix)+[('L',value),node_input]
                    log = {}; targets=set(); flagged=False
                    for pos,x in enumerate(full):
                        if pos==len(prefix): targets.add(root)
                        if x in log: continue
                        if x[0]=='N': targets.update(x[1:])
                        y=table[x]
                        if y in log.values() or y in targets: flagged=True
                        log[x]=y
                    mismatch = value != extracted(index)
                    assert not mismatch or flagged
                    prefix_checked += 1
                    mismatch_cases += mismatch
                    bad_trace_cases += flagged
out['prefix_extraction'] = {'accepted_opening_cases':prefix_checked,
                           'mismatches':mismatch_cases,'flagged_trace_cases':bad_trace_cases,
                           'unflagged_mismatches':0}
# Exact worst-case union numerator from t-th fresh response target count 3t-1+R.
budget_checks=0
for q in range(51):
    for roots in range(21):
        assert sum(3*t-1+roots for t in range(1,q+1)) == (3*q*q+q)//2+roots*q
        budget_checks += 1
out['union_budget_integer_checks'] = budget_checks
# Nonvacuity: a small collision-free checkpoint log resolves an actually far F5 word.
log = [(('L',1),10),(('L',4),11),(('N',10,11),20),
       (('N',11,10),21),(('N',20,21),30)]
def resolve(index):
    digest=30
    for bit in [index & 1,(index >> 1) & 1]:
        query=next(x for x,y in log if x[0]=='N' and y==digest)
        digest=query[1+bit]
    return next(x[1] for x,y in log if x[0]=='L' and y==digest)
word=[resolve(i) for i in range(4)]
assert word==[1,4,4,1]
responses=set();targets=set()
for query,response in log:
    if query[0]=='N': targets.update(query[1:])
    assert response not in responses and response not in targets
    responses.add(response)
distances=[sum(v!=(a*x+b)%5 for x,v in zip([1,2,3,4],word))
           for a,b in product(range(5),repeat=2)]
assert min(distances)==2
accepted=0
for challenge,section in product(range(5),[1,2]):
    left=word[section-1];right=word[(-section)%5-1]
    folded=((left+right)*3+challenge*(left-right)*pow(2*section,-1,5))%5
    accepted += folded==1  # transparent terminal constant chosen before query
assert accepted==5
out['nonvacuity_F5']={'checkpoint_word':word,'checkpoint_unflagged':True,
                      'affine_codewords_checked':25,'distance':str(Fraction(min(distances),4)),
                      'one_query_accepted':accepted,'challenge_query_pairs':10,
                      'scope':'Far initial extracted word and prefix-fixed terminal/raw openings; not all 19-round premises.'}
rendered=json.dumps(out,indent=2)+'\n'
(HERE/'RESULTS.json').write_text(rendered)
print(rendered,end='')
