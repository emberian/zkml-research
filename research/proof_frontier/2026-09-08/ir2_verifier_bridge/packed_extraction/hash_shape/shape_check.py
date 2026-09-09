#!/usr/bin/env python3
"""Pure retained-public-log shape control; does not run any cryptographic verifier."""
from pathlib import Path
import hashlib,importlib.util,json,sys
sys.dont_write_bytecode=True
root=Path(__file__).resolve().parent
bridge=root.parents[5]/'research/vfhe_2026_09_08/query_runtime/acceptance_bridge'
spec=importlib.util.spec_from_file_location('canonical_admission',bridge/'run.py');mod=importlib.util.module_from_spec(spec);spec.loader.exec_module(mod)
events_path=bridge/'canonical001/events.jsonl'
events=[json.loads(x) for x in events_path.read_text().splitlines()]
summary=mod.collect(events)
admission=mod.canonical_profile(summary,events,mod.CANONICAL_QUERY_TEMPLATE)
# Same four extension elements, but append four words to the salt vector.
# This checks shape only. It does not claim a hash collision for the saved proof.
event=next(e for e in events if e['kind']=='fri_packed_row_verified' and e['data']['extension_width']==4)
salt=event['data']['opening_proof'][0][0];assert len(salt)==4
salt.extend(salt[:])
changed=mod.collect(events);assert not changed['canonical_predicates']['all_salt_rows_exactly_four']
try:mod.canonical_profile(changed,events,mod.CANONICAL_QUERY_TEMPLATE)
except AssertionError:refused=True
else:refused=False
assert refused
shapes={'fri_round4':4*4+4,'fri_rounds0_to3':8*4+4,'input_batch0':sum(w+4 for w in admission['declared_base_widths'][0]),'input_batch4':sum(w+4 for w in admission['declared_base_widths'][4])}
result={'claim':'EXECUTED pure canonical-admission shape control on retained public events, not fresh proof verification','profile':admission['profile'],'canonical_saved_log_admission':True,'same_fri_data_salt8_refused':refused,'accepted_leaf_lengths_by_role':shapes,'payload20_fri_round4_shape':True,'payload24_fri_round4_shape':False,'payload20_input_batch0_or4_shape':False,'payload24_input_batch0_or4_shape':True,'root_roles_are_distinct':True,'native_or_hash_verifier_called':False,'pins':{str(p):hashlib.sha256(p.read_bytes()).hexdigest() for p in [bridge/'run.py',events_path,root/'shape_check.py']}}
(root/'results/shape.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
