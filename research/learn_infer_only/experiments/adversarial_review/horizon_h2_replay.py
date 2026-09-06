#!/usr/bin/env python3
"""Read-only replay of owner functions, preserving JSON key normalization."""
import hashlib
import importlib.util
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
LANE = HERE.parent/'private_construction'
source = LANE/'finite_ladder.py'
record = LANE/'results/finite_ladder_results.json'
inputs = [Path(__file__).resolve(), source, record, LANE/'FINITE_LADDER.md']
hashes = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
spec = importlib.util.spec_from_file_location('finite_ladder_review', source)
owner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(owner)
witness, schedule = owner.finite_witness(), owner.proof_schedule()
saved = json.loads(record.read_text())
normalized_witness = json.loads(json.dumps(witness))
assert normalized_witness == saved['finite_witness']
assert json.loads(json.dumps(schedule)) == saved['proof_schedule']
out = {
    'label': 'EXECUTED owner pure-function replay; no cryptography',
    'command': [sys.executable, str(Path(__file__).resolve())], 'inputs': hashes,
    'inputs_unchanged': all(hashes[str(p)] == hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs),
    'initial_states': witness['initial_states_checked'],
    'complete_paths': witness['complete_two_command_paths_checked'],
    'behavioral_classes': witness['behavioral_classes'],
    'issued_keys_exposed': len(witness['schedule']['exposed_inventory']['all_function_keys']),
    'raw_masters': witness['schedule']['exposed_inventory']['raw_masters'],
    'saved_results_match_after_JSON_normalization': True,
    'initial_raw_Python_comparison_equal': witness == saved['finite_witness'],
    'reviewer_first_attempt_failure': 'Raw Python equality failed because public-key dictionary integer keys become strings in JSON; normalized replay matches exactly.',
}
assert out['inputs_unchanged']
(HERE/'horizon_h2_replay.json').write_text(json.dumps(out, indent=2)+'\n')
print(json.dumps(out, indent=2))
