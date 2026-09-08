#!/usr/bin/env python3
"""Cost/source hashes and saved-output equivalence; no cryptographic operations."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parents[3]
PRIVATE = HERE.parent.parent
REVIEW = RESEARCH / 'experiments/adversarial_review/public_setup_pq'
MIRROR = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

results = json.loads((HERE/'results.json').read_text())
assert (HERE/'results.json').read_bytes() == (HERE/'derive_costs.stdout.json').read_bytes()
for path, expected in results['read_source_sha256'].items():
    assert sha(Path(path)) == expected, path
assert sha(HERE.parent/'notes/AUDIT.md') == '2c6f649fa0891be05dd1f3a1f89c935692091195e71f0b1959d78b5ef9061007'
sources = [
    PRIVATE/'designated_span/CONTRACT.md',
    RESEARCH/'experiments/he_closure_costs/estimator/AUDIT.md',
    RESEARCH/'experiments/he_closure_costs/estimator/run_estimates.py',
    RESEARCH/'experiments/he_closure_costs/estimator/runtime/pinned-estimator/estimator/nd.py',
    REVIEW/'FIXED_COORDINATE_QPT.md',
    REVIEW/'quantitative_regularity/BOUND.md',
    REVIEW/'quantitative_regularity/RESULTS.json',
    MIRROR/'2011/501.pdf', MIRROR/'2007/432.pdf',
]
out = {
    'scope':'public arithmetic and provenance only; no cryptographic runtime or estimator',
    'accounting_command':'python3 research/learn_infer_only/experiments/private_construction/public_setup_pq/costs/derive_costs.py',
    'accounting_exit_code':0,
    'first_failed_attempt_preserved_in':'initial_failure.md',
    'saved_stdout_exactly_matches_results':True,
    'all_recorded_input_hashes_match':True,
    'frozen_audit_unchanged':True,
    'additional_sources_sha256':{str(p):sha(p) for p in sources},
    'artifact_sha256':{},
    'new_source_discovery_counts':{'web_search':0,'scry_SQL':0,'scry_schema':0,'Kagi':0,'PDF_downloads':0},
    'source_page_renders':'pdftoppm -f 18 -l 18 -singlefile -scale-to 1800 / 3200 -png [pinned 2015/608.pdf] [source-page18 / source-page18-hi]',
}
for p in sorted([*HERE.glob('*.md'),*HERE.glob('*.py'),HERE/'results.json',
                 HERE/'derive_costs.stdout.json',HERE/'.gitignore']):
    out['artifact_sha256'][p.name] = sha(p)
(HERE/'COST_MANIFEST.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
