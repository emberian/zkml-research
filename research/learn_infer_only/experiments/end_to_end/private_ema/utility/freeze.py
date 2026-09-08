"""Freeze algorithm, evaluation programs and existing inputs without scoring."""
import datetime
import sys
from common import ROOT, PRIOR, load, save, sha

assert not (ROOT / 'freeze.json').exists(), 'Never overwrite a freeze'
assert not (ROOT / 'results.json').exists()
paths = set()
inventories = {}
for directory in [PRIOR, PRIOR / 'materialized']:
    manifest = directory / 'manifest.json'
    inventory = load(manifest)
    paths.add(manifest)
    for name, row in inventory['files'].items():
        p = directory / name
        assert sha(p) == row['sha256'], str(p)
        paths.add(p)
    inventories[str(manifest)] = len(inventory['files'])
for name in ['CONTRACT.md', 'common.py', 'freeze.py', 'evaluate.py', 'audit.py', 'launch.py']:
    paths.add(ROOT / name)
for name in ['CONTRACT.md', 'REPORT.md', 'costs.csv', 'src/lib.rs', 'src/bin/host.rs']:
    paths.add(ROOT.parent / name)
save(ROOT / 'freeze.json', {
    'created_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
    'scope': 'Fixed selected-bin EMA, reused-data exploratory, no new heldout estimate',
    'algorithm': {'routes': 2, 'bins_per_route': 4, 'numerator_state': 7,
                  'denominator': 8, 'label_scale': 120, 'floor': True,
                  'zero_prediction': 1, 'unselected_state_unchanged': True},
    'history_seeds': list(range(67000, 67064)),
    'all_query_ids': list(range(256, 384)),
    'materialized_history_seeds': [67000, 67001],
    'materialized_query_ids': [256,257,272,273,288,289,304,305,320,321,336,337,352,353,368,369],
    'prior_inventories_verified': inventories,
    'files': {str(p): {'sha256': sha(p), 'bytes': p.stat().st_size} for p in sorted(paths)},
    'python': sys.version,
    'new_model_calls': 0, 'web_searches': 0, 'scry_sql': 0, 'scry_schema': 0,
})
print({'freeze_sha256': sha(ROOT / 'freeze.json'), 'pinned_files': len(paths)})
