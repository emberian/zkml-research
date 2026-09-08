"""Only file/provenance helpers; no model imports or evaluation at import."""
import hashlib
import json
import math
import statistics
from pathlib import Path

ROOT = Path(__file__).resolve().parent
E2E = ROOT.parents[1]
PRIOR = E2E / 'utility/semantic_axis_successor'
load = lambda p: json.loads(Path(p).read_text())

def save(p, value):
    Path(p).write_text(json.dumps(value, sort_keys=True, indent=2) + '\n')

def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()

def verify_freeze():
    frozen = load(ROOT / 'freeze.json')
    for path, row in frozen['files'].items():
        assert sha(path) == row['sha256'], path
    return len(frozen['files'])

def stats(values):
    sd = statistics.stdev(values) if len(values) > 1 else 0
    return {'n_histories': len(values), 'mean': statistics.mean(values), 'sd': sd,
            'normal95_half_width': 1.96 * sd / math.sqrt(len(values)),
            'min': min(values), 'max': max(values)}

def cell(rows, key='ema_prediction'):
    correct = sum(r[key] == r['target'] for r in rows)
    return {'correct': correct, 'queries': len(rows), 'accuracy': correct / len(rows)}
