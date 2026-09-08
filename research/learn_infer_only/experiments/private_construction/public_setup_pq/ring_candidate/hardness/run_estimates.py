#!/usr/bin/env python3
"""Exactly 24 declared parameter-estimator entries; no crypto/lattice attack."""
from hashlib import sha256
from pathlib import Path
import json
import os
import signal
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[3] / 'he_closure_costs/estimator/runtime/pinned-estimator'
os.environ['DOT_SAGE'] = str(HERE / 'runtime/sage_cache')
os.environ['MPLCONFIGDIR'] = str(HERE / 'runtime/mpl')
os.environ['XDG_CACHE_HOME'] = str(HERE / 'runtime/xdg')
sys.dont_write_bytecode = True


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


grid = json.loads((HERE / 'GRID.json').read_text())
pin = json.loads(Path(grid['source_manifest_path']).read_text())
assert digest(Path(grid['source_manifest_path'])) == grid['source_manifest_sha256']
for item in pin['source_files']:
    assert digest(Path(item['path'])) == item['sha256'], item['path']
assert len(grid['points']) == 2 and grid['proposed_calls']['count'] == 24
assert not (HERE / 'estimates.jsonl').exists(), 'Retain outputs; do not silently rerun'
sys.path.insert(0, str(SOURCE))
from sage.all import QQ, ZZ, log, oo
from sage.version import version as sage_version
from estimator import LWE, ND
from estimator.reduction import ADPS16, MATZOV

MODELS = {
    'MATZOV_classical': lambda: MATZOV(nn='list_decoding-classical'),
    'ADPS16_classical': lambda: ADPS16(mode='classical'),
    'ADPS16_quantum_core_svp': lambda: ADPS16(mode='quantum'),
    'MATZOV_quantum_depth_width': lambda: MATZOV(nn='list_decoding-dw'),
}
assert list(MODELS) == grid['proposed_calls']['models']
assert sage_version == '10.8'


def expired(*args):
    raise TimeoutError('45-second estimator calculation limit')


def cost_values(cost):
    fields = {str(k): str(v) for k, v in cost.items() if k != 'problem'}
    logs = {}
    for key in ['rop', 'red', 'mem', 'm', 'N', 'guess']:
        if key in cost:
            value = cost[key]
            try:
                logs[key] = float(log(value, 2)) if value > 0 and value != oo else str(value)
            except Exception:
                logs[key] = None
    return fields, logs


signal.signal(signal.SIGALRM, expired)
manifest = {
    'scope': 'Generic heuristic parameter estimates for an explicitly structured ring instance; no cryptographic or lattice attack execution',
    'estimator_archive_commit': grid['estimator_archive_commit'],
    'sage_version': sage_version, 'python': sys.version, 'source_path': str(SOURCE),
    'source_files': pin['source_files'], 'invocation': sys.argv,
    'predeclared_grid_sha256': digest(HERE / 'GRID.json'),
    'predeclared_mapping_sha256': digest(HERE / 'MODEL_AND_GRID.md'),
    'driver_sha256': digest(Path(__file__)), 'per_entry_seconds_limit': 45,
    'paths': grid['proposed_calls']['paths'], 'models': list(MODELS),
    'planned_entries': 24, 'primal_shape_model': 'gsa',
    'normalization': 'All entries explicitly receive normalized input; raw and normalized counts retained',
}
(HERE / 'estimates.manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
attempts = entries = 0
with (HERE / 'estimates.jsonl').open('x') as out:
    for point in grid['points']:
        n, w, q = point['N'], point['w_ring_samples'], ZZ(point['q'])
        xe = ND.DiscreteGaussianAlpha(QQ(1024) / q, q)
        raw = LWE.Parameters(n=n, q=q, Xs=ND.UniformMod(q), Xe=xe, m=w*n)
        normalized = raw.normalize()
        for model_label, model_factory in MODELS.items():
            for path in grid['proposed_calls']['paths']:
                attempts += 1
                row = {
                    'attempt': attempts, 'point': point['label'], 'N_secret': n,
                    'ring_samples_raw': w, 'ring_samples_normalized': w-1,
                    'q_exact': str(q), 'error_width_exact': '1024',
                    'error_stddev_estimator': str(xe.stddev),
                    'scalar_proxy_raw_n': raw.n, 'scalar_proxy_raw_m': raw.m,
                    'scalar_proxy_normalized_n': normalized.n,
                    'scalar_proxy_normalized_m': normalized.m,
                    'raw_repr': repr(raw), 'normalized_repr': repr(normalized),
                    'path': path, 'model': model_label, 'estimator_entered': False,
                }
                started = time.monotonic()
                print('START', attempts, point['label'], model_label, path, flush=True)
                signal.alarm(45)
                try:
                    assert normalized.n == n and normalized.m == (w-1)*n
                    assert type(normalized.Xs).__name__ == type(normalized.Xe).__name__ == 'DiscreteGaussian'
                    assert normalized.Xs.mean == normalized.Xe.mean == 0
                    assert normalized.Xs.stddev == normalized.Xe.stddev == xe.stddev
                    assert len(normalized.Xs) == n and len(normalized.Xe) == (w-1)*n
                    model = model_factory()
                    row['estimator_entered'] = True
                    entries += 1
                    if path == 'dual':
                        cost = LWE.dual(normalized, red_cost_model=model)
                    elif path == 'usvp':
                        cost = LWE.primal_usvp(normalized, red_cost_model=model, red_shape_model='gsa')
                    elif path == 'bdd':
                        cost = LWE.primal_bdd(normalized, red_cost_model=model, red_shape_model='gsa')
                    else:
                        raise ValueError(path)
                    row['fields'], row['log2_fields'] = cost_values(cost)
                    row['status'] = 'EXECUTED'
                except Exception as error:
                    row['status'] = 'TIMEOUT' if isinstance(error, TimeoutError) else 'ERROR'
                    row['exception'] = repr(error)
                    row['traceback'] = traceback.format_exc()
                finally:
                    signal.alarm(0)
                row['seconds_estimator_not_attack'] = time.monotonic() - started
                out.write(json.dumps(row) + '\n')
                out.flush()
                print('RESULT', attempts, row['status'], row.get('log2_fields'),
                      row.get('fields', {}).get('beta'), flush=True)

assert attempts == 24
for item in pin['source_files']:
    assert digest(Path(item['path'])) == item['sha256'], item['path']
manifest.update({'attempts_completed': attempts, 'estimator_entries': entries,
                 'all_27_source_hashes_unchanged_after': True,
                 'output_sha256': digest(HERE / 'estimates.jsonl')})
(HERE / 'estimates.manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
print('FINISHED', attempts, entries, flush=True)
