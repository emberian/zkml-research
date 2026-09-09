import importlib.util, json, tempfile
from pathlib import Path
path = Path('research/vfhe_2026_09_08/matched_field/caller.py').resolve()
spec = importlib.util.spec_from_file_location('matched_field_caller', path)
m = importlib.util.module_from_spec(spec); spec.loader.exec_module(m)
passed = []
def reject(name, operation):
    try: operation()
    except (ValueError, OSError, KeyError, TypeError): passed.append(name)
    else: raise RuntimeError('unexpected acceptance: ' + name)
for kind, inputs, output in [('linear', m.INPUTS, 'dot_ciphertext_sha256'), ('update', m.UPDATE_INPUTS, 'out_sha256')]:
    good = {field: 'a' * 64 for field in inputs}
    if m.expected_values(good, kind) != good: raise RuntimeError('valid expectation rejected')
    if m.expected_values({**good, output: 'b' * 64}, kind)[output] != 'b' * 64: raise RuntimeError('valid output pin rejected')
    reject(kind + '-missing-input', lambda: m.expected_values({}, kind))
    reject(kind + '-extra-field', lambda: m.expected_values({**good, 'unexpected': 'b' * 64}, kind))
    reject(kind + '-uppercase-digest', lambda: m.expected_values({**good, output: 'B' * 64}, kind))
reject('private-path', lambda: m.public_path('/tmp/.private/reader.key'))
with tempfile.TemporaryDirectory(prefix='matched-public-caller-check-') as td:
    root = Path(td)
    plan = root / 'plan.json'; plan.write_text('{}\n')
    duplicate = root / 'duplicate.json'; duplicate.write_text('{"x": 1, "x": 2}')
    reject('duplicate-json-field', lambda: m.read(duplicate))
    nonfinite = root / 'nonfinite.json'; nonfinite.write_text('{"x": NaN}')
    reject('nonfinite-json-field', lambda: m.read(nonfinite))
    profile = root / 'PIPELINE.json'
    cfg = m.pin_config(plan, Path('/usr/bin/true'), profile)
    if m.config(profile) != cfg: raise RuntimeError('valid profile rejected')
    reject('existing-output-profile', lambda: m.pin_config(plan, Path('/usr/bin/true'), profile))
    plan.write_text('{"mutated": true}\n')
    reject('plan-byte-pin', lambda: m.config(profile))
print(json.dumps({'python_optimized_mode': not __debug__, 'linear_and_update_valid_expectations_accepted': True, 'valid_profile_accepted': True, 'rejections': passed, 'proofs_generated': 0, 'fhe_evaluations': 0, 'private_files_read': 0}))
