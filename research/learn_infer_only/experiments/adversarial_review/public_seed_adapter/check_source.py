"""Read-only frozen-source/AST/public-constant audit; no adapter import or crypto."""
import ast
import hashlib
import json
from pathlib import Path
import sys

HERE = Path(__file__).resolve().parent
ADAPTER = HERE.parents[1] / 'private_construction/designated_span/public_coin_setup/public_seed/adapter'
EXPECTED = 'be861661892f52e52068d88361fc1519989ae6103a4945a3c6c7e41a8ffc5fac'
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
assert sys.flags.optimize == 0
assert sha(ADAPTER / 'SOURCE_PINS.json') == EXPECTED
pins = json.loads((ADAPTER / 'SOURCE_PINS.json').read_text())
checked = {}
for name, digest in pins['source_sha256'].items():
    assert sha(ADAPTER / name) == digest, name
    checked[name] = digest
for name, item in pins['copied_predecessors'].items():
    assert sha(Path(item['original'])) == item['sha256'] == checked[name]
    assert Path(item['original']).read_bytes() == (ADAPTER / name).read_bytes()
for name, digest in pins['frozen_crypto'].items():
    assert checked['source/public_setup/source/crypto/' + name] == digest
for name, digest in pins['reviewed_mathematics'].items():
    assert sha(Path(name)) == digest
native = pins['native_dependency']
assert sha(Path(native['path'])) == native['sha256']
environment = json.loads((ADAPTER / 'ENVIRONMENT.json').read_text())
for item in environment['binaries']:
    assert sha(Path(item['path'])) == item['sha256']

trees = {name: ast.parse((ADAPTER / name).read_text(), filename=name)
         for name in checked if name.endswith('.py')}
assert len(trees) == 9
function = lambda tree, name: next(n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef) and n.name == name)
calls = lambda tree: [n for n in ast.walk(tree) if isinstance(n, ast.Call)]
called = lambda node: ast.unparse(node.func)
driver = trees['driver.py']
main = function(driver, 'main')
run_mkdir = next(n for n in calls(main) if called(n) == 'run.mkdir')
gate_checks = [n for n in calls(main) if called(n) == 'c.require' and any(
    isinstance(x, ast.Constant) and isinstance(x.value, str) and x.value.startswith(('prelaunch review', 'pinned independent source', 'root notified'))
    for x in n.args)]
assert len(gate_checks) == 3 and all(n.lineno < run_mkdir.lineno for n in gate_checks)
allowset = next(n for n in ast.walk(function(driver, 'call')) if isinstance(n, ast.Set))
allowed = ast.literal_eval(allowset)
assert allowed == {'validate-context', 'recipient-finalize', 'issuer-encrypt', 'host-learn', 'encode-query', 'host-infer', 'reader-decrypt'}
backend_calls = [n for n in calls(main) if called(n) == 'call' and len(n.args) > 1 and isinstance(n.args[1], ast.Constant)]
normal_commands = [n.args[1].value for n in sorted(backend_calls, key=lambda n: n.lineno)]
assert set(normal_commands) <= allowed | {'auth-init', 'recipient-init', 'public-build', 'verify-public'}
assert not set(normal_commands) & {'initializer', 'keygen', 'recipient-register'}
close = next(n for n in ast.walk(main) if isinstance(n, ast.Assign) and any(
    isinstance(t, ast.Name) and t.id == 'public_closed' for t in n.targets) and isinstance(n.value, ast.Constant) and n.value.value is True)
decrypts = [n for n in backend_calls if n.args[1].value == 'reader-decrypt']
assert len(decrypts) == 1 and decrypts[0].lineno > close.lineno
assert any(k.arg == 'is_private' and isinstance(k.value, ast.Constant) and k.value.value is True for k in decrypts[0].keywords)
assert all(n.lineno < close.lineno for n in backend_calls if n not in decrypts)
public_saves = [n for n in calls(main) if called(n) == 'save' and n.args and ast.unparse(n.args[0]).startswith('public /')]
assert public_saves and max(n.lineno for n in public_saves) < close.lineno
closure_save = next(n for n in public_saves if 'PUBLIC_COMPLETE.json' in ast.unparse(n.args[0]))
assert closure_save.lineno == max(n.lineno for n in public_saves)
subprocess_calls = [n for n in calls(driver) if called(n).startswith('subprocess.')]
assert len(subprocess_calls) == 1 and called(subprocess_calls[0]) == 'subprocess.run'
assert any(k.arg == 'timeout' for k in subprocess_calls[0].keywords)

setup = trees['seed_setup.py']
execute = function(setup, 'execute')
delegates = [n for n in calls(execute) if called(n) == 'original.execute']
assert len(delegates) == 1
first = execute.body[0]
assert isinstance(first, ast.If) and ast.literal_eval(first.test.comparators[0]) == ('auth-init', 'recipient-init')
assert delegates[0] in calls(first)
transcript = function(setup, 'make_transcript')
derive_call = next(n for n in calls(transcript) if called(n) == 'derive.derive')
complete_call = next(n for n in calls(transcript) if called(n) == 'original.complete')
handler = next(n for n in ast.walk(transcript) if isinstance(n, ast.ExceptHandler))
assert ast.unparse(handler.type) == 'derive.SeedRejected'
assert isinstance(handler.body[-1], ast.Raise) and complete_call.lineno > handler.end_lineno > derive_call.lineno
rejected = next(n for n in ast.walk(handler) if isinstance(n, ast.Dict))
rejected_keys = {k.value for k in rejected.keys if isinstance(k, ast.Constant)}
assert {'registry_sha256', 'announcements', 'complete_domain', 'source_identity', 'derivation', 'context_created', 'retry_permitted'} <= rejected_keys
derive_tree = trees['derive.py']
assert [ast.unparse(n) for n in derive_tree.body if isinstance(n, (ast.Import, ast.ImportFrom))] == ['import hashlib', 'import json']
reference = trees['public_reference.py']
assert not any('reader-decrypt' in ast.unparse(n) or '.private' in ast.unparse(n) for n in calls(reference))
assert not any(called(n) in ('c.NativePow', 'c.exp', 'c.decode') for n in calls(reference))

rows = json.loads((ADAPTER / 'source/public_setup/source/crypto/rows.json').read_text())
assert len(rows) == 16 and all(len(row) == 577 for row in rows)
# Independent exact rational elimination of the small PUBLIC integer pivot matrix.
from fractions import Fraction
matrix = [[Fraction(x) for x in row[:16]] for row in rows]
det = Fraction(1)
for column in range(16):
    pivot = next(i for i in range(column, 16) if matrix[i][column])
    if pivot != column:
        matrix[pivot], matrix[column] = matrix[column], matrix[pivot]
        det *= -1
    value = matrix[column][column]
    det *= value
    for i in range(column + 1, 16):
        scale = matrix[i][column] / value
        for j in range(column, 16):
            matrix[i][j] -= scale * matrix[column][j]
assert det == -812032080
selected = {1: 0, 16: 1, 32: 2, 33: 3}
for tree in (driver, reference):
    selection = next(n.value for n in ast.walk(tree) if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'selected' for t in n.targets))
    assert ast.literal_eval(selection) == selected
queue, expiries = [], []
for t in range(1, 34):
    if len(queue) == 32:
        expiries.append((t, queue.pop(0)))
    queue.append(t)
assert expiries == [(33, 1)] and queue == list(range(2, 34))
assert not (ADAPTER / 'reports/normal_001').exists(), 'review is prelaunch only'
assert not (ADAPTER / 'PRELAUNCH_REVIEW.json').exists(), 'gate must remain absent until review disposition'
result = {
    'ok': True, 'source_pins_sha256': EXPECTED, 'source_contract_helper_pins': len(checked),
    'byte_identical_predecessors': len(pins['copied_predecessors']), 'reviewed_mathematics_pins': len(pins['reviewed_mathematics']),
    'native_dependency_bytes_checked_without_loading': 1, 'environment_binary_bytes_checked_without_loading': len(environment['binaries']),
    'environment_inventory_sha256': sha(ADAPTER / 'ENVIRONMENT.json'), 'python_ASTs_parsed': len(trees),
    'gate_precedes_run_directory': True, 'normal_backend_allowlist': sorted(allowed),
    'source_public_closure_line': close.lineno, 'source_first_private_decode_line': decrypts[0].lineno,
    'no_later_public_call_or_public_save_in_frozen_driver_AST': True,
    'rejection_record_before_completion_and_context': True, 'independent_public_integer_pivot_determinant': int(det),
    'public_schedule': {'learns': 33, 'infer_steps_and_rows': selected, 'expiry_step_and_original': expiries},
    'runtime_and_gate_absent_at_review': True, 'crypto_or_private_execution': 0,
    'scope': 'Source/AST and pure public integer checks, not a runtime trace, whole-program proof, concrete-hash proof or full transitive binary attestation.'
}
(HERE / 'source_results.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
print(json.dumps(result, indent=2, sort_keys=True))
