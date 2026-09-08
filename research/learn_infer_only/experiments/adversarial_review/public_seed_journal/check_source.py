"""Snapshot and check preparation sources only. No backend imports or runtime."""
import ast
from hashlib import sha256
import json
from pathlib import Path
import stat

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
AUTHOR = ROOT / 'research/learn_infer_only/experiments/private_construction/designated_span/public_coin_setup/public_seed/journal'


def read(path):
    path = Path(path).resolve()
    assert path.is_relative_to(ROOT)
    assert not {'runtime', '.private', 'private', 'signer_route', 'verified_route'}.intersection(path.parts)
    return path.read_bytes()


def pin(path):
    path = Path(path).resolve()
    data = read(path)
    return {'path': str(path), 'bytes': len(data), 'sha256': sha256(data).hexdigest(),
            'mode': oct(stat.S_IMODE(path.stat().st_mode))}


snapshot = HERE / 'source_snapshot'
snapshot.mkdir(exist_ok=True)
names = ['setup_join.py', 'driver.py', 'private_oracle.py', 'CONTRACT.md',
         'SOURCE_PINS.json', 'WRAPPER_ORIGINS.json']
owned_source = []
for name in names:
    data = read(AUTHOR/name)
    (snapshot/name).write_bytes(data)
    original = pin(AUTHOR/name)
    assert original['sha256'] == sha256(data).hexdigest()
    owned_source.append(original)
inventory = json.loads(read(snapshot/'SOURCE_PINS.json'))
copies = []
parsed = []
for name, expected in inventory['files'].items():
    copied, original = pin(AUTHOR/name), pin(expected['origin'])
    assert copied['sha256'] == original['sha256'] == expected['sha256']
    assert copied['bytes'] == original['bytes'] == expected['bytes']
    assert copied['mode'] == original['mode'] == expected['mode']
    copies.extend([copied, original])
    if name.endswith('.py'):
        ast.parse(read(AUTHOR/name), filename=name)
        parsed.append(name)
nested = json.loads(read(AUTHOR/'source/seed_setup/SOURCE_PINS.json'))
for name, expected in nested['source_sha256'].items():
    assert pin(AUTHOR/'source/seed_setup'/name)['sha256'] == expected
assert len(nested['source_sha256']) == 12
origins = json.loads(read(snapshot/'WRAPPER_ORIGINS.json'))
for name, entry in origins.items():
    original = pin(entry['origin'])
    assert original['sha256'] == entry['original_sha256']
    copies.append(original)
trees = {}
for name in ['setup_join.py', 'driver.py', 'private_oracle.py']:
    trees[name] = ast.parse(read(snapshot/name), filename=name)
    parsed.append(name)
driver = trees['driver.py']
public = next(n for n in driver.body if isinstance(n, ast.FunctionDef) and n.name == 'public_run')
private = next(n for n in driver.body if isinstance(n, ast.FunctionDef) and n.name == 'private_run')
public_names = [n.func.id for n in ast.walk(public) if isinstance(n, ast.Call) and isinstance(n.func, ast.Name)]
assert 'private_call' not in public_names
private_calls = [n for n in ast.walk(private) if isinstance(n, ast.Call) and isinstance(n.func, ast.Name) and n.func.id == 'private_call']
assert len(private_calls) == 2  # One unchanged drain, then integer comparison.
constructor = next(n for n in ast.walk(driver) if isinstance(n, ast.ClassDef) and n.name == 'PublicRun')
init = next(n for n in constructor.body if isinstance(n, ast.FunctionDef) and n.name == '__init__')
assert not any(isinstance(n, ast.Attribute) and n.attr == '__init__' for n in ast.walk(init))
source = read(snapshot/'driver.py').decode()
for expected in ['range(1,34)', 'if n==16:', "fresh[1:]", "query_index=row", "'persistentHostCompletedExactly37'", "'historicalRetriesPreserveHeadAndSelection'", "'PUBLIC_GATE.json'", "'PUBLIC_SEAL.json'"]:
    assert expected in source
schedule = []
queue = []
expiries = []
checkpoints = []
for n in range(1,34):
    if len(queue) == 32:
        expiries.append(queue.pop(0))
    queue.append(n)
    schedule.append({'kind': 'Learn', 'n': n})
    if n in {1:0,16:1,32:2,33:3}:
        schedule.append({'kind': 'Infer', 'n': n, 'row': {1:0,16:1,32:2,33:3}[n]})
    if n == 16:
        checkpoints.append(len(schedule))
assert len(schedule) == 37 and checkpoints == [18] and expiries == [1]
assert queue == list(range(2,34))
assert schedule[1] == {'kind': 'Infer', 'n': 1, 'row': 0}
result = {'status': 'PASS_SOURCE_SNAPSHOT_ONLY', 'launch_authorized': False,
          'prelaunch_acceptance_issued': False, 'cryptography_executed': False,
          'scope': 'Current source snapshot, copied predecessor identity, AST and index schedule. Launcher/public closure/final preparation gate not accepted.',
          'author_source_snapshot': owned_source,
          'frozen_predecessor_records': copies,
          'copied_dependency_count': len(inventory['files']),
          'nested_seed_adapter_source_pins': 12, 'parsed_python_files': parsed,
          'workload': {'learns': 33, 'infers': 4, 'expiries': 1, 'finalized_events': 37,
                       'reopen_revision': 18, 'historical_retry_original_revision': 2,
                       'final_queue': queue},
          'public_function_calls_no_private_call': True,
          'private_function_has_one_drain_then_one_comparison': True,
          'new_crypto_calls': 0, 'new_private_reads': 0, 'new_web_queries': 0,
          'new_scry_queries': 0, 'new_PDF_downloads': 0}
text = json.dumps(result, indent=2)+'\n'
(HERE/'source_results.json').write_text(text)
print(text, end='')
