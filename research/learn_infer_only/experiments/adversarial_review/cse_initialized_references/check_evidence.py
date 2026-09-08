"""Independent source/pin/patch audit. Uses saved Lean evidence; never invokes Lean."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
RESIDENT = HERE.parents[2]
REPO = RESIDENT.parents[1]
PACKAGE = RESIDENT / 'formal/cse_initialized_references'
COMPANION = Path('/Users/ember/dev/minidregg')
SOURCE = PACKAGE / 'Compiler/CseInitializedReferences.lean'
PATCH = PACKAGE / 'minidregg-cse-initialized-references.patch'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
parser = argparse.ArgumentParser()
parser.add_argument('--manifest-sha256', required=True)
args = parser.parse_args()
assert sha(PACKAGE / 'manifest.json') == args.manifest_sha256
manifest = json.loads((PACKAGE / 'manifest.json').read_text())
for name, digest in manifest['files'].items():
    assert sha(PACKAGE / name) == digest, name
assert sha(SOURCE) == '1e8037c2c4ce35727a804912560b13a89a673682a8ca7405f2d1d4504d884386'
assert sha(PATCH) == '39afffcab611adc4a3a292bd3935ea551ae5f22e264660c9d2c0523256c74c6c'
verification = json.loads((PACKAGE / 'results/verification.json').read_text())
assert verification['all_package_checks_passed'] and verification['source_sha256'] == sha(SOURCE)
assert verification['patch_sha256'] == sha(PATCH)
assert all(item['exit_code'] == 0 for item in verification['checks'])
saved = json.loads((PACKAGE / 'results/lean_006.json').read_text())
assert saved['exit_code'] == 0 and saved['source_unchanged']
assert saved['source_sha256'] == saved['source_sha256_after'] == sha(SOURCE)
assert saved['stdout'] == saved['stderr'] == ''
assert Path(saved['command'][-1]) == SOURCE
environment = json.loads((PACKAGE / 'results/environment.json').read_text())
assert len(environment['dependencies']) == 4
for record in environment['dependencies']:
    assert record['exit_code'] == 0 and record['stdout'] == record['stderr'] == ''
    assert sha(Path(record['command'][-1])) == record['sha256']
for kind in ['dependency_source_sha256', 'reused_source_sha256']:
    for path, digest in verification[kind].items():
        assert sha(Path(path)) == digest, path
baseline = json.loads((PACKAGE / 'results/baseline.json').read_text())
for path, digest in baseline['frozen_files'].items():
    assert sha(REPO / path) == digest, path

raw = SOURCE.read_text()
def mask(text):
    """Mask nested Lean comments and strings, preserving line numbers."""
    result, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth = 1; result.extend('  '); i += 2
            while depth:
                assert i < len(text)
                if text.startswith('/-', i): depth += 1; result.extend('  '); i += 2
                elif text.startswith('-/', i): depth -= 1; result.extend('  '); i += 2
                else: result.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('--', i):
            while i < len(text) and text[i] != '\n': result.append(' '); i += 1
        elif text[i] == '"':
            result.append(' '); i += 1
            while i < len(text):
                if text[i] == '\\': result.extend('  '); i += 2
                elif text[i] == '"': result.append(' '); i += 1; break
                else: result.append('\n' if text[i] == '\n' else ' '); i += 1
        else: result.append(text[i]); i += 1
    return ''.join(result)
code = mask(raw)
assert re.findall(r'^import (\S+)', code, re.M) == ['Compiler.CseStructure']
assert re.findall(r'^namespace (\S+)', code, re.M) == ['Minidregg.Compiler.CseInitializedReferences']
forbidden = re.findall(r'\b(?:sorry|admit|axiom|unsafe|native_decide|implemented_by)\b', code)
assert not forbidden, forbidden
declarations = re.findall(r'^(?:theorem|lemma) (\w+)', code, re.M)
assert len(declarations) == len(set(declarations)) == 29
pin_pattern = r"/-- info: '([^']+)' (.*?) -/\s*#guard_msgs \(whitespace := lax\) in #print axioms (\w+)"
pins = []
for qualified, message, name in re.findall(pin_pattern, raw, re.S):
    assert qualified == 'Minidregg.Compiler.CseInitializedReferences.' + name
    if message == 'does not depend on any axioms': axioms = []
    else:
        match = re.fullmatch(r'depends on axioms: \[(.*?)\]', message)
        assert match
        axioms = [item.strip() for item in match.group(1).split(',')]
    assert set(axioms) <= {'propext', 'Quot.sound', 'Classical.choice'}
    pins.append({'theorem': name, 'qualified_name': qualified, 'axioms': axioms})
assert [p['theorem'] for p in pins] == declarations
assert len(re.findall(r'#print axioms', code)) == len(pins)
assert verification['census']['theorems'] == declarations
assert verification['census']['theorem_count'] == verification['census']['pin_count'] == len(pins)
for pin, author_pin in zip(pins, verification['census']['pins'], strict=True):
    assert pin['qualified_name'] == author_pin['theorem'] and pin['axioms'] == author_pin['axioms']
# Presence model inspects only addresses and stores externally supplied values.
storage = code[code.index('def inputStore'):code.index('theorem input_store_available')]
assert 'payload : DGate F2 → α' in storage and 'some (payload g)' in storage
assert 'Function.update store g.out' in storage and '∀ (α : Type)' in storage
assert not re.search(r'\b(?:eval|fillAux|cseGo|xor|and|GateOp)\b|\.op\b', storage)
assert 'def cseGo' not in code and 'def execute' not in code

checks = []
def run(command, cwd):
    outcome = subprocess.run(command, cwd=cwd, capture_output=True, text=True)
    row = {'command': command, 'cwd': str(cwd), 'exit_code': outcome.returncode,
           'stdout': outcome.stdout, 'stderr': outcome.stderr}
    checks.append(row)
    assert outcome.returncode == 0, row
    return outcome.stdout
assert run(['git', 'rev-parse', 'HEAD'], COMPANION) == baseline['companion_head']
assert run(['git', 'status', '--porcelain'], COMPANION) == baseline['companion_status']
umbrella = (COMPANION / 'Compiler.lean').read_bytes()
with tempfile.TemporaryDirectory(prefix='patch_check_', dir=HERE) as directory:
    scratch = Path(directory)
    (scratch / 'Compiler').mkdir()
    (scratch / 'Compiler.lean').write_bytes(umbrella)
    run(['git', 'init', '-q'], scratch)
    run(['git', 'apply', '--check', str(PATCH)], scratch)
    run(['git', 'apply', str(PATCH)], scratch)
    assert (scratch / 'Compiler/CseInitializedReferences.lean').read_bytes() == SOURCE.read_bytes()
    assert (scratch / 'Compiler.lean').read_text() == umbrella.decode().rstrip('\n') + '\n\nimport Compiler.CseInitializedReferences\n'
    assert sorted(str(p.relative_to(scratch)) for p in scratch.rglob('*.lean')) == ['Compiler.lean', 'Compiler/CseInitializedReferences.lean']
assert (COMPANION / 'Compiler.lean').read_bytes() == umbrella
assert sha(PACKAGE / 'manifest.json') == args.manifest_sha256
report = {'ok': True, 'author_manifest_sha256': args.manifest_sha256, 'author_manifest_files': len(manifest['files']),
          'source_sha256': sha(SOURCE), 'patch_sha256': sha(PATCH), 'saved_final_Lean_result_sha256': sha(PACKAGE / 'results/lean_006.json'),
          'theorem_count': len(declarations), 'axiom_pins': pins, 'forbidden_identifiers': forbidden,
          'four_saved_fresh_proposal_dependency_checks_agree': True,
          'reused_companion_source_hashes': verification['reused_source_sha256'],
          'frozen_predecessor_files_rehashed': len(baseline['frozen_files']),
          'storage_model_has_no_gate_evaluator': True, 'patch_exactly_source_and_umbrella_import': True,
          'companion_HEAD_status_and_umbrella_preserved': True, 'independent_commands': checks,
          'Lean_builds_by_reviewer': 0, 'crypto_execution': 0,
          'scope': 'Independent source/census/hash and isolated patch application. Lean success and axiom guard evaluation are attributed to saved exact author output, with cached companion/external dependencies; no whole-tree rebuild.'}
(HERE / 'evidence_results.json').write_text(json.dumps(report, indent=2, sort_keys=True) + '\n')
print(json.dumps({key: value for key, value in report.items() if key not in ['axiom_pins', 'independent_commands']}, indent=2, sort_keys=True))
