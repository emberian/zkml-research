#!/usr/bin/env python3
"""Independent frozen-byte, source census and isolated patch review. No Lean/runtime run."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
PACKAGE = ROOT / 'research/learn_infer_only/formal/emitted_schedule_execution'
COMPANION = Path('/Users/ember/dev/minidregg')
SOURCE = PACKAGE / 'Compiler/EmittedScheduleExecution.lean'
PATCH = PACKAGE / 'minidregg-emitted-schedule-execution.patch'
EXPECTED_SOURCE = '37d9b62f5a0b0b3b80fa7b2de2f8322e71c92b4635710f64eb848f573bffb077'
EXPECTED_PATCH = '057672fd7654df79812d5071bd0c00497ef7c462b53c0314a62c97fcc219d72c'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def code_only(text):
    """Erase nested Lean comments and strings, preserving line numbers."""
    out = list(text)
    i = 0
    depth = 0
    string = False
    while i < len(text):
        if depth:
            if text[i:i+2] == '/-':
                depth += 1
                out[i:i+2] = '  '
                i += 2
            elif text[i:i+2] == '-/':
                depth -= 1
                out[i:i+2] = '  '
                i += 2
            else:
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif string:
            if text[i] == '\\':
                out[i:i+2] = '  '
                i += 2
            else:
                if text[i] == '"': string = False
                if text[i] != '\n': out[i] = ' '
                i += 1
        elif text[i:i+2] == '/-':
            depth = 1
            out[i:i+2] = '  '
            i += 2
        elif text[i:i+2] == '--':
            end = text.find('\n', i)
            if end < 0: end = len(text)
            out[i:end] = ' ' * (end-i)
            i = end
        elif text[i] == '"':
            string = True
            out[i] = ' '
            i += 1
        else:
            i += 1
    assert depth == 0 and not string
    return ''.join(out)

assert sha(SOURCE) == EXPECTED_SOURCE
assert sha(PATCH) == EXPECTED_PATCH
manifest = json.loads((PACKAGE / 'manifest.json').read_text())
manifest_matches = {p: sha(PACKAGE / p) == h for p, h in manifest['files'].items()}
assert all(manifest_matches.values())
baseline = json.loads((PACKAGE / 'results/baseline.json').read_text())
frozen_matches = {p: sha(ROOT / p) == h for p, h in baseline['frozen_files'].items()}
assert len(frozen_matches) == 41 and all(frozen_matches.values())
verification = json.loads((PACKAGE / 'results/verification.json').read_text())
dependency_matches = {p: sha(Path(p)) == h for key in ['dependency_source_sha256', 'reused_source_sha256']
                      for p, h in verification[key].items()}
assert all(dependency_matches.values())

text = SOURCE.read_text()
code = code_only(text)
declarations = [{'name': m.group(2), 'kind': m.group(1), 'line': code.count('\n', 0, m.start())+1}
                for m in re.finditer(r'(?m)^[ \t]*(?:private\s+|protected\s+)?(theorem|lemma)\s+(\w+)', code)]
pins = re.findall(r"/-- info: 'Minidregg\.Compiler\.EmittedScheduleExecution\.(\w+)' (depends on axioms: \[[^\]]*\]|does not depend on any axioms) -/\s*#guard_msgs \(whitespace := lax\) in #print axioms (\w+)", text)
assert len(declarations) == len(pins) == 19
assert [d['name'] for d in declarations] == [p[0] for p in pins] == [p[2] for p in pins]
allowed_axioms = {'propext', 'Classical.choice', 'Quot.sound'}
pin_census = []
for declaration, (name, message, target) in zip(declarations, pins):
    axioms = [] if message == 'does not depend on any axioms' else message.split('[')[1][:-1].split(', ')
    assert set(axioms) <= allowed_axioms
    pin_census.append(dict(declaration, exact_pin=True, axioms=axioms))
forbidden = re.findall(r'\b(?:sorry|sorryAx|axiom|admit|native_decide|unsafe)\b', code)
assert not forbidden
imports = re.findall(r'(?m)^import\s+(\S+)', code)
assert imports == ['Compiler.PrivateAddressEmaSchedule']
assert re.findall(r'^\+\+\+ b/(.*)$', PATCH.read_text(), re.M) == [
    'Compiler.lean', 'Compiler/EmittedScheduleExecution.lean']

commands = []
def run(argv, cwd):
    r = subprocess.run(argv, cwd=cwd, capture_output=True, text=True)
    commands.append(dict(command=argv, cwd=str(cwd), exit_code=r.returncode,
                         stdout=r.stdout, stderr=r.stderr))
    assert r.returncode == 0, commands[-1]
    return r.stdout

base = baseline['companion_head'].strip()
compiler_base = run(['git', 'show', f'{base}:Compiler.lean'], COMPANION)
compiler_base_sha = hashlib.sha256(compiler_base.encode()).hexdigest()
with tempfile.TemporaryDirectory(prefix='independent_emitted_execution_patch_') as tmp:
    tmp = Path(tmp)
    (tmp / 'Compiler').mkdir()
    (tmp / 'Compiler.lean').write_text(compiler_base)
    run(['git', 'init', '-q'], tmp)
    run(['git', 'apply', '--check', str(PATCH)], tmp)
    run(['git', 'apply', str(PATCH)], tmp)
    assert sha(tmp / 'Compiler/EmittedScheduleExecution.lean') == EXPECTED_SOURCE
    assert (tmp / 'Compiler.lean').read_text() == compiler_base.rstrip('\n') + '\n\nimport Compiler.EmittedScheduleExecution\n'
    patch_replay = dict(exact_module_bytes=True, only_umbrella_addition=True,
                        companion_base_commit=base, compiler_base_sha256=compiler_base_sha)
# Keep the git-show command and its digest, without copying the whole umbrella to the log.
commands[0]['stdout'] = f'[captured Compiler.lean; SHA-256 {compiler_base_sha}]'

lean_log = json.loads((PACKAGE / 'results/lean_006.json').read_text())
assert lean_log['exit_code'] == 0 and lean_log['stdout'] == lean_log['stderr'] == ''
assert lean_log['source_sha256'] == lean_log['source_sha256_after'] == EXPECTED_SOURCE
assert verification['actual_validity_kernel_proved'] is False
assert all(row['structurallyValid'] for row in verification['compiled_structural_checks'])
assert sha(SOURCE) == EXPECTED_SOURCE and sha(PATCH) == EXPECTED_PATCH

result = dict(all_checks_passed=True, source_sha256=sha(SOURCE), patch_sha256=sha(PATCH),
              author_manifest_sha256=sha(PACKAGE / 'manifest.json'),
              manifest_files_checked=len(manifest_matches), manifest_matches=manifest_matches,
              frozen_inputs_checked=len(frozen_matches), frozen_input_matches=frozen_matches,
              dependency_matches=dependency_matches, theorem_count=len(declarations),
              pin_census=pin_census, forbidden_tokens=forbidden, imports=imports,
              patch_replay=patch_replay, commands=commands,
              author_clean_lean_log_checked=True, lean_reexecuted=False, runtime_reexecuted=False,
              actual_validity_kernel_proved=False,
              author_compiled_structural_checks=verification['compiled_structural_checks'])
(HERE / 'RESULTS.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ['all_checks_passed', 'source_sha256', 'patch_sha256',
      'manifest_files_checked', 'frozen_inputs_checked', 'theorem_count', 'actual_validity_kernel_proved',
      'lean_reexecuted', 'runtime_reexecuted']}, indent=2))
