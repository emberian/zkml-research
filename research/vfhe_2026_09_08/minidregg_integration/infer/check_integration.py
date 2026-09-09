#!/usr/bin/env python3
"""Check patch transport and new import glue, reusing all completed module artifacts."""
from pathlib import Path
import hashlib, json, os, subprocess, time

ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent
MAIN = Path('/Users/ember/dev/minidregg')
sha = lambda data: hashlib.sha256(data).hexdigest()
provenance = json.loads((ROOT / 'PROVENANCE.json').read_text())
assert provenance['state'] == 'assembled; integration checks pending'
base = provenance['base_commit']
patch = ROOT / 'minidregg-complete-infer.patch'
assert sha(patch.read_bytes()) == provenance['patch_sha256']
base_root = subprocess.check_output(['git', 'show', f'{base}:Compiler.lean'], cwd=MAIN)
dirty_root = (MAIN / 'Compiler.lean').read_bytes()
old_root = (PRIOR / 'proposal/Compiler.lean').read_bytes()
new_root = (ROOT / 'proposal/Compiler.lean').read_bytes()
anchor = next(line for line in base_root.decode().splitlines(keepends=True) if line.startswith('import Compiler.AirModularView '))
old_hook = next(line for line in old_root.decode().splitlines(keepends=True) if line.startswith('import Compiler.FheArithmetic '))
new_hook = next(line for line in new_root.decode().splitlines(keepends=True) if line.startswith('import Compiler.FheInfer '))
checks = []

def record(command, cwd, *, env=None, timeout=180, label):
    started = time.monotonic()
    try:
        result = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
        code, stdout, stderr = result.returncode, result.stdout, result.stderr
    except subprocess.TimeoutExpired as error:
        code, stdout, stderr = 124, error.stdout or '', error.stderr or ''
    if isinstance(stdout, bytes):
        stdout = stdout.decode()
    if isinstance(stderr, bytes):
        stderr = stderr.decode()
    item = {'label': label, 'argv': command, 'cwd': str(cwd), 'exit_code': code,
            'seconds': time.monotonic() - started, 'stdout': stdout, 'stderr': stderr}
    checks.append(item)
    provenance['integration_checks'] = checks
    (ROOT / 'PROVENANCE.json').write_text(json.dumps(provenance, indent=2) + '\n')
    print(json.dumps({'label': label, 'exit_code': code, 'seconds': item['seconds']}), flush=True)
    assert code == 0, item

for kind, original in [('base', base_root), ('dirty', dirty_root)]:
    target = ROOT / f'check_{kind}'
    target.mkdir(exist_ok=False)
    (target / 'Compiler.lean').write_bytes(original)
    record(['git', 'init', '--quiet'], target, label=f'{kind} scratch repository')
    record(['git', 'apply', '--check', str(patch)], target, label=f'{kind} applicability')
    record(['git', 'apply', str(patch)], target, label=f'{kind} isolated apply')
    expected = original.decode().replace(anchor, anchor + old_hook + new_hook).encode()
    assert (target / 'Compiler.lean').read_bytes() == expected, 'Root edits not preserved'
    for rel, info in provenance['files'].items():
        if rel != 'Compiler.lean':
            assert sha((target / rel).read_bytes()) == info['sha256'], rel
record(['git', 'apply', '--check', str(patch)], MAIN, label='actual companion read-only applicability')

build = ROOT / 'build'
(build / 'Compiler').mkdir(parents=True, exist_ok=True)
old_artifacts = json.loads((PRIOR / 'reused_oleans.json').read_text())['modules']
old_oleans = {item['module'].replace('.', '/') + '.lean': Path(item['retained_olean']) for item in old_artifacts}
old_oleans['Compiler/FheArithmetic.lean'] = PRIOR / 'build/Compiler/FheArithmetic.olean'
# The first Compiler directory is a complete namespace overlay. Reuse the old
# integration cache links; do not compile or recensus those dependency files.
for cached in (PRIOR / 'build/Compiler').rglob('*'):
    if cached.is_file():
        target = build / 'Compiler' / cached.relative_to(PRIOR / 'build/Compiler')
        target.parent.mkdir(parents=True, exist_ok=True)
        if not target.exists():
            target.symlink_to(cached.resolve())
reused = []
for rel, info in provenance['files'].items():
    if not rel.startswith('Compiler/') or info['group'] == 'integration':
        continue
    if rel in old_oleans:
        selected = old_oleans[rel]
    else:
        source = Path(info['source'])
        package = source.parent.parent
        choices = [package / 'build/Compiler' / (source.stem + '.olean'),
                   package / '.build/Compiler' / (source.stem + '.olean')]
        selected = next((candidate for candidate in choices if candidate.exists()), None)
        assert selected is not None, (rel, 'missing retained completed olean', list(map(str, choices)))
    for sibling in selected.parent.glob(selected.stem + '.*'):
        if sibling.is_file():
            target = build / 'Compiler' / sibling.name
            if target.is_symlink():
                target.unlink()
            assert not target.exists(), (str(target), 'unexpected regular artifact')
            target.symlink_to(sibling.resolve())
    reused.append({'module': rel[:-5].replace('/', '.'), 'source': info['source'],
                   'retained_olean': str(selected), 'resolved_olean': str(selected.resolve())})
provenance['retained_oleans'] = reused
provenance['retained_olean_scope'] = 'Reused existing completed-module artifacts and their author evidence; no theorem recompilation or new artifact audit.'
previous = json.loads((PRIOR / 'glue_checks.json').read_text())
lean_path = str(build) + ':' + ':'.join(previous['lean_path'].split(':')[1:])
lean = previous['checks'][0]['command'][0]
env = dict(os.environ, LEAN_PATH=lean_path)
provenance['glue_lean_path'] = lean_path
for label, cwd, source, output in [
    ('new FheInfer umbrella', ROOT / 'proposal', 'Compiler/FheInfer.lean', build / 'Compiler/FheInfer.olean'),
    ('base Compiler import glue', ROOT / 'proposal', 'Compiler.lean', build / 'Compiler.olean'),
    ('dirty Compiler import glue', ROOT / 'check_dirty', 'Compiler.lean', build / 'DirtyCompiler.olean')]:
    record([lean, '-o', str(output), source], cwd, env=env, label=label)

record(['bash', str(MAIN / 'scripts/check-import-boundary.sh')], MAIN, label='existing Theory/Selvage import boundary')
assert (MAIN / 'Compiler.lean').read_bytes() == dirty_root, 'Companion root changed during checks'
assert sha((PRIOR / 'minidregg-fhe-arithmetic.patch').read_bytes()) == provenance['predecessor_patch']['sha256']
provenance['state'] = 'complete; applicability and new import glue passed'
provenance['preservation'] = {'main_Compiler_unchanged': True, 'predecessor_patch_unchanged': True,
    'dirty_root_preserved_except_two_proposed_imports': True, 'all_applied_copied_sources_exact': True,
    'base_Compiler_sha256': sha(base_root), 'observed_dirty_Compiler_sha256': sha(dirty_root),
    'no_Theory_or_Selvage_target_changed': not any(path.startswith(('Theory/', 'Selvage/')) or path in ['Theory.lean', 'Selvage.lean'] for path in provenance['files'])}
(ROOT / 'PROVENANCE.json').write_text(json.dumps(provenance, indent=2) + '\n')
print(json.dumps({'status': 'PASS', 'checks': len(checks), 'compiled_glue_files': 3,
                  'completed_theorem_modules_recompiled': 0, 'files': len(provenance['files'])}), flush=True)
