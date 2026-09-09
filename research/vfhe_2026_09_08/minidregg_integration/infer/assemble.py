#!/usr/bin/env python3
"""Consolidate only completed sources; no theorem build or exporter execution."""
from pathlib import Path
import difflib, hashlib, json, re, subprocess, sys

ROOT = Path(__file__).resolve().parent
PRIOR = ROOT.parent
LANES = PRIOR.parent
MAIN = Path('/Users/ember/dev/minidregg')
BASE = '6937394e1dc2c2aaff986c7d4b3a258aca5d16fd'
PREPARE = '--prepare' in sys.argv
sha = lambda data: hashlib.sha256(data).hexdigest()
read_json = lambda path: json.loads(path.read_text())
old = read_json(PRIOR / 'PROVENANCE.json')
old_patch = PRIOR / 'minidregg-fhe-arithmetic.patch'
assert sha(old_patch.read_bytes()) == '7e3e625deefe311d1f7d359ca6f3fc54fc727818bc138afaf955170cc42ed265'
assert old['base_commit'] == BASE
files, records, candidates, evidence, overlaps = {}, {}, {}, {}, []

def imports(data):
    return [module for line in re.findall(r'^import\s+([^\n]+)', data.decode(), re.M)
            for module in line.split('--', 1)[0].split()]

def include(path, target, expected, group, original=None):
    data = path.read_bytes()
    digest = sha(data)
    assert digest == expected, (str(path), 'source pin mismatch')
    if target in files:
        assert files[target] == data, (target, 'conflicting target requires explicit resolution')
        overlaps.append({'target': target, 'resolution': 'identical source reused once', 'source': str(path), 'sha256': digest})
        return
    files[target] = data
    records[target] = {'source': str(path.resolve()), 'sha256': digest, 'group': group, 'existing_pin_checked': True}
    if original is not None:
        records[target]['predecessor_provenance'] = original

for target, entry in old['files'].items():
    include(PRIOR / 'proposal' / target, target, entry['sha256'], 'frozen 51-file predecessor', entry)

def index_pins(value):
    if isinstance(value, dict):
        path, digest = value.get('path'), value.get('sha256')
        if isinstance(path, str) and isinstance(digest, str):
            p = Path(path)
            if p.suffix == '.lean' and p.parent.name == 'Compiler':
                target = 'Compiler/' + p.name
                candidates.setdefault(target, {})[(str(p), digest)] = {'source': p, 'sha256': digest}
        for child in value.values():
            index_pins(child)
    elif isinstance(value, list):
        for child in value:
            index_pins(child)

packages = ['rescale_compiler_successor', 'rescale_native_emitter', 'basis_extension_successor',
            'full_bfv_tensor_arithmetic', 'full_bfv_keyswitch_arithmetic']
if not PREPARE:
    packages.append('full_bfv_infer_composition')
for package in packages:
    folder = LANES / package
    pinfile = folder / 'source_pins.json'
    pins = read_json(pinfile)
    if package == 'full_bfv_infer_composition':
        assert sha(pinfile.read_bytes()) == '1c59ee77e6284ba46001fcbff896125e522bfaccd72f4838114fd34881798e7c'
    index_pins(pins)
    evidence[package] = {'source_pins': str(pinfile), 'source_pins_sha256': sha(pinfile.read_bytes())}
    for marker in ['proposal.patch', 'MANIFEST.sha256', 'MANIFEST.json', 'SOURCE_MANIFEST.json']:
        path = folder / marker
        if path.exists():
            evidence[package][marker] = {'path': str(path), 'sha256': sha(path.read_bytes())}
    entries = pins.get('owned_sources', pins.get('owned'))
    assert isinstance(entries, list), (package, 'unexpected source pin schema')
    for entry in entries:
        source_pin = entry.get('source', entry)
        path = Path(source_pin['path'])
        relative = str(path.relative_to(folder))
        if re.fullmatch(r'(Compiler/[^/]+|Emit[^/]+)\.lean', relative):
            include(path, relative, source_pin['sha256'], package)

tracked = set(subprocess.check_output(['git', 'ls-tree', '--name-only', '-r', BASE], cwd=MAIN, text=True).splitlines())
processed, base_dependencies = set(), dict(old['base_direct_dependencies'])
while pending := sorted(set(files) - processed):
    for target in pending:
        processed.add(target)
        for module in imports(files[target]):
            if not module.startswith('Compiler.'):
                continue
            rel = module.replace('.', '/') + '.lean'
            if rel in files:
                continue
            if rel in tracked:
                if rel not in base_dependencies:
                    base_dependencies[rel] = {'source': str(MAIN / rel), 'git_blob': subprocess.check_output(
                        ['git', 'rev-parse', f'{BASE}:{rel}'], cwd=MAIN, text=True).strip()}
                continue
            choices = list(candidates.get(rel, {}).values())
            assert choices, (rel, 'missing pinned off-tree prerequisite')
            assert len({item['sha256'] for item in choices}) == 1, (rel, 'dependency pin conflict')
            selected = choices[0]
            include(selected['source'], rel, selected['sha256'], 'required Infer prerequisite')

metadata = {'state': 'predecessors staged; awaiting final composition freeze' if PREPARE else 'assembled; integration checks pending',
    'base_commit': BASE, 'predecessor_patch': {'path': str(old_patch), 'sha256': sha(old_patch.read_bytes())},
    'files': records, 'completed_package_evidence': evidence, 'base_direct_dependencies': base_dependencies,
    'overlap_resolution': overlaps,
    'preserved_predecessor_resolution': old['exporter_resolution'],
    'excluded': ['separate TFHE/soundness expansions beyond the 51-file predecessor',
                 'paused restricted_ring_arithmetic', 'native runtime crates and proof/trace payloads',
                 'experimental PrintAxioms/ProfileStats runners and constant-regeneration scripts'],
    'scope': 'Compiler source and Lean exporters only; exact completed sources with import-only integration glue.'}

if not PREPARE:
    modules = {path for path in files if path.startswith('Compiler/')}
    referenced = {module.replace('.', '/') + '.lean' for path in modules for module in imports(files[path])}
    entries = sorted(modules - referenced)
    assert 'Compiler/FheArithmetic.lean' in entries
    entries.remove('Compiler/FheArithmetic.lean')
    entries.insert(0, 'Compiler/FheArithmetic.lean')
    umbrella = ('/- Completed compiler arithmetic for the saved nonlinear Infer.\n'
        'This imports the exact predecessor, source composition, witness exhibits and\n'
        'witness-plan producers. It adds no theorem or runtime/cryptographic refinement. -/\n'
        + ''.join('import ' + path[:-5].replace('/', '.') + '\n' for path in entries))
    files['Compiler/FheInfer.lean'] = umbrella.encode()
    records['Compiler/FheInfer.lean'] = {'source': 'new import-only integration glue',
        'sha256': sha(umbrella.encode()), 'group': 'integration'}
    previous_root = files['Compiler.lean']
    anchor = next(line for line in previous_root.decode().splitlines(keepends=True) if line.startswith('import Compiler.FheArithmetic '))
    hook = 'import Compiler.FheInfer  -- complete saved nonlinear Infer source dependencies; runtime trust boundaries remain explicit\n'
    files['Compiler.lean'] = previous_root.decode().replace(anchor, anchor + hook).encode()
    records['Compiler.lean'] = {'source': f'git:{BASE}:Compiler.lean plus predecessor and Infer imports',
        'sha256': sha(files['Compiler.lean']), 'group': 'integration',
        'predecessor_root_sha256': sha(previous_root), 'preserved_predecessor_import': anchor.strip()}
    overlaps.append({'target': 'Compiler.lean', 'resolution': 'retain predecessor FheArithmetic import; append one FheInfer import',
                     'predecessor_sha256': sha(previous_root), 'final_sha256': sha(files['Compiler.lean'])})
    graph = {path: [module.replace('.', '/') + '.lean' for module in imports(data)
                   if module.replace('.', '/') + '.lean' in files] for path, data in files.items()}
    order, done, active = [], set(), set()
    def visit(path):
        if path in done:
            return
        assert path not in active, ('import cycle', path)
        active.add(path)
        for dep in graph[path]:
            visit(dep)
        active.remove(path)
        done.add(path)
        order.append(path)
    visit('Compiler/FheInfer.lean')
    assert all(path in done for path in files if path.startswith('Compiler/')), sorted(set(files) - done)
    metadata['module_dependency_order'] = order.copy()
    for path in sorted(files):
        visit(path)
    metadata['all_file_order'] = order
    metadata['new_glue'] = ['Compiler/FheInfer.lean', 'Compiler.lean one additional import']
    base_root = subprocess.check_output(['git', 'show', f'{BASE}:Compiler.lean'], cwd=MAIN).decode()
    patch = []
    for target in sorted(files):
        assert target == 'Compiler.lean' or target not in tracked, (target, 'unexpected base-source replacement')
        before = base_root if target == 'Compiler.lean' else ''
        patch.append(f'diff --git a/{target} b/{target}\n')
        if target != 'Compiler.lean':
            patch.append('new file mode 100644\n')
        patch.extend(difflib.unified_diff(before.splitlines(keepends=True), files[target].decode().splitlines(keepends=True),
            fromfile=f'a/{target}' if target == 'Compiler.lean' else '/dev/null', tofile=f'b/{target}', n=2))
    patch_path = ROOT / 'minidregg-complete-infer.patch'
    patch_path.write_text(''.join(patch))
    metadata['patch_sha256'] = sha(patch_path.read_bytes())
    metadata['patch_bytes'] = patch_path.stat().st_size

tree = ROOT / 'proposal'
for target, data in files.items():
    path = tree / target
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_bytes(data)
(ROOT / 'PROVENANCE.json').write_text(json.dumps(metadata, indent=2) + '\n')
print(json.dumps({'state': metadata['state'], 'files': len(files),
    'compiler_modules': sum(path.startswith('Compiler/') for path in files),
    'exporters': sum(path.startswith('Emit') for path in files),
    'required_infer_prerequisites': [path for path, info in records.items() if info['group'] == 'required Infer prerequisite'],
    'patch_sha256': metadata.get('patch_sha256')}, indent=2))
