#!/usr/bin/env python3
"""Observed clean-producer cache export and read-only admission planning.

No Lean, subprocess, ambient environment inspection, or overlay installation.
Only export_completed_run writes, and only to fresh caller-selected export paths.
The caller must authorize export separately. All other public APIs are read-only.
See adversarial_review/verified_project_cache_implementation/REPORT.md for scope.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import re
import stat
from datetime import datetime, timezone

BUILD_ROOT = Path(__file__).resolve().parent / 'build'
UMBRELLAS = ('Theory', 'Compiler', 'Selvage', 'Assurance')
SCHEMA = 'observed-verified-project-cache-v1'
MODULE = re.compile(r'[A-Za-z_][A-Za-z_0-9]*(?:\.[A-Za-z_][A-Za-z_0-9]*)*\Z')
HASH = re.compile(r'[a-f0-9]{64}\Z')


class CacheError(ValueError):
    """A required provenance, path, byte or resolver check did not pass."""


def require(condition, message):
    if not condition:
        raise CacheError(message)


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'), allow_nan=False).encode()


def digest(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def _json(path):
    # Reject duplicate keys, rather than accepting an ambiguous signed/pinned map.
    def pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, f'Duplicate JSON key: {key}')
            result[key] = value
        return result
    return json.loads(Path(path).read_bytes(), object_pairs_hook=pairs)


def _regular(path):
    path = Path(path)
    require(path.is_absolute(), f'Absolute path required: {path}')
    for parent in (path, *path.parents):
        require(not parent.is_symlink(), f'Symlink forbidden: {parent}')
    require(path.is_file() and stat.S_ISREG(path.stat().st_mode), f'Regular file required: {path}')
    return path


def file_pin(path, *, allow_file_link=False):
    path = Path(path)
    if not allow_file_link:
        _regular(path)
    before = path.stat()
    require(stat.S_ISREG(before.st_mode), f'Nonregular input: {path}')
    h = hashlib.sha256()
    with path.open('rb') as stream:
        while block := stream.read(1024 * 1024):
            h.update(block)
    after = path.stat()
    require((before.st_size, before.st_mtime_ns, before.st_ino) ==
            (after.st_size, after.st_mtime_ns, after.st_ino), f'Input changed during hash: {path}')
    return {'sha256': h.hexdigest(), 'bytes': after.st_size}


def _relative(value):
    path = Path(value)
    require(isinstance(value, str) and value and not path.is_absolute()
            and '..' not in path.parts and '.' not in path.parts
            and str(path) == value, f'Unsafe relative path: {value}')
    return path


def _fresh(path):
    path = Path(path)
    require(path.is_absolute() and not path.exists() and not path.is_symlink(), f'Fresh absolute directory required: {path}')
    require(path.resolve() == path, f'Canonical export path required: {path}')
    for parent in path.parents:
        require(not parent.is_symlink(), f'Symlink parent forbidden: {parent}')
    return path


def _files(root):
    root = Path(root)
    require(root.is_dir() and root.resolve() == root, f'Canonical directory required: {root}')
    result = {}
    for directory, folders, names in os.walk(root):
        for folder in folders:
            require(not (Path(directory) / folder).is_symlink(), 'Directory symlink forbidden')
        for name in names:
            path = Path(directory) / name
            result[str(path.relative_to(root))] = file_pin(path)
    return result


def _masked(source):
    out, i = list(source), 0
    while i < len(source):
        start = i
        if source.startswith('/-', i):
            depth, i = 1, i + 2
            while i < len(source) and depth:
                if source.startswith('/-', i):
                    depth, i = depth + 1, i + 2
                elif source.startswith('-/', i):
                    depth, i = depth - 1, i + 2
                else:
                    i += 1
            require(depth == 0, 'Unclosed Lean comment')
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            i += 1
            closed = False
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i, closed = i + 1, True
                    break
                else:
                    i += 1
            require(closed, 'Unclosed Lean string')
        else:
            i += 1
            continue
        for j in range(start, min(i, len(source))):
            if source[j] != '\n':
                out[j] = ' '
    return ''.join(out)


def parse_header(source):
    """The producer's plain import subset, with explicit implicit-Init accounting."""
    clean = _masked(source)
    found = []
    for header in re.finditer(r'^[ \t]*(?:(?:public|private|meta)[ \t]+)*import\b[^\n]*', clean, re.M):
        match = re.fullmatch(r'[ \t]*import[ \t]+([^\n]+)', header.group())
        require(match is not None, f'Unsupported import: {header.group()}')
        names = match.group(1).split()
        require(names and all(MODULE.fullmatch(name) for name in names), 'Unsupported module name')
        found.extend(names)
    require(len(found) == len(set(found)), 'Duplicate import requires an explicit parser successor')
    require(not re.search(r'^\s*(?:public\s+)?module\b', clean, re.M), 'Lean module-system header unsupported in v1')
    prelude = list(re.finditer(r'^[ \t]*prelude\b[^\n]*', clean, re.M))
    require(len(prelude) <= 1 and all(m.group().strip() == 'prelude' for m in prelude), 'Unsupported prelude command')
    return {'imports': found, 'implicit_init': not bool(prelude)}


def _topo(nodes):
    pending = {name: set(row['project_dependencies']) for name, row in nodes.items()}
    require(all(deps <= nodes.keys() for deps in pending.values()), 'Missing project dependency')
    result = []
    while pending:
        ready = sorted(name for name, deps in pending.items() if not deps)
        require(ready, 'Cyclic project graph')
        result.extend(ready)
        for name in ready:
            del pending[name]
        for deps in pending.values():
            deps.difference_update(ready)
    return result


def _source_tree(root):
    root = Path(root)
    require(root.is_dir() and root.resolve() == root, 'Canonical source directory required')
    nodes, inventory = {}, {}
    for directory, folders, names in os.walk(root):
        folders[:] = [f for f in folders if f != '.git']
        for folder in folders:
            require(not (Path(directory) / folder).is_symlink(), 'Source directory symlink')
        for filename in names:
            if not filename.endswith('.lean'):
                continue
            path = Path(directory) / filename
            rel = str(path.relative_to(root))
            name = rel[:-5].replace('/', '.')
            require(MODULE.fullmatch(name), f'Unsupported source module path: {rel}')
            pin = file_pin(path)
            text = path.read_text()
            require(file_pin(path) == pin, f'Source changed during parse: {path}')
            inventory[rel] = pin
            nodes[name] = {'source_relative': rel, 'source_pin': pin, **parse_header(text)}
    require(set(UMBRELLAS) <= nodes.keys(), 'Four umbrellas required')
    for row in nodes.values():
        row['project_dependencies'] = [name for name in row['imports'] if name in nodes]
    seen, todo = set(), list(UMBRELLAS)
    while todo:
        name = todo.pop()
        if name not in seen:
            seen.add(name)
            todo.extend(nodes[name]['project_dependencies'])
    closure = {name: nodes[name] for name in sorted(seen)}
    _topo(closure)
    return closure, inventory


def _policy(policy):
    keys = {'schema', 'compiler', 'toolchain_root', 'external_roots', 'forbidden_project_roots',
            'lean_version', 'platform', 'lean_options', 'semantic_environment'}
    require(set(policy) == keys and policy['schema'] == 'explicit-lean-cli-policy-v1', 'Unknown compiler policy field/schema')
    require(policy['lean_options'] == [] and policy['semantic_environment'] == {}, 'v1 supports plain lean -o and no semantic environment overrides')
    require(policy['lean_version'] and policy['platform'], 'Explicit version/platform required')
    require(policy['external_roots'] and policy['forbidden_project_roots'], 'Explicit external and forbidden roots required')
    require(len(policy['external_roots']) == len(set(policy['external_roots'])), 'Duplicate external root')
    for value in [policy['compiler'], policy['toolchain_root'], *policy['external_roots'], *policy['forbidden_project_roots']]:
        require(isinstance(value, str) and Path(value).is_absolute(), 'Absolute explicit policy paths required')
    forbidden = [Path(p).resolve() for p in policy['forbidden_project_roots']]
    roots = [Path(p) for p in [*policy['external_roots'], policy['toolchain_root']]]
    for root in roots:
        require(root.resolve() == root and (root.is_dir() or not root.exists()), f'Canonical directory or absent cohort root required: {root}')
        for parent in (root, *root.parents):
            require(not parent.is_symlink(), f'Cohort root has a symlink ancestor: {parent}')
        require(all(not root.is_relative_to(ban) and not ban.is_relative_to(root) for ban in forbidden), 'Cohort overlaps forbidden project cache')
    require(Path(policy['toolchain_root']).is_dir(), 'Toolchain root must exist')
    compiler = _regular(Path(policy['compiler']))
    require(compiler.is_relative_to(Path(policy['toolchain_root'])), 'Compiler must belong to pinned toolchain root')
    return roots, forbidden


def observe_cohort(compiler_policy):
    """Hash only caller-explicit public package/toolchain trees; never inspect os.environ."""
    policy = json.loads(canonical(compiler_policy))
    roots, forbidden = _policy(policy)
    inventories = []
    for root in roots:
        entries = {}
        for directory, folders, names in os.walk(root):
            for folder in folders:
                path = Path(directory) / folder
                require(not path.is_symlink(), f'Cohort directory symlink unsupported: {path}')
                entries[str(path.relative_to(root)) + '/'] = {'kind': 'directory'}
            for filename in names:
                path = Path(directory) / filename
                resolved = path.resolve()
                require(any(resolved.is_relative_to(r) for r in roots), 'Cohort file link escapes explicit roots')
                require(all(not resolved.is_relative_to(ban) for ban in forbidden), 'Cohort file reaches forbidden project cache')
                row = {'kind': 'file', **file_pin(path, allow_file_link=True)}
                if path.is_symlink():
                    row.update(kind='file_symlink', link_target=os.readlink(path), resolved_target=str(resolved))
                entries[str(path.relative_to(root))] = row
        inventories.append({'root': str(root), 'present': root.is_dir(), 'entries': entries})
    return {'schema': 'observed-public-external-toolchain-cohort-v1', 'policy': policy,
            'trees': inventories, 'compiler_pin': file_pin(policy['compiler'])}


def _external_resolution(name, cohort):
    require(MODULE.fullmatch(name), 'Invalid imported module name')
    namespace, rel = name.split('.')[0], name.replace('.', '/') + '.olean'
    by_root = {row['root']: row['entries'] for row in cohort['trees']}
    for root in cohort['policy']['external_roots']:
        entries = by_root[root]
        if namespace + '/' in entries or namespace + '.olean' in entries:
            require(rel in entries and entries[rel]['kind'] in ('file', 'file_symlink'),
                    f'Namespace shadowing leaves unresolved module: {name} in {root}')
            return {'root': root, 'relative': rel, 'sha256': entries[rel]['sha256']}
    raise CacheError(f'Unresolved external import: {name}')


def _resolutions(nodes, cohort):
    namespaces = {name.split('.')[0] for name in nodes}
    result = {}
    for name, row in nodes.items():
        imports = row['imports'] + (['Init'] if row['implicit_init'] and 'Init' not in row['imports'] else [])
        resolved = []
        for imported in imports:
            if imported in nodes:
                resolved.append({'module': imported, 'owner': 'project'})
            else:
                require(imported.split('.')[0] not in namespaces,
                        f'Project namespace shadows external import: {imported}')
                resolved.append({'module': imported, 'owner': 'external', **_external_resolution(imported, cohort)})
        result[name] = resolved
    return result


def _input_keys(nodes, cohort_sha, policy_sha):
    result = {}
    for name in _topo(nodes):
        row = nodes[name]
        result[name] = digest({'module': name, 'source_pin': row['source_pin'], 'imports': row['imports'],
                               'implicit_init': row['implicit_init'], 'resolutions': row['resolutions'],
                               'cohort_sha256': cohort_sha, 'policy_sha256': policy_sha,
                               'dependencies': [(dep, result[dep], nodes[dep]['object_pin']) for dep in row['project_dependencies']]})
    return result


def _project_objects(root, nodes):
    inventory = _files(Path(root))
    expected = {name.replace('.', '/') + '.olean' for name in nodes}
    require(set(inventory) == expected, 'Project object tree has missing files or unrecorded sidecars/objects')
    _exact_directories(Path(root), expected)
    return inventory


def _exact_directories(root, relative_files):
    expected = {str(parent) for rel in relative_files for parent in Path(rel).parents if str(parent) != '.'}
    actual = {str((Path(directory) / folder).relative_to(root))
              for directory, folders, _ in os.walk(root) for folder in folders}
    require(actual == expected, 'Unplanned directory could change namespace resolution')


def _producer(run_dir, build_dir, expected_report_sha256, expected_harness_sha256, policy):
    """Read the saved report schema without importing or executing the archived harness."""
    run_dir, build_dir = Path(run_dir), Path(build_dir)
    report_pin = file_pin(run_dir / 'report.json')
    require(report_pin['sha256'] == expected_report_sha256, 'Producer report hash mismatch')
    require(file_pin(run_dir / 'check_all_formal.py')['sha256'] == expected_harness_sha256, 'Archived harness hash mismatch')
    report = _json(run_dir / 'report.json')
    require(report['status'] == 'passed' and report['rebuild_project_source_closure'] is True, 'Producer is not a successful clean project closure')
    require(report['combined_patch_exact_content_verified'] is True and report['all_selected_modules_rooted'] is True, 'Producer source gates absent')
    for key in ('changed_inputs', 'changed_companion_sources'):
        require(report[key] == [], f'Producer changed: {key}')
    require(report['input_hashes_before'] == report['input_hashes_after'] and report['input_hashes_before'], 'Producer input stability failed')
    for key in ('companion_head', 'companion_status'):
        require(report[key + '_before'] == report[key + '_after'], f'Producer {key} changed')
    require(report['companion_head_before'], 'Producer companion identity absent')
    require(set(report['umbrella_builds']) == set(UMBRELLAS) and len(report['umbrella_builds']) == 4, 'Four umbrella builds missing')
    harness_inputs = [v for p, v in report['input_hashes_before'].items() if Path(p).name == 'check_all_formal.py']
    require(harness_inputs == [expected_harness_sha256], 'Archived harness not bound to successful input map')
    require(_json(run_dir / 'cached_dependency_artifacts.json') == [], 'Producer inherited project objects')
    require(_json(run_dir / 'companion_source_hashes_before.json') == _json(run_dir / 'companion_source_hashes_after.json'), 'Saved companion maps differ')
    evidence_names = {'report.json', 'check_all_formal.py', 'cached_dependency_artifacts.json',
                      'companion_source_hashes_before.json', 'companion_source_hashes_after.json',
                      'applied_source_hashes.json', 'axiom_census.json', 'compiled_olean_hashes.json'}
    candidates = []
    for original, sha in report['input_hashes_before'].items():
        candidate = run_dir / Path(original).name
        if candidate.suffix == '.json' and candidate.is_file() and file_pin(candidate)['sha256'] == sha:
            if _json(candidate) == report['manifest']:
                candidates.append(candidate.name)
    require(len(candidates) == 1, 'No unique exact archived input manifest')
    evidence_names.add(candidates[0])
    patch = report['combined_patch']
    patch_name = Path(patch['path']).name
    require(file_pin(run_dir / patch_name)['sha256'] == patch['sha256'], 'Archived combined patch mismatch')
    evidence_names.add(patch_name)
    logs = {}
    for row in report['commands']:
        rel = str(_relative(row['log']))
        require('/' not in rel and row['label'] not in logs, 'Duplicate or nested command log')
        log = _json(run_dir / rel)
        require(row['exit_code'] == log['exit_code'] == 0 and row['label'] == log['label'], 'Producer command did not pass')
        logs[row['label']] = log
        evidence_names.add(rel)
    for label in ('boundary_applied_source', 'boundary_existing_companion', 'combined_patch_check', 'combined_patch_apply'):
        require(label in logs, f'Missing producer gate: {label}')
    require(logs['lean_version']['stdout'].strip() == policy['lean_version'].strip(), 'Saved Lean version differs from explicit policy')
    require(logs['lean_version']['command'] == [policy['compiler'], '--version'], 'Saved compiler command differs')
    nodes, source_inventory = _source_tree(build_dir / 'source')
    census = _json(run_dir / 'axiom_census.json')
    require(set(census) <= nodes.keys(), 'Selected source is outside full closure')
    base_paths = logs['companion_source_list']['stdout'].splitlines()
    expected_sources = set(base_paths) | {row['dest'] for row in census.values()}
    require(set(source_inventory) == expected_sources, 'Isolated source inventory differs from source list plus selected modules')
    for rel, sha in _json(run_dir / 'applied_source_hashes.json').items():
        require(file_pin(build_dir / 'source' / _relative(rel))['sha256'] == sha, f'Applied source changed: {rel}')
    order = report['full_compile_order']
    require(len(order) == len(set(order)) == report['project_modules_compiled'] == len(nodes)
            and set(order) == set(nodes), 'Producer compile set/count mismatch')
    positions = {name: i for i, name in enumerate(order)}
    require(all(positions[dep] < positions[name] for name, row in nodes.items() for dep in row['project_dependencies']), 'Producer order is not topological')
    objects = _project_objects(build_dir / 'olean', nodes)
    output_map = _json(run_dir / 'compiled_olean_hashes.json')
    require(set(output_map) == set(nodes), 'Saved object map does not cover exact project closure')
    expected_lean_path = ':'.join([str(build_dir / 'olean'), *policy['external_roots']])
    require(report['lean_path'] == expected_lean_path, 'Producer LEAN_PATH differs from explicit roots')
    for name, row in nodes.items():
        label = 'lean_' + name.replace('.', '_')
        require(label in logs, f'Missing actual compile log: {name}')
        log = logs[label]
        source = build_dir / 'source' / row['source_relative']
        rel = name.replace('.', '/') + '.olean'
        output = build_dir / 'olean' / rel
        require(log['command'] == [policy['compiler'], '-o', str(output), str(source)] and log['cwd'] == str(build_dir / 'source'), 'Unexpected project compile argv/cwd')
        require(log['source'] == str(source) and log['source_sha256_before'] == log['source_sha256_after'] == row['source_pin']['sha256'], 'Compile source pin mismatch')
        require(log['lean_path'] == expected_lean_path, 'Per-command resolver path differs')
        require(not re.search(r'uses [‘\"\']?sorry|sorryAx', log['stdout'] + log['stderr']), 'Producer proof-placeholder diagnostic')
        require(output_map[name] == {'path': str(output), 'sha256': objects[rel]['sha256']}, 'Saved output byte hash mismatch')
        row.update(object_relative=rel, object_pin=objects[rel], producer_log=next(r['log'] for r in report['commands'] if r['label'] == label))
    actual_compiles = {label for label in logs if label.startswith('lean_') and label != 'lean_version'}
    require(actual_compiles == {'lean_' + name.replace('.', '_') for name in nodes}, 'Unaccounted project compile log')
    return report, nodes, source_inventory, {name: file_pin(run_dir / name) for name in sorted(evidence_names)}


def export_completed_run(*, run_dir, build_dir, metadata_dir, object_dir, compiler_policy,
                         expected_report_sha256, expected_harness_sha256):
    """Export after separate authorization; this function never runs Lean or a build.

    Large objects/source copies must be under integration/build/. A manifest is
    published last. Failure may leave an unsealed partial directory; never reuse it.
    """
    require(HASH.fullmatch(expected_report_sha256) and HASH.fullmatch(expected_harness_sha256), 'Explicit expected producer hashes required')
    run_dir, build_dir = Path(run_dir), Path(build_dir)
    metadata_dir, object_dir = _fresh(metadata_dir), _fresh(object_dir)
    require(object_dir.is_relative_to(BUILD_ROOT.resolve()), 'Object export must be under ignored integration/build/')
    require(not metadata_dir.is_relative_to(object_dir) and not object_dir.is_relative_to(metadata_dir), 'Metadata and object directories must be separate')
    require(all(not destination.is_relative_to(subject) and not subject.is_relative_to(destination)
                for destination in (metadata_dir, object_dir) for subject in (run_dir, build_dir)), 'Export cannot overlap producer paths')
    cohort = observe_cohort(compiler_policy)
    report, nodes, source_inventory, evidence = _producer(run_dir, build_dir, expected_report_sha256, expected_harness_sha256, compiler_policy)
    resolutions = _resolutions(nodes, cohort)
    for name, row in nodes.items():
        row['resolutions'] = resolutions[name]
    cohort_sha, policy_sha = digest(cohort), digest(compiler_policy)
    keys = _input_keys(nodes, cohort_sha, policy_sha)
    metadata_dir.mkdir(parents=True)
    object_dir.mkdir(parents=True)
    def copy(source, target, pin):
        target.parent.mkdir(parents=True, exist_ok=True)
        require(file_pin(source) == pin, f'Export input changed: {source}')
        with target.open('xb') as output, Path(source).open('rb') as stream:
            while block := stream.read(1024 * 1024):
                output.write(block)
        require(file_pin(target) == pin and file_pin(source) == pin, 'Export copy changed')
    for name, pin in evidence.items():
        copy(run_dir / name, metadata_dir / 'evidence' / name, pin)
    for row in nodes.values():
        copy(build_dir / 'source' / row['source_relative'], object_dir / 'source' / row['source_relative'], row['source_pin'])
        copy(build_dir / 'olean' / row['object_relative'], object_dir / 'olean' / row['object_relative'], row['object_pin'])
    require(observe_cohort(compiler_policy) == cohort, 'External/toolchain cohort changed during export')
    final_report, final_nodes, final_sources, final_evidence = _producer(run_dir, build_dir, expected_report_sha256, expected_harness_sha256, compiler_policy)
    require(final_report == report and final_sources == source_inventory and final_evidence == evidence, 'Producer changed during export')
    for name in nodes:
        require({k: v for k, v in nodes[name].items() if k != 'resolutions'} == final_nodes[name], 'Producer module changed during export')
    manifest = {'schema': SCHEMA, 'created_utc': datetime.now(timezone.utc).isoformat(),
                'cohort_basis': 'post_success_observed_trusted_external_cohort',
                'historical_external_prepost_attestation_claim': False,
                'historical_ambient_environment_attestation_claim': False,
                'producer': {'run_dir': str(run_dir), 'build_dir': str(build_dir), 'report_sha256': expected_report_sha256,
                             'archived_harness_sha256': expected_harness_sha256, 'project_modules_compiled': len(nodes)},
                'helper_sha256': file_pin(Path(__file__).resolve())['sha256'],
                'object_directory': str(object_dir), 'cohort': cohort, 'cohort_sha256': cohort_sha,
                'compiler_policy_sha256': policy_sha, 'modules': nodes, 'module_input_keys': keys,
                'source_inventory_at_export': source_inventory, 'evidence': _files(metadata_dir),
                'object_files': _files(object_dir), 'seed_promotion_from_cached_runs_permitted': False}
    path = metadata_dir / 'manifest.json'
    with path.open('xb') as stream:
        stream.write(json.dumps(manifest, indent=2, sort_keys=True).encode() + b'\n')
    _verify_export(path, file_pin(path)['sha256'])
    return {'manifest_path': str(path), 'manifest_pin': file_pin(path), 'project_modules': len(nodes),
            'cohort_sha256': cohort_sha, 'object_directory': str(object_dir)}


def _verify_export(manifest_path, expected_sha256):
    path = _regular(Path(manifest_path))
    require(file_pin(path)['sha256'] == expected_sha256, 'Cache manifest hash mismatch')
    manifest = _json(path)
    require(manifest['schema'] == SCHEMA and manifest['cohort_basis'] == 'post_success_observed_trusted_external_cohort', 'Unsupported cache schema/basis')
    require(manifest['historical_external_prepost_attestation_claim'] is False and manifest['seed_promotion_from_cached_runs_permitted'] is False, 'Unsupported provenance claim')
    actual = _files(path.parent)
    del actual[path.name]
    require(actual == manifest['evidence'], 'Export evidence bytes or membership changed')
    objects = Path(manifest['object_directory'])
    require(objects.is_relative_to(BUILD_ROOT.resolve()), 'Export object directory outside permitted storage')
    require(_files(objects) == manifest['object_files'], 'Export object/source bytes or membership changed')
    require(digest(manifest['cohort']) == manifest['cohort_sha256'] and digest(manifest['cohort']['policy']) == manifest['compiler_policy_sha256'], 'Cohort/policy digest mismatch')
    nodes, _ = _source_tree(objects / 'source')
    require(set(nodes) == set(manifest['modules']), 'Export source graph membership changed')
    object_pins = _project_objects(objects / 'olean', nodes)
    resolutions = _resolutions(nodes, manifest['cohort'])
    for name, row in nodes.items():
        saved = manifest['modules'][name]
        require(all(saved[k] == v for k, v in row.items()), 'Export source graph differs')
        require(saved['object_relative'] == name.replace('.', '/') + '.olean'
                and saved['object_pin'] == object_pins[saved['object_relative']]
                and saved['resolutions'] == resolutions[name], 'Export object/resolution binding differs')
    require(_input_keys(manifest['modules'], manifest['cohort_sha256'], manifest['compiler_policy_sha256']) == manifest['module_input_keys'], 'Transitive input key mismatch')
    require(file_pin(path.parent / 'evidence/report.json')['sha256'] == manifest['producer']['report_sha256']
            and file_pin(path.parent / 'evidence/check_all_formal.py')['sha256'] == manifest['producer']['archived_harness_sha256'], 'Producer evidence identity mismatch')
    return manifest


def _admission_records(old, nodes, cohort_sha, policy_sha, source_root, overlay_root):
    decisions, copies, rebuilds = {}, [], []
    for name in _topo(nodes):
        row, reasons = nodes[name], []
        if name in UMBRELLAS:
            reasons.append('umbrella_always_rebuilt')
        if cohort_sha != old['cohort_sha256'] or policy_sha != old['compiler_policy_sha256']:
            reasons.append('external_toolchain_or_policy_changed')
        if name not in old['modules']:
            reasons.append('new_module')
        else:
            previous = old['modules'][name]
            if any(previous[k] != row[k] for k in ('source_pin', 'imports', 'implicit_init', 'project_dependencies', 'resolutions')):
                reasons.append('source_import_or_resolution_changed')
        if any(decisions[dep]['action'] == 'rebuild' for dep in row['project_dependencies']):
            reasons.append('project_dependency_rebuilt')
        decisions[name] = {'action': 'rebuild' if reasons else 'copy', 'reasons': reasons}
        if reasons:
            rebuilds.append({'module': name, 'source': str(source_root / row['source_relative']),
                             'output': str(overlay_root / (name.replace('.', '/') + '.olean')), 'reasons': reasons})
        else:
            previous = old['modules'][name]
            copies.append({'module': name, 'source': str(Path(old['object_directory']) / 'olean' / previous['object_relative']),
                           'destination': str(overlay_root / previous['object_relative']), 'pin': previous['object_pin'],
                           'transitive_input_key': old['module_input_keys'][name], 'producer_log': previous['producer_log']})
    return decisions, copies, rebuilds


def plan_admission(*, manifest_path, expected_sha256, source_root, selected_modules, overlay_root, compiler_policy):
    """Read-only: return ordered copies/rebuilds after byte, graph and resolver checks."""
    manifest_path, source_root, overlay_root = Path(manifest_path), Path(source_root), Path(overlay_root)
    old = _verify_export(manifest_path, expected_sha256)
    require(overlay_root.is_absolute() and overlay_root.resolve() == overlay_root, 'Canonical overlay path required')
    require(not overlay_root.exists() or (overlay_root.is_dir() and not any(overlay_root.iterdir())), 'Prospective overlay must be absent or empty')
    for parent in (overlay_root, *overlay_root.parents):
        require(not parent.is_symlink(), 'Overlay symlink forbidden')
    for forbidden in compiler_policy['forbidden_project_roots']:
        require(not overlay_root.is_relative_to(Path(forbidden).resolve()), 'Overlay reaches forbidden main-project cache')
    require(not overlay_root.is_relative_to(source_root) and not source_root.is_relative_to(overlay_root), 'Source and overlay trees must be separate')
    nodes, sources = _source_tree(source_root)
    require(set(selected_modules) <= nodes.keys(), 'Selected module outside umbrella closure')
    cohort = observe_cohort(compiler_policy)
    resolutions = _resolutions(nodes, cohort)
    cohort_sha, policy_sha = digest(cohort), digest(compiler_policy)
    for name, row in nodes.items():
        row['resolutions'] = resolutions[name]
    decisions, copies, rebuilds = _admission_records(old, nodes, cohort_sha, policy_sha, source_root, overlay_root)
    result = {'schema': 'verified-project-cache-admission-plan-v1', 'parent_manifest': str(manifest_path),
              'parent_manifest_sha256': expected_sha256, 'source_root': str(source_root), 'overlay_root': str(overlay_root),
              'source_inventory': sources, 'modules': nodes, 'cohort': cohort, 'cohort_sha256': cohort_sha,
              'compiler_policy_sha256': policy_sha, 'ordered_copies': copies, 'ordered_rebuilds': rebuilds,
              'full_compile_order': _topo(nodes), 'decisions': decisions,
              'lean_path': ':'.join([str(overlay_root), *compiler_policy['external_roots']]),
              'project_cache_fallback_permitted': False, 'installation_performed': False}
    result['plan_sha256'] = digest(result)
    recheck_plan_inputs(result)
    return result


def _check_plan(plan):
    require(plan['schema'] == 'verified-project-cache-admission-plan-v1', 'Unknown admission plan')
    require(digest({k: v for k, v in plan.items() if k != 'plan_sha256'}) == plan['plan_sha256'], 'Admission plan changed')
    require(plan['project_cache_fallback_permitted'] is False and plan['installation_performed'] is False, 'Unsupported admission flags')


def recheck_plan_inputs(plan):
    """Read-only before/after compilation check of seed, sources and explicit cohort."""
    _check_plan(plan)
    old = _verify_export(Path(plan['parent_manifest']), plan['parent_manifest_sha256'])
    nodes, sources = _source_tree(Path(plan['source_root']))
    require(sources == plan['source_inventory'] and set(nodes) == set(plan['modules']), 'Prospective source tree changed')
    cohort = observe_cohort(plan['cohort']['policy'])
    require(cohort == plan['cohort'] and digest(cohort) == plan['cohort_sha256'], 'External/toolchain cohort changed since admission')
    resolved = _resolutions(nodes, cohort)
    for name, row in nodes.items():
        require({**row, 'resolutions': resolved[name]} == plan['modules'][name], 'Prospective source/import graph changed')
        row['resolutions'] = resolved[name]
    require(digest(cohort['policy']) == plan['compiler_policy_sha256'], 'Plan policy digest differs')
    decisions, copies, rebuilds = _admission_records(old, nodes, plan['cohort_sha256'], plan['compiler_policy_sha256'],
                                                   Path(plan['source_root']), Path(plan['overlay_root']))
    require((decisions, copies, rebuilds) == (plan['decisions'], plan['ordered_copies'], plan['ordered_rebuilds']), 'Plan copy/rebuild records differ from verified inputs')
    require(plan['full_compile_order'] == _topo(nodes)
            and plan['lean_path'] == ':'.join([plan['overlay_root'], *cohort['policy']['external_roots']]), 'Plan order/resolver differs')
    return {'ok': True, 'parent_manifest_sha256': plan['parent_manifest_sha256'],
            'cohort_sha256': plan['cohort_sha256'], 'source_inventory_sha256': digest(sources)}


def verify_staged_copies(plan):
    """Read-only precompile destination check; the wrapper alone performs copies."""
    recheck_plan_inputs(plan)
    overlay = Path(plan['overlay_root'])
    actual = _files(overlay)
    expected = {str(Path(row['destination']).relative_to(overlay)): row['pin'] for row in plan['ordered_copies']}
    require(actual == expected, 'Staged copies differ, or unplanned objects/sidecars exist')
    _exact_directories(overlay, expected)
    return {'ok': True, 'copied_modules': len(expected), 'destination_inventory_sha256': digest(actual)}


def verify_final_outputs(plan):
    """Read-only completion check: stable inputs, exact objects, unchanged copied bytes.

    Newly built hashes are observations for the wrapper's new report; this does
    not certify successful compilation or promote a cached run to a clean seed.
    """
    recheck_plan_inputs(plan)
    overlay = Path(plan['overlay_root'])
    outputs = _project_objects(overlay, plan['modules'])
    for row in plan['ordered_copies']:
        rel = str(Path(row['destination']).relative_to(overlay))
        require(outputs[rel] == row['pin'], 'Copied object changed during wrapper compilation')
    return {'ok': True, 'cohort_sha256': plan['cohort_sha256'], 'parent_manifest_sha256': plan['parent_manifest_sha256'],
            'object_files': outputs, 'object_inventory_sha256': digest(outputs), 'cache_seed_promotion_permitted': False}
