#!/usr/bin/env python3
"""Integrate explicit finished proposals, without writing to companion trees.

Reuse the lane checkers' read-only dependency-overlay technique, but compile every
selected proposal together in one fresh overlay, in import order. Discover modules
from the explicit patch manifest, never from ignored build trees or review copies.
Each run gets an immutable numbered report/log directory and a fresh scratch tree.
"""
from __future__ import annotations

import argparse
from collections import Counter
from datetime import datetime, timezone
import difflib
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import traceback

HERE = Path(__file__).resolve().parent
RESIDENT = HERE.parents[1]
COMPANION = Path('/Users/ember/dev/minidregg')
LEAN = '/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean'
UMBRELLAS = ('Theory', 'Compiler', 'Selvage', 'Assurance')
ALLOWED_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n')


def stripped_lean(source: str) -> str:
    """Mask nested comments and strings, retaining positions and line numbers.

    This is a lexical census, not a substitute for the Lean parser/kernel. All
    final sources are also elaborated with their exact-output axiom guards.
    """
    out = list(source)
    i = 0
    while i < len(source):
        start = i
        if source.startswith('/-', i):
            depth = 1
            i += 2
            while i < len(source) and depth:
                if source.startswith('/-', i):
                    depth += 1
                    i += 2
                elif source.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
            if depth:
                raise ValueError('Unclosed Lean comment')
        elif source.startswith('--', i):
            i = source.find('\n', i)
            if i == -1:
                i = len(source)
        elif source[i] == '"':
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            i += 1
            continue
        for j in range(start, min(i, len(source))):
            if source[j] != '\n':
                out[j] = ' '
    return ''.join(out)


def imports(source: str) -> list[str]:
    return re.findall(r'^\s*import\s+([A-Za-z_][\w.]*)', stripped_lean(source), re.M)


def census(source: str) -> dict:
    clean = stripped_lean(source)
    declarations = re.findall(r'\b(?:theorem|lemma)\s+([\w.\']+)', clean)
    # Match each actual documentation block independently, then require a guard
    # immediately after it. This avoids crossing unrelated documentation blocks.
    pins = []
    for comment in re.finditer(r'/--(?:(?!-/)[\s\S])*?-/', source):
        msg = re.fullmatch(r"\s*info:\s*'([^']+)'\s+(depends on axioms:\s*\[([\s\S]*?)\]|does not depend on any axioms)\s*", comment.group()[3:-2])
        if not msg:
            continue
        guard = re.match(r'\s*#guard_msgs(?:\s*\([^)]*\))?\s+in\s+#print\s+axioms\s+([\w.\']+)', source[comment.end():])
        if not guard:
            raise ValueError('Axiom output comment without adjacent exact guard')
        axioms = [] if msg.group(3) is None else re.findall(r'[\w.]+', msg.group(3))
        if not set(axioms) <= ALLOWED_AXIOMS:
            raise ValueError(f'Unexpected axiom set: {axioms}')
        pins.append(dict(theorem=msg.group(1), requested_name=guard.group(1),
                         axioms=axioms, line=source.count('\n', 0, comment.start()) + 1,
                         expected_message=' '.join(comment.group()[3:-2].split())))
    raw_prints = re.findall(r'#print\s+axioms\s+([\w.\']+)', clean)
    forbidden = [dict(token=m.group(), line=clean.count('\n', 0, m.start()) + 1)
                 for m in re.finditer(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|run_tac)\b|#(?:eval|run)\b', clean)]
    names = [p['theorem'] for p in pins]
    if len(names) != len(set(names)):
        raise ValueError('Duplicate theorem axiom pin')
    if len(raw_prints) != len(pins):
        raise ValueError(f'Unguarded axiom print: {len(raw_prints)} prints, {len(pins)} guards')
    if len(declarations) != len(pins):
        raise ValueError(f'Theorem/pin count differs: {len(declarations)} vs {len(pins)}')
    unmatched = [name for name in declarations
                 if sum(p['theorem'] == name or p['theorem'].endswith('.' + name) for p in pins) != 1]
    if unmatched:
        raise ValueError(f'Theorem-to-pin matching ambiguous or absent: {unmatched}')
    if forbidden:
        raise ValueError(f'Forbidden constructs in proposed proof source: {forbidden}')
    return dict(theorems=declarations, theorem_count=len(declarations), pin_count=len(pins),
                pins=pins, forbidden_constructs=forbidden,
                lexical_scope='Comments and strings masked; Lean elaboration checks exact guard messages.')


def topo(nodes: dict[str, list[str]]) -> list[str]:
    pending = {key: set(value) & nodes.keys() for key, value in nodes.items()}
    order = []
    while pending:
        ready = sorted(key for key, deps in pending.items() if not deps)
        if not ready:
            raise ValueError(f'Import cycle among selected modules: {pending}')
        for key in ready:
            order.append(key)
            del pending[key]
        for deps in pending.values():
            deps.difference_update(ready)
    return order


class Run:
    def __init__(self):
        results = HERE / 'results'
        results.mkdir(exist_ok=True)
        number = max([int(p.name.split('_')[-1]) for p in results.glob('run_*') if p.is_dir()] + [0]) + 1
        self.name = f'run_{number:03}'
        self.results = results / self.name
        self.scratch = HERE / 'build' / self.name
        self.results.mkdir()
        self.scratch.mkdir(parents=True)
        self.report = dict(label='EXECUTED integration of selected proposed Lean modules',
                           status='running', started_utc=datetime.now(timezone.utc).isoformat(),
                           command=[sys.executable, *sys.argv], commands=[],
                           no_clean_full_build_claim=True, metered_search_queries=0)
        self.inputs = {}
        self.companion_sources = []
        self.start = time.monotonic()

    def snapshot(self, paths):
        return {str(p): sha(p) if p.is_file() else None for p in sorted(set(paths))}

    def command(self, label, command, cwd, env=None, source=None, require=True):
        before = sha(source) if source else None
        started = time.monotonic()
        p = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True)
        record = dict(label=label, command=[str(x) for x in command], cwd=str(cwd),
                      exit_code=p.returncode, stdout=p.stdout, stderr=p.stderr,
                      elapsed_seconds=time.monotonic() - started)
        if env and 'LEAN_PATH' in env:
            record['lean_path'] = env['LEAN_PATH']
        if source:
            record.update(source=str(source), source_sha256_before=before,
                          source_sha256_after=sha(source))
            if record['source_sha256_after'] != before:
                raise RuntimeError(f'Source changed while compiling {source}')
        filename = f'{len(self.report["commands"]) + 1:03}_{label}.json'
        save(self.results / filename, record)
        self.report['commands'].append(dict(label=label, log=filename, exit_code=p.returncode))
        print(f'{label}: exit {p.returncode} ({record["elapsed_seconds"]:.2f}s)', flush=True)
        if p.returncode:
            print(p.stdout + p.stderr, flush=True)
        if require and p.returncode:
            raise RuntimeError(f'{label} failed; see {filename}')
        return record

    def finish(self):
        if self.inputs:
            after = self.snapshot([Path(p) for p in self.inputs])
            self.report['input_hashes_before'] = self.inputs
            self.report['input_hashes_after'] = after
            self.report['changed_inputs'] = [p for p in self.inputs if self.inputs[p] != after[p]]
        if self.companion_sources:
            after = self.snapshot(self.companion_sources)
            save(self.results / 'companion_source_hashes_after.json', after)
            before = json.loads((self.results / 'companion_source_hashes_before.json').read_text())
            self.report['changed_companion_sources'] = [p for p in before if before[p] != after[p]]
        for key, cmd in [('companion_head_after', ['git', 'rev-parse', 'HEAD']),
                         ('companion_status_after', ['git', 'status', '--short'])]:
            result = self.command(key, cmd, COMPANION, require=False)
            self.report[key] = result['stdout']
        if self.report.get('changed_inputs') or self.report.get('changed_companion_sources'):
            self.report['status'] = 'failed_source_changed'
        if self.report.get('companion_head_before') != self.report.get('companion_head_after'):
            self.report['status'] = 'failed_companion_head_changed'
        if self.report.get('companion_status_before') != self.report.get('companion_status_after'):
            self.report['status'] = 'failed_companion_status_changed'
        self.report['elapsed_seconds'] = time.monotonic() - self.start
        self.report['finished_utc'] = datetime.now(timezone.utc).isoformat()
        save(self.results / 'report.json', self.report)
        save(HERE / 'results/latest.json', dict(report=str((self.results / 'report.json').relative_to(RESIDENT)),
                                                status=self.report['status']))
        print(f'{self.name}: {self.report["status"]}; report {self.results / "report.json"}', flush=True)


def integrate(run: Run, manifest_path: Path, with_checks: bool):
    manifest = json.loads(manifest_path.read_text())
    run.report['manifest'] = manifest
    for key, cmd in [('companion_head_before', ['git', 'rev-parse', 'HEAD']),
                     ('companion_status_before', ['git', 'status', '--short'])]:
        run.report[key] = run.command(key, cmd, COMPANION)['stdout']
    run.command('lean_version', [LEAN, '--version'], HERE)
    source_list = run.command('companion_source_list', ['git', 'ls-files', '--cached', '--others',
                                                       '--exclude-standard', '*.lean'], COMPANION)
    relative_sources = sorted(set(source_list['stdout'].splitlines()))
    for rel in relative_sources:
        if Path(rel).is_absolute() or '..' in Path(rel).parts:
            raise ValueError('Unsafe companion source path')
    run.companion_sources = [COMPANION / rel for rel in relative_sources]
    run.companion_sources.append(COMPANION / 'scripts/check-import-boundary.sh')
    save(run.results / 'companion_source_hashes_before.json', run.snapshot(run.companion_sources))
    env_record = RESIDENT / 'experiments/results/environment.json'
    modules = {}
    patch_records = []
    inputs = [Path(__file__).resolve(), manifest_path, env_record]
    for lane in manifest['lanes']:
        patch_path = RESIDENT / lane['patch']
        inputs.append(patch_path)
        patch_text = patch_path.read_text()
        destinations = re.findall(r'^\+\+\+ b/(.+\.lean)$', patch_text, re.M)
        lane_pins = 0
        for dest in destinations:
            if dest in [u + '.lean' for u in UMBRELLAS]:
                continue
            if Path(dest).is_absolute() or '..' in Path(dest).parts:
                raise ValueError('Unsafe patch destination')
            module = dest[:-5].replace('/', '.')
            if module in modules:
                raise ValueError(f'Duplicate proposed module {module}')
            source = RESIDENT / lane['root'] / dest
            inputs.append(source)
            text = source.read_text()
            inventory = census(text)
            lane_pins += inventory['pin_count']
            # Verify the lane patch really carries this exact new-file source.
            section = re.split(r'^\+\+\+ b/' + re.escape(dest) + r'\n', patch_text, maxsplit=1, flags=re.M)[1]
            section = re.split(r'^(?:diff --git |--- )', section, maxsplit=1, flags=re.M)[0]
            added = ''.join(line[1:] for line in section.splitlines(keepends=True) if line.startswith('+'))
            if added != text:
                raise ValueError(f'Lane patch source differs from selected file: {source}')
            modules[module] = dict(source=source, dest=dest, text=text, imports=imports(text),
                                   lane=lane['name'], census=inventory)
        if lane_pins != lane['expected_pins']:
            raise ValueError(f'Pin count changed for lane {lane["name"]}: {lane_pins}')
        patch_records.append(dict(path=str(patch_path), sha256=sha(patch_path),
                                  lane=lane['name'], discovered_destinations=destinations))
    for rel in manifest.get('checks', []):
        inputs.append(RESIDENT / rel)
    run.inputs = run.snapshot(inputs)
    run.report['lane_patches'] = patch_records
    run.report['module_count'] = len(modules)
    run.report['theorem_pins'] = sum(m['census']['pin_count'] for m in modules.values())
    if run.report['theorem_pins'] != manifest['expected_theorem_pins']:
        raise ValueError('Combined theorem pin total changed')
    inventory = {name: dict(source=str(m['source']), sha256=sha(m['source']), dest=m['dest'],
                             imports=m['imports'], lane=m['lane'], **m['census']) for name, m in modules.items()}
    save(run.results / 'axiom_census.json', inventory)
    run.report['axiom_sets'] = dict(Counter(','.join(sorted(p['axioms'])) or '(none)'
                                          for m in modules.values() for p in m['census']['pins']))
    module_order = topo({name: m['imports'] for name, m in modules.items()})
    run.report['module_compile_order'] = module_order

    # Source-only baseline copy: all current tracked/untracked nonignored Lean
    # files, preserving current dirty umbrella bytes. Never patch a symlink.
    source_root = run.scratch / 'source'
    source_root.mkdir()
    for rel in relative_sources + ['scripts/check-import-boundary.sh']:
        target = source_root / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(COMPANION / rel, target)
    run.command('isolated_git_init', ['git', 'init', '-q'], source_root)
    combined = ''
    staged_umbrellas = {}
    for umbrella in UMBRELLAS:
        original = (source_root / (umbrella + '.lean')).read_text()
        existing = set(imports(original))
        additions = [name for name in module_order if name.startswith(umbrella + '.') and name not in existing]
        staged = original.rstrip('\n') + '\n\n' + ''.join('import ' + name + '\n' for name in additions)
        staged_umbrellas[umbrella] = staged
        combined += ''.join(difflib.unified_diff(original.splitlines(True), staged.splitlines(True),
                                                fromfile='a/' + umbrella + '.lean', tofile='b/' + umbrella + '.lean'))
    for name in module_order:
        m = modules[name]
        if (source_root / m['dest']).exists():
            raise ValueError(f'Proposed new module already exists in companion: {m["dest"]}')
        combined += ''.join(difflib.unified_diff([], m['text'].splitlines(True),
                                                fromfile='/dev/null', tofile='b/' + m['dest']))
    patch_path = RESIDENT / 'formal/integration/minidregg-combined-resident.patch'
    patch_path.parent.mkdir(parents=True, exist_ok=True)
    patch_path.write_text(combined)
    (run.results / patch_path.name).write_text(combined)
    run.report['combined_patch'] = dict(path=str(patch_path), sha256=sha(patch_path),
                                       baseline='Current companion source bytes, including dirty Compiler.lean.')
    run.command('combined_patch_check', ['git', 'apply', '--check', str(patch_path)], source_root)
    run.command('combined_patch_apply', ['git', 'apply', str(patch_path)], source_root)
    expected = {m['dest']: m['text'] for m in modules.values()}
    expected.update({u + '.lean': text for u, text in staged_umbrellas.items()})
    for rel, text in expected.items():
        if (source_root / rel).read_text() != text:
            raise ValueError(f'Combined patch content mismatch: {rel}')
    save(run.results / 'applied_source_hashes.json', {rel: sha(source_root / rel) for rel in expected})
    run.report['combined_patch_exact_content_verified'] = True
    run.command('boundary_applied_source', ['bash', str(source_root / 'scripts/check-import-boundary.sh')], source_root)
    run.command('boundary_existing_companion', ['bash', str(COMPANION / 'scripts/check-import-boundary.sh')], COMPANION)

    # Mirror all companion artifact directories with real local directories and
    # file symlinks. A namespace in the first LEAN_PATH root shadows later roots;
    # a partial namespace directory cannot rely on per-module fallback.
    overlay = run.scratch / 'olean'
    overlay.mkdir()
    artifacts = COMPANION / '.lake/build/lib/lean'
    skip_modules = set(modules) | set(UMBRELLAS)
    artifact_records = []
    for folder, dirs, files in os.walk(artifacts):
        relfolder = Path(folder).relative_to(artifacts)
        targetfolder = overlay / relfolder
        targetfolder.mkdir(parents=True, exist_ok=True)
        for filename in files:
            source = Path(folder) / filename
            rel = source.relative_to(artifacts)
            base = rel.as_posix().split('.')[0].replace('/', '.')
            if base in skip_modules:
                continue
            (targetfolder / filename).symlink_to(source)
            st = source.stat()
            artifact_records.append(dict(path=str(source), size=st.st_size, mtime_ns=st.st_mtime_ns))
    save(run.results / 'cached_dependency_artifacts.json', artifact_records)
    prior = json.loads(env_record.read_text())
    paths = next(c['stdout'].strip() for c in prior['checks'] if c['command'] == ['lake', 'env', 'printenv', 'LEAN_PATH'])
    env = dict(os.environ, LEAN_PATH=str(overlay) + ':' + paths)
    run.report['lean_path'] = env['LEAN_PATH']
    run.report['environment_provenance'] = dict(path=str(env_record), sha256=sha(env_record),
                                                source_command=['lake', 'env', 'printenv', 'LEAN_PATH'],
                                                reused_dependency_paths=True)
    all_compile = {name: m['imports'] for name, m in modules.items()}
    all_compile.update({u: imports(text) for u, text in staged_umbrellas.items()})
    order = topo(all_compile)
    run.report['full_compile_order'] = order
    outputs = {}
    for name in order:
        rel = name.replace('.', '/')
        source = source_root / (rel + '.lean')
        output = overlay / (rel + '.olean')
        output.parent.mkdir(parents=True, exist_ok=True)
        if output.is_symlink() or not output.resolve().is_relative_to(run.scratch.resolve()):
            raise RuntimeError(f'Refuse output outside isolated overlay: {output}')
        run.command('lean_' + name.replace('.', '_'), [LEAN, '-o', str(output), str(source)], source_root, env, source)
        outputs[name] = dict(path=str(output), sha256=sha(output))
    save(run.results / 'compiled_olean_hashes.json', outputs)
    run.report['umbrella_builds'] = list(UMBRELLAS)
    run.report['checks_executed'] = []
    if with_checks:
        check_cwd = run.scratch / 'checks/formal/integer_certificate_emission'
        check_results = run.scratch / 'checks/experiments/integer_certificate_emission'
        check_cwd.mkdir(parents=True)
        check_results.mkdir(parents=True)
        for rel in manifest.get('checks', []):
            original = RESIDENT / rel
            source = check_cwd / 'Compiler' / original.name
            source.parent.mkdir(exist_ok=True)
            shutil.copy2(original, source)
            output = overlay / 'Compiler' / (source.stem + '.olean')
            if output.is_symlink():
                raise RuntimeError('Refuse checker output through symlink')
            run.command('lean_checks_' + source.stem, [LEAN, '-o', str(output), str(source)], check_cwd, env, source)
            run.report['checks_executed'].append(str(original))
        saved = run.results / 'integer_check_outputs'
        shutil.copytree(check_results, saved)
        run.report['check_output_hashes'] = {p.name: sha(p) for p in sorted(saved.iterdir()) if p.is_file()}
    run.report['status'] = 'passed'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--manifest', type=Path, default=HERE / 'modules.json')
    parser.add_argument('--checks', action='store_true', help='Run integer #eval checks in isolated output directories.')
    args = parser.parse_args()
    run = Run()
    try:
        integrate(run, args.manifest.resolve(), args.checks)
    except Exception as error:
        run.report['status'] = 'failed'
        run.report['error'] = str(error)
        run.report['traceback'] = traceback.format_exc()
        print(run.report['traceback'], flush=True)
    finally:
        run.finish()
    return 0 if run.report['status'] == 'passed' else 1


if __name__ == '__main__':
    raise SystemExit(main())
