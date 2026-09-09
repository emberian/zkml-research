#!/usr/bin/env python3
"""Check the complete retained runtime; optionally rebuild missing executables.

Default/--check is read-only. --build builds only missing known executables,
offline in isolated target directories. It never overwrites an existing binary,
changes a pin, runs a proof, initializes a key, or loads the encoder model.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import tempfile
import time

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent
REPO = next(p for p in HERE.parents if (p / 'AGENTS.md').is_file())
DEFAULT_WORKER = RESEARCH / 'nonlinear_performance_successor/runtime/caller.py'
DEFAULT_PROFILE = DEFAULT_WORKER.parent / 'caller/PIPELINE.json'
HELPER = RESEARCH / 'proved_journal/live_nonlinear/fixture_builder/helper.py'
HELPER_PINS = HELPER.parent / 'SOURCE_PINS.json'
UTILITY = REPO / 'research/learn_infer_only/experiments/adaptation_utility'
ENCODER_PYTHON = UTILITY / '.venv/bin/python'
PACKAGES = ('numpy', 'torch', 'transformers', 'tokenizers', 'safetensors')


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()


def read(path):
    return json.loads(Path(path).read_text())


def python_environment(path):
    probe = """import importlib.metadata,json,sys
p={}
for name in ('numpy','torch','transformers','tokenizers','safetensors'):
 try:p[name]=importlib.metadata.version(name)
 except importlib.metadata.PackageNotFoundError:p[name]=None
print(json.dumps({'python':sys.executable,'version':list(sys.version_info[:3]),'packages':p}))
"""
    try:
        result = subprocess.run([str(path), '-c', probe], capture_output=True, text=True, timeout=15)
        if result.returncode:
            return {'python': str(path), 'ready': False, 'error': result.stderr.strip()}
        info = json.loads(result.stdout)
        info['ready'] = all(info['packages'].values()) and info['version'] >= [3, 10]
        return info
    except (OSError, ValueError, subprocess.TimeoutExpired) as exc:
        return {'python': str(path), 'ready': False, 'error': str(exc)}


def recipes():
    native = RESEARCH / 'nonlinear_performance/runtime/native'
    result = {}
    for package, binary in (('infer', 'vfhe-complete-kernel-infer'),
                            ('square', 'vfhe-full-bfv-multiply'),
                            ('rescale', 'vfhe-whole-rescale-runtime'),
                            ('update', 'vfhe-live-nonlinear-update')):
        result[binary] = native / package / 'Cargo.toml'
    result['lean-bigint-witness'] = RESEARCH / 'rescale_native_emitter/native/Cargo.toml'
    result['kernel-crypto'] = (REPO / 'research/learn_infer_only/experiments/end_to_end/'
                             'nonlinear_successor_2026_09_08/crypto/Cargo.toml')
    return result


def build_recipe(path):
    manifest = recipes().get(Path(path).name)
    if manifest is None:
        return None
    cargo = shutil.which('cargo') or str(Path.home() / '.cargo/bin/cargo')
    argv = [cargo, 'build', '--release', '--offline', '--locked', '--manifest-path',
            str(manifest), '--bin', Path(path).name]
    return {'manifest': str(manifest), 'argv': argv,
            'environment': {'CARGO_BUILD_JOBS': '4', 'RAYON_NUM_THREADS': '4',
                            'CARGO_TARGET_DIR': '<isolated-build-directory>/target'},
            'command': 'CARGO_BUILD_JOBS=4 RAYON_NUM_THREADS=4 '
                       'CARGO_TARGET_DIR=/absolute/new-build/target ' + shlex.join(argv),
            'source_available': manifest.is_file() and manifest.with_name('Cargo.lock').is_file()}


def inspect(profile, worker):
    result = {'ready': False, 'profile': str(profile), 'worker': str(worker),
              'files_checked': 0, 'issues': [], 'executables': [],
              'runtime_artifacts': 'Retained JSON templates, witness plans and linear plan; Lean rebuild is not needed to launch.',
              'portability': 'The retained profiles, encoder configuration and Cargo path dependencies contain absolute workspace/cache paths. This is a retained-workspace bootstrap, not a portable fresh-clone installer.'}
    try:
        config = read(profile)
        if config.get('schema') != 'caller-selected-profiled-kernel-v1':
            raise ValueError('unsupported profile schema')
        expected = dict(config['pins'])
        issuer = read(HELPER_PINS)
        for entry in issuer['sources'] + issuer['model']:
            old = expected.setdefault(entry['path'], entry['sha256'])
            if old != entry['sha256']:
                raise ValueError('conflicting pins for ' + entry['path'])
    except (OSError, ValueError, KeyError) as exc:
        result['issues'].append({'kind': 'profile', 'error': str(exc),
                                 'action': 'Restore the retained caller profile and issuer SOURCE_PINS.json.'})
        return result
    executable_paths = {str(Path(p).resolve()) for p in config['native'].values()}
    executable_paths.add(str(Path(config['zstd']).resolve()))
    for profiles in config['profiles'].values():
        executable_paths.update(str(Path(p['executor']).resolve()) for p in profiles)
    executable_paths.update(entry['path'] for entry in issuer['sources']
                            if '/target/release/' in entry['path'])
    for text, digest in expected.items():
        path = Path(text)
        executable = str(path.resolve()) in executable_paths
        state = 'valid'
        actual = None
        try:
            actual = sha(path)
            if actual != digest:
                state = 'hash-mismatch'
            elif executable and not os.access(path, os.X_OK):
                state = 'not-executable'
        except FileNotFoundError:
            state = 'missing'
        except OSError as exc:
            state = 'unreadable: ' + str(exc)
        result['files_checked'] += 1
        item = {'path': text, 'state': state, 'expected_sha256': digest}
        if actual and state != 'valid':
            item['actual_sha256'] = actual
        if executable:
            item['build'] = build_recipe(path)
            result['executables'].append(item)
        if state != 'valid':
            item = dict(item, kind='executable' if executable else 'retained-artifact')
            item['action'] = ('Use --build to reconstruct this missing executable; installation requires its exact pinned hash.'
                              if executable and state == 'missing' and item['build'] else
                              'Restore this exact pinned file or deliberately create a new development profile; bootstrap does not overwrite files or rewrite frozen pins.')
            result['issues'].append(item)
    if not worker.is_file():
        result['issues'].append({'kind': 'worker', 'path': str(worker), 'state': 'missing',
                                 'action': 'Restore continuing-system caller.py.'})
    current = python_environment(sys.executable)
    candidate = current if current['ready'] else python_environment(ENCODER_PYTHON)
    result['current_python'] = current
    result['selected_python'] = candidate
    result['python_lock'] = str(UTILITY / 'requirements-lock.txt')
    if not candidate['ready']:
        result['issues'].append({'kind': 'python-environment',
                                 'action': 'Restore adaptation_utility/.venv with requirements-lock.txt, then run the app with that interpreter. No packages are installed automatically.'})
    result['current_python_can_run_encoder'] = current['ready']
    result['ready'] = not result['issues']
    return result


def build_missing(check):
    builds = []
    for item in check['executables']:
        if item['state'] != 'missing' or not item['build']:
            continue
        recipe = item['build']
        record = {'destination': item['path'], 'expected_sha256': item['expected_sha256'],
                  'installed': False, 'argv': recipe['argv']}
        if not Path(item['path']).resolve().is_relative_to(REPO):
            record['error'] = 'Automatic build/install is limited to the research working tree; companion and system paths are not modified.'
            builds.append(record)
            continue
        if not recipe['source_available']:
            record['error'] = 'Retained Cargo.toml/Cargo.lock missing; restore source before building.'
            builds.append(record)
            continue
        root = Path(tempfile.mkdtemp(prefix='continuing-bootstrap-'))
        env = dict(os.environ, CARGO_TARGET_DIR=str(root / 'target'),
                   CARGO_BUILD_JOBS='4', RAYON_NUM_THREADS='4')
        record['build_directory'] = str(root)
        record['environment'] = {key: env[key] for key in recipe['environment']}
        record['log'] = str(root / 'build.log')
        print('Building missing ' + item['path'] + '; log: ' + record['log'], file=sys.stderr, flush=True)
        started = time.monotonic()
        try:
            with (root / 'build.log').open('wb') as log:
                proc = subprocess.run(recipe['argv'], cwd=HERE, env=env, stdout=log,
                                      stderr=subprocess.STDOUT, timeout=1800)
            record['returncode'] = proc.returncode
            candidate = root / 'target/release' / Path(item['path']).name
            if proc.returncode or not candidate.is_file():
                record['error'] = 'Offline build failed; inspect build.log for missing local path dependencies/toolchain/cache.'
            else:
                record['candidate'] = str(candidate)
                record['candidate_sha256'] = sha(candidate)
                if record['candidate_sha256'] != item['expected_sha256']:
                    record['error'] = 'Build succeeded with different bytes. Candidate retained; original profile and destination unchanged. Reproduce the recorded toolchain/build identity or create an explicitly approved development profile.'
                else:
                    destination = Path(item['path'])
                    destination.parent.mkdir(parents=True, exist_ok=True)
                    fd, temporary = tempfile.mkstemp(prefix='.bootstrap-', dir=destination.parent)
                    os.close(fd)
                    try:
                        shutil.copy2(candidate, temporary)
                        os.link(temporary, destination)  # atomic exclusive install; never replace
                    finally:
                        os.unlink(temporary)
                    record['installed'] = True
        except (OSError, subprocess.TimeoutExpired) as exc:
            record['error'] = str(exc)
        record['elapsed_seconds'] = time.monotonic() - started
        (root / 'BUILD.json').write_text(json.dumps(record, indent=2) + '\n')
        builds.append(record)
    return builds


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--check', action='store_true', help='Check retained runtime (default)')
    mode.add_argument('--build', action='store_true', help='Build only missing known native executables offline')
    parser.add_argument('--profile', type=Path, default=Path(os.environ.get('CONTINUING_SYSTEM_PROFILE', DEFAULT_PROFILE)))
    parser.add_argument('--worker', type=Path, default=Path(os.environ.get('CONTINUING_SYSTEM_WORKER', DEFAULT_WORKER)))
    args = parser.parse_args()
    before = inspect(args.profile.resolve(), args.worker.resolve())
    if args.build:
        builds = build_missing(before)
        result = inspect(args.profile.resolve(), args.worker.resolve()) if builds else before
        result['builds'] = builds
        result['valid_executables_rebuilt'] = 0
    else:
        result = before
    print(json.dumps(result, indent=2))
    return 0 if result['ready'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
