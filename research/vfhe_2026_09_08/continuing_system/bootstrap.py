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
LINEAR = HERE / 'linear'
MATCHED = RESEARCH / 'matched_field'
PACKED_READER = HERE / 'packed/reader'
ENGINES = ('squared-compact', 'linear-compact', 'linear-matched', 'packed-matched', 'all')
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
    result['vfhe-complete-linear-infer'] = LINEAR / 'native/Cargo.toml'
    result['vfhe-matched-field'] = MATCHED / 'native/Cargo.toml'
    result['vfhe-packed-class-reader'] = PACKED_READER / 'native/Cargo.toml'
    return result


def build_recipe(path, source_pins=None):
    manifest = recipes().get(Path(path).name)
    if manifest is None:
        return None
    cargo = shutil.which('cargo') or str(Path.home() / '.cargo/bin/cargo')
    argv = [cargo, 'build', '--release', '--offline', '--locked', '--manifest-path',
            str(manifest), '--bin', Path(path).name]
    jobs = '1' if Path(path).name in ('vfhe-complete-linear-infer', 'vfhe-matched-field',
                                     'vfhe-packed-class-reader') else '4'
    return {'manifest': str(manifest), 'argv': argv,
            'source_pins': source_pins or {},
            'environment': {'CARGO_BUILD_JOBS': jobs, 'RAYON_NUM_THREADS': jobs,
                            'CARGO_TARGET_DIR': '<isolated-build-directory>/target'},
            'command': f'CARGO_BUILD_JOBS={jobs} RAYON_NUM_THREADS={jobs} '
                       'CARGO_TARGET_DIR=/absolute/new-build/target ' + shlex.join(argv),
            'source_available': manifest.is_file() and manifest.with_name('Cargo.lock').is_file()}


def inspect(profile, worker, engine='squared-compact', linear_profile=None,
            linear_worker=None, matched_profile=None, matched_worker=None,
            packed_reader_profile=None, packed_reader=None):
    result = {'ready': False, 'profile': str(profile), 'worker': str(worker),
              'engine': engine, 'dependency_profiles': [],
              'files_checked': 0, 'issues': [], 'executables': [],
              'runtime_artifacts': 'Retained JSON templates, witness plans and linear plan; Lean rebuild is not needed to launch.',
              'portability': 'The retained profiles, encoder configuration and Cargo path dependencies contain absolute workspace/cache paths. This is a retained-workspace bootstrap, not a portable fresh-clone installer.'}
    try:
        config = read(profile)
        if config.get('schema') != 'caller-selected-profiled-kernel-v1':
            raise ValueError('unsupported profile schema')
        expected = {}
        executable_paths = set()
        build_sources = {}

        def merge(pins):
            for path, digest in pins.items():
                path = str(Path(path).resolve())
                old = expected.setdefault(path, digest)
                if old != digest:
                    raise ValueError('conflicting pins for ' + path)

        def compact_profile(path, selected_worker, schema, role):
            value = read(path)
            if value['schema'] != schema:
                raise ValueError('unsupported ' + role + ' profile schema')
            if str(selected_worker) not in value['pins']:
                raise ValueError(role + ' worker is not pinned by its selected profile')
            result['dependency_profiles'].append({'role': role, 'path': str(path),
                                                  'sha256': sha(path)})
            return value

        config = compact_profile(profile, worker, 'caller-selected-profiled-kernel-v1', 'issuer/base')
        merge(config['pins'])
        executable_paths.update(str(Path(p).resolve()) for p in config['native'].values())
        executable_paths.add(str(Path(config['zstd']).resolve()))
        for profiles in config['profiles'].values():
            executable_paths.update(str(Path(p['executor']).resolve()) for p in profiles)
        issuer = read(HELPER_PINS)
        for entry in issuer['sources'] + issuer['model']:
            merge({entry['path']: entry['sha256']})
        executable_paths.update(str(Path(entry['path']).resolve()) for entry in issuer['sources']
                                if '/target/release/' in entry['path'])

        if engine != 'squared-compact':
            linear_profile = Path(linear_profile or LINEAR / 'PIPELINE.json').resolve()
            linear_worker = Path(linear_worker or LINEAR / 'caller.py').resolve()
            linear = read(linear_profile)
            if linear['schema'] != 'caller-selected-linear-profile-v1':
                raise ValueError('unsupported linear reader profile schema')
            native = str(Path(linear['native']['infer']).resolve())
            source = {str(Path(p).resolve()): digest for p, digest in linear['pins'].items()
                      if Path(p).is_relative_to(LINEAR / 'native') and
                      (Path(p).suffix in ('.rs', '.toml', '.lock'))}
            build_sources[native] = source
            executable_paths.add(native)
            if engine in ('linear-compact', 'all'):
                compact_profile(linear_profile, linear_worker, 'caller-selected-linear-profile-v1', 'linear/compact')
                merge(linear['pins'])
                for p in linear['profiles']['mac']:
                    executable_paths.add(str(Path(p['executor']).resolve()))
            else:
                # Matched mode uses only this native reader, not its MAC caller.
                result['dependency_profiles'].append({'role': 'signed linear reader',
                    'path': str(linear_profile), 'sha256': sha(linear_profile)})
                merge({native: linear['pins'][native],
                       linear['linear_plan']: linear['linear_plan_sha256']})
                merge(source)

        if engine in ('linear-matched', 'packed-matched', 'all'):
            matched_profile = Path(matched_profile or MATCHED / 'PIPELINE.json').resolve()
            matched_worker = Path(matched_worker or MATCHED / 'caller.py').resolve()
            matched = read(matched_profile)
            if matched['schema'] != 'matched-field-linear-profile-v1':
                raise ValueError('unsupported matched-field profile schema')
            if matched['linear_plan_sha256'] != linear['linear_plan_sha256']:
                raise ValueError('matched proof engine and signed reader disagree on linear plan')
            native = str(Path(matched['native']).resolve())
            merge({str(matched_worker): matched['caller_sha256'], native: matched['native_sha256'],
                   matched['linear_plan']: matched['linear_plan_sha256']})
            executable_paths.add(native)
            source_path = MATCHED / 'SOURCE.json'
            source_record = read(source_path)
            if source_record['binary']['sha256'] != matched['native_sha256']:
                raise ValueError('matched-field SOURCE.json and selected profile disagree on binary identity')
            source = {str(MATCHED / p): digest for p, digest in source_record['files'].items()}
            for dependency in source_record['local_dependencies'].values():
                source.update({str(Path(dependency['path']) / p): digest
                               for p, digest in dependency['files'].items()})
            merge(source)
            build_sources[native] = source
            result['dependency_profiles'].append({'role': 'linear/matched',
                'path': str(matched_profile), 'sha256': sha(matched_profile),
                'source_pins': str(source_path)})

        if engine in ('packed-matched', 'all'):
            packed_reader_profile = Path(packed_reader_profile or PACKED_READER / 'PROFILE.json').resolve()
            packed_reader = Path(packed_reader or PACKED_READER / 'native/target/release/vfhe-packed-class-reader').resolve()
            packed = read(packed_reader_profile)
            source_path = PACKED_READER / 'SOURCE.json'
            source_record = read(source_path)
            if (packed['schema'] != 'packed-class-reader-profile-v1'
                    or packed['native'] != str(packed_reader)
                    or packed['maximum_class_count'] != 8
                    or packed['maximum_class_sum_bound'] != 160000
                    or len(packed['pins']) != 5):
                raise ValueError('unsupported packed reader profile')
            if (sha(packed_reader_profile) != source_record['profile_sha256']
                    or packed['pins'][str(packed_reader)] != source_record['binary_sha256']
                    or packed['pins'][str(PACKED_READER / 'native/src/main.rs')] != source_record['source_sha256']):
                raise ValueError('packed reader profile and SOURCE.json disagree on retained identities')
            merge(packed['pins'])
            executable_paths.add(str(packed_reader))
            build_sources[str(packed_reader)] = {p: digest for p, digest in packed['pins'].items()
                                                 if p != str(packed_reader)}
            result['dependency_profiles'].append({'role': 'packed class-sum reader',
                'path': str(packed_reader_profile), 'sha256': sha(packed_reader_profile),
                'source_pins': str(source_path)})
    except (OSError, ValueError, KeyError) as exc:
        result['issues'].append({'kind': 'profile', 'error': str(exc),
                                 'action': 'Restore the selected profile, worker and source records; optional engines follow CONTINUING_SYSTEM_LINEAR_*, CONTINUING_SYSTEM_MATCHED_* and CONTINUING_PACKED_READER* paths.'})
        return result
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
            item['build'] = build_recipe(path, build_sources.get(text))
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
        source_issues = []
        for path, digest in recipe['source_pins'].items():
            try:
                if sha(path) != digest:
                    source_issues.append({'path': path, 'state': 'hash-mismatch'})
            except OSError:
                source_issues.append({'path': path, 'state': 'missing-or-unreadable'})
        if source_issues:
            record.update(error='Restore the pinned build sources before rebuilding this executable.',
                          source_issues=source_issues)
            builds.append(record)
            continue
        root = Path(tempfile.mkdtemp(prefix='continuing-bootstrap-'))
        env = dict(os.environ, CARGO_TARGET_DIR=str(root / 'target'),
                   CARGO_BUILD_JOBS=recipe['environment']['CARGO_BUILD_JOBS'],
                   RAYON_NUM_THREADS=recipe['environment']['RAYON_NUM_THREADS'])
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
    parser.add_argument('--engine', choices=ENGINES, default='squared-compact',
                        help='Engine prerequisites to include; default requires no optional engine')
    for name, root in (('linear', LINEAR), ('matched', MATCHED)):
        prefix = 'CONTINUING_SYSTEM_' + name.upper()
        parser.add_argument('--' + name + '-profile', type=Path,
                            default=Path(os.environ.get(prefix + '_PROFILE', root / 'PIPELINE.json')))
        parser.add_argument('--' + name + '-worker', type=Path,
                            default=Path(os.environ.get(prefix + '_WORKER', root / 'caller.py')))
    parser.add_argument('--packed-reader-profile', type=Path,
                        default=Path(os.environ.get('CONTINUING_PACKED_READER_PROFILE', PACKED_READER / 'PROFILE.json')))
    parser.add_argument('--packed-reader', type=Path,
                        default=Path(os.environ.get('CONTINUING_PACKED_READER', PACKED_READER / 'native/target/release/vfhe-packed-class-reader')))
    args = parser.parse_args()
    selection = (args.profile.resolve(), args.worker.resolve(), args.engine,
                 args.linear_profile.resolve(), args.linear_worker.resolve(),
                 args.matched_profile.resolve(), args.matched_worker.resolve(),
                 args.packed_reader_profile.resolve(), args.packed_reader.resolve())
    before = inspect(*selection)
    if args.build:
        builds = build_missing(before)
        result = inspect(*selection) if builds else before
        result['builds'] = builds
        result['valid_executables_rebuilt'] = 0
    else:
        result = before
    print(json.dumps(result, indent=2))
    return 0 if result['ready'] else 1


if __name__ == '__main__':
    raise SystemExit(main())
