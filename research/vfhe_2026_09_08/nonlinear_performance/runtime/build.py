#!/usr/bin/env python3
"""Build the four exact copied public readers against the isolated grouped backend."""
from pathlib import Path
import json
import os
import sys
from common import ROOT, command, save, sha, check_pins, now


def main():
    if len(sys.argv) != 2:
        raise SystemExit('build.py NEW_BUILD_RECORD_DIR')
    out = Path(sys.argv[1]).resolve()
    out.mkdir()
    native = ROOT / 'native'
    copies = json.loads((native / 'SOURCE_COPIES.json').read_text())
    check_pins({r['copy']: r['sha256'] for r in copies if r['copy'].endswith('.rs')})
    env = dict(os.environ, CARGO_TARGET_DIR=str(native / 'target'), CARGO_BUILD_JOBS='4', RAYON_NUM_THREADS='4')
    bins = {'infer': 'vfhe-complete-kernel-infer', 'square': 'vfhe-full-bfv-multiply',
            'rescale': 'vfhe-whole-rescale-runtime', 'update': 'vfhe-live-nonlinear-update'}
    result = {'started_utc': now(), 'builds': []}
    for name, binary in bins.items():
        manifest = native / name / 'Cargo.toml'
        cost = command(out, name, ['/Users/ember/.cargo/bin/cargo', 'build', '--release', '--offline', '--manifest-path', manifest], 1800, env)
        executable = native / 'target/release' / binary
        result['builds'].append({'name': name, 'cost': cost, 'binary': str(executable),
                                 'binary_sha256': sha(executable), 'manifest_sha256': sha(manifest),
                                 'lock_sha256': sha(native / name / 'Cargo.lock'),
                                 'source_sha256': sha(native / name / 'src/main.rs')})
        save(out / 'progress.json', result)
    check_pins({r['copy']: r['sha256'] for r in copies if r['copy'].endswith('.rs')})
    result['finished_utc'] = now()
    save(out / 'BUILD.json', result)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
