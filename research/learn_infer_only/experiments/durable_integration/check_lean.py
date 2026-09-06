#!/usr/bin/env python3
"""Compile lane modules in a private overlay; never output through a symlink."""
from pathlib import Path
import hashlib, json, os, subprocess, sys, time

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT / 'formal/durable_integration'
OUT = HERE / 'build'
RESULTS = ROOT / 'experiments/durable_integration/results'
COMP = Path('/Users/ember/dev/minidregg')
LEAN = Path('/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean')

def run(command, cwd, env=None):
    started = time.time()
    proc = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True)
    return dict(command=[str(x) for x in command], cwd=str(cwd),
                exit_code=proc.returncode, stdout=proc.stdout, stderr=proc.stderr,
                elapsed_seconds=time.time()-started)

def main():
    RESULTS.mkdir(parents=True, exist_ok=True)
    environment = json.loads((ROOT/'experiments/results/environment.json').read_text())
    paths = next(x['stdout'].strip() for x in environment['checks']
                 if x['command'] == ['lake', 'env', 'printenv', 'LEAN_PATH'])
    overlay = OUT/'Assurance'
    overlay.mkdir(parents=True, exist_ok=True)
    for artifact in (COMP/'.lake/build/lib/lean/Assurance').iterdir():
        dest = overlay/artifact.name
        if not dest.exists() and not dest.is_symlink(): dest.symlink_to(artifact)
    env = dict(os.environ, LEAN_PATH=str(OUT)+':'+paths)
    files = [ROOT/'formal/Assurance/ResidentReleaseContext.lean',
             HERE/'Assurance/ResidentDurableIntegration.lean',
             HERE/'Assurance/ResidentDurableCollision.lean']
    for source in files:
        target = overlay/(source.stem+'.olean')
        if target.is_symlink():
            raise RuntimeError(f'refusing output through symlink: {target}')
        digest = hashlib.sha256(source.read_bytes()).hexdigest()
        old_checks = sorted(RESULTS.glob(f'lean_{source.stem}_*.json'))
        if source == files[0] and old_checks and target.exists():
            old = json.loads(old_checks[-1].read_text())
            if (old['exit_code'] == 0 and old['source_sha256'] == digest
                    and old.get('olean_sha256', hashlib.sha256(target.read_bytes()).hexdigest())
                    == hashlib.sha256(target.read_bytes()).hexdigest()):
                print(source.stem, 'verified cached dependency', flush=True)
                continue
        rec = run([LEAN, '-o', target, source], source.parent.parent, env)
        rec.update(source_sha256=digest,
                   lean_path=env['LEAN_PATH'])
        if rec['exit_code'] == 0:
            rec['olean_sha256'] = hashlib.sha256(target.read_bytes()).hexdigest()
        n = len(list(RESULTS.glob(f'lean_{source.stem}_*.json')))+1
        (RESULTS/f'lean_{source.stem}_{n:02d}.json').write_text(json.dumps(rec, indent=2)+'\n')
        print(source.stem, rec['exit_code'], rec['stdout'], rec['stderr'], flush=True)
        if rec['exit_code']: return rec['exit_code']
    return 0

if __name__ == '__main__': raise SystemExit(main())
