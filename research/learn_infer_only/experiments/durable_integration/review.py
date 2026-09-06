#!/usr/bin/env python3
"""Stage the lane patch and umbrella and retain read-only integration checks."""
from pathlib import Path
import difflib, hashlib, json, os, subprocess, sys, time

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT/'formal/durable_integration'
RESULTS = ROOT/'experiments/durable_integration/results'
COMP = Path('/Users/ember/dev/minidregg')
LEAN = Path('/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean')

def run(command, cwd, env=None):
    t=time.time()
    p=subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True)
    return dict(command=[str(x) for x in command], cwd=str(cwd), exit_code=p.returncode,
                stdout=p.stdout, stderr=p.stderr, elapsed_seconds=time.time()-t)

def main():
    sources=[HERE/'Assurance/ResidentDurableIntegration.lean',
             HERE/'Assurance/ResidentDurableCollision.lean']
    digests={}
    for source in sources:
        lean_checks=sorted(RESULTS.glob(f'lean_{source.stem}_*.json'))
        checked=json.loads(lean_checks[-1].read_text())
        digest=hashlib.sha256(source.read_bytes()).hexdigest()
        if checked['exit_code'] != 0 or checked['source_sha256'] != digest:
            raise RuntimeError('latest Lean success does not match current source: '+str(source))
        digests[source.stem]=digest
    original=(COMP/'Assurance.lean').read_text()
    staged=original+'\nimport Assurance.ResidentDurableIntegration\nimport Assurance.ResidentDurableCollision\n'
    umbrella=HERE/'Assurance.lean'
    if umbrella.is_symlink(): raise RuntimeError('refusing symlink write')
    umbrella.write_text(staged)
    patch=''
    for source in sources:
        patch+=''.join(difflib.unified_diff([], source.read_text().splitlines(True),
                        fromfile='/dev/null', tofile='b/Assurance/'+source.name))
    patch+=''.join(difflib.unified_diff(original.splitlines(True), staged.splitlines(True),
                                      fromfile='a/Assurance.lean', tofile='b/Assurance.lean'))
    patchpath=HERE/'minidregg-durable-integration.patch'
    patchpath.write_text(patch)
    env=dict(os.environ, LEAN_PATH=checked['lean_path'])
    commands=[([LEAN, umbrella], HERE, env),
              (['bash', COMP/'scripts/check-import-boundary.sh'], COMP, None),
              (['git', 'apply', '--check', patchpath], COMP, None),
              ([sys.executable, Path(__file__).with_name('inspect_sources.py')], ROOT, None),
              (['git', 'rev-parse', 'HEAD'], COMP, None),
              (['git', 'status', '--short'], COMP, None)]
    records=[]
    for cmd,cwd,e in commands:
        rec=run(cmd,cwd,e); records.append(rec)
        print(' '.join(str(x) for x in cmd), rec['exit_code'], rec['stdout'], rec['stderr'], flush=True)
    deps=['Theory/CellState.lean', 'Theory/CellStateWitness.lean',
          'Kernel/DurableDataIntent.lean', 'Kernel/GuardedDurableCommit.lean',
          'Kernel/DurableCommitProtocol.lean', 'Kernel/ReplicatedSettlementFinality.lean',
          'Kernel/FinalityGate.lean']
    result=dict(module_sha256=digests, patch_sha256=hashlib.sha256(patchpath.read_bytes()).hexdigest(),
                prerequisite='formal/minidregg-resident-release.patch supplies ResidentReleaseContext',
                checks=records, source_hashes={x:hashlib.sha256((COMP/x).read_bytes()).hexdigest() for x in deps})
    history=sorted(RESULTS.glob('review_*.json'))
    if not history and (RESULTS/'review.json').exists():
        (RESULTS/'review_01.json').write_bytes((RESULTS/'review.json').read_bytes())
        history=[RESULTS/'review_01.json']
    (RESULTS/f'review_{len(history)+1:02d}.json').write_text(json.dumps(result,indent=2)+'\n')
    (RESULTS/'review.json').write_text(json.dumps(result,indent=2)+'\n')
    return int(any(r['exit_code'] for r in records))

if __name__ == '__main__': raise SystemExit(main())
