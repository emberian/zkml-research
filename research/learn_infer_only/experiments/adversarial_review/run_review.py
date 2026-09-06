#!/usr/bin/env python3
"""Independent bounded review runner; writes only this lane's directory."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import os
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parents[1]
ROOT = RESEARCH.parents[1]


def run(name, command, cwd, env=None, inputs=()):
    started = datetime.now(timezone.utc).isoformat()
    tick = time.monotonic()
    hashes_before = {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    try:
        p = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True, timeout=180)
        data = dict(exit_code=p.returncode, stdout=p.stdout, stderr=p.stderr)
    except subprocess.TimeoutExpired as e:
        data = dict(exit_code='timeout', stdout=str(e.stdout), stderr=str(e.stderr))
    record = dict(command=command, cwd=str(cwd), started_utc=started,
                  elapsed_seconds=time.monotonic()-tick,
                  inputs=hashes_before,
                  inputs_unchanged=all(hashes_before[str(p)]==hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs), **data)
    version = 1+len(list(HERE.glob(f'{name}_*.json')))
    (HERE / f'{name}_{version:02}.json').write_text(json.dumps(record, indent=2)+'\n')
    print(f'{name}: {data["exit_code"]}', flush=True)
    if data['stdout']: print(data['stdout'], flush=True)
    if data['stderr']: print(data['stderr'], flush=True)
    return data['exit_code'] == 0


def lean_environment(build):
    environment = json.loads((RESEARCH / 'experiments/results/environment.json').read_text())
    base = next(x['stdout'].strip() for x in environment['checks']
                if x['command'] == ['lake', 'env', 'printenv', 'LEAN_PATH'])
    overlay = build/'Assurance'
    overlay.mkdir(parents=True, exist_ok=True)
    for artifact in (RESEARCH/'formal/build/Assurance').iterdir():
        target = overlay/artifact.name
        if not target.exists() and not target.is_symlink():
            target.symlink_to(artifact)
    compiler = build/'Compiler'
    compiler.mkdir(parents=True, exist_ok=True)
    for artifact in Path('/Users/ember/dev/minidregg/.lake/build/lib/lean/Compiler').iterdir():
        target = compiler/artifact.name
        if not target.exists() and not target.is_symlink():
            target.symlink_to(artifact)
    return dict(os.environ, LEAN_PATH=str(build)+':'+str(RESEARCH/'formal/build')+':'+base)


def main():
    tasks = sys.argv[1:] or ['python', 'lean']
    locations = {
        'lean': (HERE/'RestoreSeamWitness.lean', 'lean_seam'),
        'durable_unsafe': (HERE/'snapshots/b174ddb157caa8cc/Assurance/ResidentDurableIntegration.lean', 'lean_durable_unsafe'),
        'durable': (RESEARCH/'formal/durable_integration/Assurance/ResidentDurableIntegration.lean', 'lean_durable'),
        'collision': (RESEARCH/'formal/durable_integration/Assurance/ResidentDurableCollision.lean', 'lean_collision'),
        'adaptive': (RESEARCH/'formal/randomness_composition/Assurance/ResidentAdaptiveContext.lean', 'lean_adaptive'),
        'multi_receipt': (RESEARCH/'formal/randomness_composition/Assurance/ResidentMultiReceiptSchedule.lean', 'lean_multi_receipt'),
        'bfv_reference': (RESEARCH/'formal/bfv_lift_refinement/Compiler/BFVScaleLiftRefinement.lean', 'lean_bfv_reference'),
        'bfv_engine': (RESEARCH/'formal/bfv_lift_refinement/engine_refinement/Compiler/FheRnsScaleDecomposition.lean', 'lean_bfv_engine'),
        'bfv_envelope': (HERE/'BFVEnvelopeSeamWitness.lean', 'lean_bfv_envelope'),
        'ema_certificate': (RESEARCH/'formal/durable_integration/Compiler/ResidentEmaCertificate.lean', 'lean_ema_certificate'),
        'ema_cell': (RESEARCH/'formal/durable_integration/Assurance/ResidentEmaCell.lean', 'lean_ema_cell'),
        'ema_release': (RESEARCH/'formal/durable_integration/Assurance/ResidentEmaRelease.lean', 'lean_ema_release'),
        'ema_witness': (RESEARCH/'formal/durable_integration/Assurance/ResidentEmaWitness.lean', 'lean_ema_witness'),
        'ema_census': (HERE/'EmaDescriptorReview.lean', 'lean_ema_census'),
        'ema_zero_oracle': (HERE/'EmaZeroOracleReview.lean', 'lean_ema_zero_oracle'),
        'release_packet': (HERE/'ReleasePacketSeamWitness.lean', 'lean_release_packet'),
    }
    good = True
    for task in tasks:
        if task == 'he_results':
            source = HERE/'he_results_review.py'
            inputs = [source, RESEARCH/'experiments/he_closure_costs/estimator/summary.json']
            good &= run('he_results_parse', [sys.executable, str(source)], ROOT, inputs=inputs)
            if not good: return 1
            continue
        if task == 'bfv_check':
            source = RESEARCH/'experiments/bfv_lift_refinement/check_engine.py'
            inputs = [source, source.parent/'fhe_scaler_model.py', source.parent/'engine_probe/full-coefficients.jsonl.gz']
            good &= run('bfv_retained', [sys.executable, str(source)], ROOT,
                        env=dict(os.environ, PYTHONDONTWRITEBYTECODE='1'), inputs=inputs)
            if not good: return 1
            continue
        if task == 'python':
            for script in ['writer_recovery.py', 'restore_release.py']:
                path = RESEARCH/'experiments'/script
                good &= run(path.stem, [sys.executable,str(path)], ROOT, inputs=[path])
            continue
        source, label = locations[task]
        build = HERE/('build_unsafe' if task in ['durable_unsafe', 'release_packet'] else 'build')
        env = lean_environment(build)
        module_dir = source.parent.name if source.parent.name in ['Compiler', 'Theory', 'Assurance'] else 'Assurance'
        output = build/module_dir/(source.stem+'.olean')
        if output.is_symlink():
            raise RuntimeError(f'Refusing to write through dependency symlink: {output}')
        inputs = [source, RESEARCH/'formal/Assurance/ResidentReleaseContext.lean']
        if task in ['collision','release_packet']:
            inputs += [(HERE/'snapshots/b174ddb157caa8cc/Assurance/ResidentDurableIntegration.lean') if task=='release_packet' else (RESEARCH/'formal/durable_integration/Assurance/ResidentDurableIntegration.lean'),
                       build/'Assurance/ResidentDurableIntegration.olean']
        if task == 'multi_receipt':
            inputs += [RESEARCH/'formal/randomness_composition/Assurance/ResidentAdaptiveContext.lean',
                       build/'Assurance/ResidentAdaptiveContext.olean']
        if task in ['bfv_engine', 'bfv_envelope']:
            inputs += [RESEARCH/'formal/bfv_lift_refinement/Compiler/BFVScaleLiftRefinement.lean',
                       build/'Compiler/BFVScaleLiftRefinement.olean']
        if task == 'bfv_envelope':
            inputs += [RESEARCH/'formal/bfv_lift_refinement/engine_refinement/Compiler/FheRnsScaleDecomposition.lean',
                       build/'Compiler/FheRnsScaleDecomposition.olean']
        if task in ['ema_cell', 'ema_release', 'ema_witness', 'ema_census', 'ema_zero_oracle']:
            inputs += [RESEARCH/'formal/durable_integration/Compiler/ResidentEmaCertificate.lean',
                       build/'Compiler/ResidentEmaCertificate.olean']
        if task in ['ema_cell', 'ema_release', 'ema_witness', 'ema_zero_oracle']:
            inputs += [RESEARCH/'formal/durable_integration/Assurance/ResidentDurableIntegration.lean',
                       build/'Assurance/ResidentDurableIntegration.olean']
        if task in ['ema_release', 'ema_witness', 'ema_zero_oracle']:
            inputs += [RESEARCH/'formal/durable_integration/Assurance/ResidentEmaCell.lean',
                       build/'Assurance/ResidentEmaCell.olean']
        if task in ['ema_witness', 'ema_zero_oracle']:
            inputs += [RESEARCH/'formal/durable_integration/Assurance/ResidentEmaRelease.lean',
                       build/'Assurance/ResidentEmaRelease.olean']
        if task == 'ema_zero_oracle':
            inputs += [RESEARCH/'formal/durable_integration/Assurance/ResidentEmaWitness.lean',
                       build/'Assurance/ResidentEmaWitness.olean']
        good &= run(label, ['/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean',
                            '-o',str(output),str(source)],
                    HERE if source.parent == HERE else source.parents[1], env, inputs)
        if not good: return 1
    return 0 if good else 1

if __name__ == '__main__':
    raise SystemExit(main())
