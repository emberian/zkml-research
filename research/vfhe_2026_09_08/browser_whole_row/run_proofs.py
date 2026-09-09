#!/usr/bin/env python3
"""Re-prove three fixed public cases with the source-preserving whole-row gate.

No key generation, encryption, text encoding, decryption, new AIR, or old-fixture
mutation. Existing Lean-produced traces are read from their pinned public runs.
This one-shot recorded run refuses to overwrite its outputs.
"""
from pathlib import Path
import datetime, hashlib, json, os, shutil, subprocess, sys, time

ROOT = Path(__file__).resolve().parent
LANES = ROOT.parent
REPO = LANES.parent.parent
WHOLE = REPO / 'research/proof_frontier/2026-09-08/ir2_verifier_bridge/air_pcs_join/whole_domain'
FAST = LANES / 'proved_journal/fast_live_successor'

def sha(path):
    h = hashlib.sha256()
    with path.open('rb') as f:
        for block in iter(lambda: f.read(1024 * 1024), b''):
            h.update(block)
    return h.hexdigest()

def pin(path):
    assert '.private' not in path.parts and 'private' not in path.parts
    return {'path': str(path.resolve()), 'bytes': path.stat().st_size, 'sha256': sha(path)}

def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('x') as f:
        json.dump(value, f, indent=2)
        f.write('\n')

def run(label, argv, env=None):
    out = ROOT / 'results' / (label + '.stdout')
    err = ROOT / 'results' / (label + '.stderr')
    start = time.monotonic()
    record = {'argv': list(map(str, argv)), 'cwd': str(ROOT),
              'started_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'RAYON_NUM_THREADS': (env or os.environ).get('RAYON_NUM_THREADS')}
    with out.open('x') as stdout, err.open('x') as stderr:
        result = subprocess.run(record['argv'], cwd=ROOT, env=env, stdout=stdout, stderr=stderr)
    record.update(returncode=result.returncode, elapsed_seconds=time.monotonic()-start,
                  finished_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),
                  stdout=pin(out), stderr=pin(err))
    save(ROOT / 'results' / (label + '.command.json'), record)
    print(json.dumps({'step': label, 'returncode': result.returncode,
                      'elapsed_seconds': record['elapsed_seconds']}), flush=True)
    if result.returncode:
        raise RuntimeError(label + ' failed; retained stderr: ' + str(err))
    return record

def main():
    (ROOT / 'results').mkdir(exist_ok=False)
    (ROOT / 'sources').mkdir(exist_ok=False)
    copied = {}
    for source, relative in [
        (WHOLE / 'repair_template.py', 'repair_template.py'),
        (WHOLE / 'proposal/Compiler/Ir2WholeRow.lean', 'Compiler/Ir2WholeRow.lean'),
        (WHOLE / 'proposal/Compiler/BfvQueryWholeRows.lean', 'Compiler/BfvQueryWholeRows.lean'),
        (WHOLE / 'proposal/EmitBfvQuery.lean', 'EmitBfvQueryWholeRow.lean'),
        (LANES / 'arithmetic_coverage/EmitBfvExpiry.lean', 'EmitBfvExpiryOriginal.lean'),
        (LANES / 'arithmetic_coverage/Compiler/BfvExpiryLayout.lean', 'Compiler/BfvExpiryLayout.lean'),
        (LANES / 'arithmetic_coverage/artifact_pins.json', 'expiry-artifact-pins.json'),
        (LANES / 'query_native_emitter/SOURCE_PINS.json', 'query-witness-source-pins.json'),
        (LANES / 'query_runtime/src/main.rs', 'query_runtime.rs'),
        (LANES / 'proved_operation/src/main.rs', 'update_runtime.rs'),
        (LANES / 'proved_operation/src/update.rs', 'update_public_reader.rs'),
    ]:
        target = ROOT / 'sources' / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        copied[relative] = pin(source)
    save(ROOT / 'sources/ORIGINS.json', copied)
    original_templates = {
        'expiry': LANES / 'arithmetic_coverage/artifacts_expiry/template_ir2.json',
        'query': LANES / 'query_arithmetic/artifacts/template_ir2.json'}
    expected_hashes = {
        'expiry': '1afc2b3a120f59fdd79d273c6d32887373c5718225cb6e94b82a7231010c3aa7',
        'query': 'f42c5efcaa994656b0c9ef2d1270aa2d6eb7dae0e5ba85938d23dbb3dc46c10d'}
    templates = {}
    for kind, source in original_templates.items():
        assert sha(source) == expected_hashes[kind]
        target = ROOT / 'templates' / kind / 'template_ir2.json'
        run('migrate-' + kind, [sys.executable, ROOT / 'sources/repair_template.py', source, target])
        templates[kind] = target
    # Query migration is independently identical to the already executed Lean
    # whole-domain emitter. The expiry uses its existing row-local arithmetic
    # and the same strict polynomial-preserving serializer migration.
    assert templates['query'].read_bytes() == (WHOLE / 'generated_query/template_ir2.json').read_bytes()
    cases = [{
        'id': 'learner-expiry', 'kind': 'expiry',
        'case': LANES / 'proved_operation/results/learner_expiry001',
        'trace': LANES / 'arithmetic_coverage/artifacts_expiry/trace.leu32',
        'rows': LANES / 'proved_operation/results/learner_expiry001/public_ntt_rows.json',
        'binary': LANES / 'proved_operation/target/release/vfhe-proved-operation',
        'mode': 'prove-update', 'files': ['acc.ct', 'fresh.ct', 'old.ct', 'out.ct', 'source_event.json'],
    }]
    for i in range(2):
        cases.append({
            'id': 'class' + str(i), 'kind': 'query',
            'case': FAST / f'results/fast001/class{i}/case',
            'trace': FAST / f'runtime/fast001/queries/new-two-class-query/proof{i}/generated/trace.leu32',
            'rows': FAST / f'results/fast001/class{i}/case/public_rows.json',
            'binary': LANES / 'query_runtime/target/release/vfhe-query-runtime',
            'mode': 'prove', 'files': ['acc.ct', 'query.json', 'out.ct'],
        })
    # Only explicitly enumerated public files are inspected; no directory walk
    # enters runtime state or private setup material.
    origin_cases = []
    for case in cases:
        item = {k: v for k, v in case.items() if k not in ['files']}
        for key in ['case']:
            item[key] = str(item[key])
        for key in ['trace', 'rows', 'binary']:
            item[key] = pin(item[key])
        item['public_case_files'] = [pin(case['case'] / name) for name in case['files']]
        item['template'] = pin(templates[case['kind']])
        origin_cases.append(item)
    save(ROOT / 'SOURCE_PINS.json', {
        'classification': 'SOURCE', 'cases': origin_cases,
        'original_templates': {k: pin(v) for k, v in original_templates.items()},
        'generated_query_origin': pin(WHOLE / 'generated_query/template_ir2.json'),
        'scope': 'Fixed public cases and source-derived traces; all-row wrapping changes, polynomial bodies unchanged.'})
    env = dict(os.environ, RAYON_NUM_THREADS='4')
    for case in cases:
        output = ROOT / 'proofs' / case['id']
        output.parent.mkdir(exist_ok=True)
        run('prove-' + case['id'], [case['binary'], case['mode'], templates[case['kind']],
            case['case'], case['trace'], output], env)
    print(json.dumps({'status': 'PASS', 'new_proofs': 3, 'native_self_checks': 3}), flush=True)

if __name__ == '__main__':
    main()
