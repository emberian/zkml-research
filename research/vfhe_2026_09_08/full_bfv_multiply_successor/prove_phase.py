#!/usr/bin/env python3
"""Emit and prove all complete chunks of one approved multiplication phase.

Usage: prove_phase.py extension|tensor CASE NEW_RUN
Fresh full-operation verification is performed by verify_whole.py after both
new phases exist; successful phase production alone is not a whole proof.
"""
import json
import hashlib
import os
from pathlib import Path
import sys
import time
from common import ROOT, check_pins, command, now, save, sha


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if len(argv) != 3 or argv[0] not in ('extension', 'tensor'):
        raise SystemExit(__doc__)
    kind = argv[0]
    case, run = (Path(x).resolve() for x in argv[1:])
    config_path = ROOT / (kind + '.json')
    config = json.loads(config_path.read_text())
    check_pins(config['source_pins'])
    case_pins = {str(p): sha(p) for p in case.rglob('*') if p.is_file()}
    operation = json.loads((case / 'operation.json').read_text())
    chunks = [x for x in operation['chunks'] if x['kind'] == kind]
    count, arity = (4, 84) if kind == 'extension' else (18, 56)
    assert len(chunks) == count
    for i, chunk in enumerate(chunks):
        assert chunk['index'] == i and chunk['rows'] == 4096 and chunk['arity'] == arity
        assert chunk['first_row'] == i * 4096 and chunk['end_row_exclusive'] == (i + 1) * 4096
        assert sha(case / chunk['path']) == chunk['sha256']
        rows = json.loads((case / chunk['path']).read_text())
        assert len(rows) == 4096
        assert all(len(r) == arity and r[0] == i * 4096 + j for j, r in enumerate(rows))
    run.mkdir()
    work = ROOT / 'work' / (kind + '-' + hashlib.sha256(str(run).encode()).hexdigest()[:16])
    work.mkdir(parents=True, exist_ok=False)
    frozen = {'kind': kind, 'case': str(case), 'config_sha256': sha(config_path),
              'source_pins': config['source_pins'], 'case_pins': case_pins, 'started_utc': now()}
    save(run / 'inputs.json', frozen)
    env = dict(os.environ, RAYON_NUM_THREADS='4')
    results = []
    started = time.monotonic()
    try:
        for chunk in chunks:
            i = chunk['index']
            profile = config['profiles'][0 if kind == 'extension' else i // 2]
            name = f'chunk{i:03}'
            generated = work / name
            save(run / 'progress.json', {'phase': 'emit', 'index': i, 'completed': len(results), 'utc': now()})
            emit = command(run, name + '-emit', [profile['emitter'], profile['plan'], profile['template'], case / chunk['path'], generated], 900, env)
            assert sha(generated / 'template_ir2.json') == profile['template_sha256']
            trace = generated / 'trace.leu32'
            assert trace.stat().st_size == 4096 * profile['width'] * 4
            raw_sha, raw_bytes = sha(trace), trace.stat().st_size
            save(run / 'progress.json', {'phase': 'prove', 'index': i, 'completed': len(results), 'utc': now()})
            out = run / name
            prove = command(run, name + '-prove', [config['native'], 'prove', kind, i, profile['template'], case, trace, out], 1800, env)
            proof = json.loads((out / 'proof.json').read_text())
            assert proof['verified'] and proof['kind'] == kind and proof['index'] == i
            assert proof['rows'] == 4096 and proof['width'] == profile['width'] and proof['arity'] == arity
            assert proof['first_row'] == i * 4096 and proof['end_row_exclusive'] == (i + 1) * 4096
            assert proof['binding'] == operation['binding']
            assert proof['public_rows_sha256'] == chunk['sha256']
            assert proof['template_sha256'] == profile['template_sha256']
            assert proof['proof_sha256'] == sha(out / 'proof.bin')
            compressed = trace.with_suffix('.leu32.zst')
            packing = command(run, name + '-compress', [config['zstd'], '-T1', '-3', '--no-progress', trace, '-o', compressed], 300, env)
            transport = {'path': str(compressed), 'sha256': sha(compressed), 'bytes': compressed.stat().st_size,
                         'raw_sha256': raw_sha, 'raw_bytes': raw_bytes, 'tracked_in_git': False}
            trace.unlink()
            result = {'index': i, 'proof': proof, 'costs': {'emit': emit, 'prove': prove, 'compress': packing}, 'witness_transport': transport}
            save(out / 'result.json', result)
            results.append(result)
            print(json.dumps({'kind': kind, 'index': i, 'proof_self_verified': True, 'proof_bytes': proof['proof_bytes']}), flush=True)
        check_pins(config['source_pins'])
        check_pins(case_pins)
        assert sha(config_path) == frozen['config_sha256']
        save(run / 'result.json', {'phase_complete': True, 'whole_operation_verified': False, 'kind': kind,
             'chunks': results, 'binding': operation['binding'], 'elapsed_seconds': time.monotonic() - started,
             'finished_utc': now(), 'config_sha256': frozen['config_sha256']})
        save(run / 'progress.json', {'phase': 'complete', 'completed': count, 'utc': now()})
    except BaseException as e:
        save(run / 'failure.json', {'error': repr(e), 'completed_chunks': len(results), 'utc': now(), 'retried': False})
        raise


if __name__ == '__main__':
    main()
