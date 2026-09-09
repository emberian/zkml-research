#!/usr/bin/env python3
"""Produce the complete initial-product and ten switching/reduction proofs."""
import hashlib
import json
import os
from pathlib import Path
import sys
import time
from common import ROOT, check_pins, command, now, save, sha


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    if len(argv) != 2:
        raise SystemExit('usage: prove.py CASE NEW_RUN')
    case, out = (Path(x).resolve() for x in argv)
    config_path = ROOT / 'PIPELINE.json'
    config = json.loads(config_path.read_text())
    check_pins(config['source_pins'])
    op = json.loads((case / 'operation.json').read_text())
    assert len(op['chunks']) == 88 and op['public_arity'] == 97 and op['stages'] == 11
    assert op['binding']['linear_plan_sha256'] == config['linear_plan_sha256']
    case_pins = {str(p): sha(p) for p in case.rglob('*') if p.is_file()}
    for i, chunk in enumerate(op['chunks']):
        assert chunk['index'] == i and chunk['stage'] == i // 8 and chunk['prime_index'] == (i % 8) // 2
        assert chunk['rows'] == 4096 and chunk['first_row'] == i * 4096 and chunk['end_row_exclusive'] == (i + 1) * 4096
        path = case / chunk['path']
        assert sha(path) == chunk['sha256']
        rows = json.loads(path.read_text())
        assert len(rows) == 4096 and all(len(r) == 97 and r[0] == i * 4096 + j for j, r in enumerate(rows))
    out.mkdir()
    work = ROOT / 'work' / hashlib.sha256(str(out).encode()).hexdigest()[:16]
    work.mkdir(parents=True, exist_ok=False)
    frozen = {'case_pins': case_pins, 'source_pins': config['source_pins'], 'config_sha256': sha(config_path), 'started_utc': now()}
    save(out / 'inputs.json', frozen)
    env = dict(os.environ, RAYON_NUM_THREADS='4')
    started = time.monotonic()
    results = []
    try:
        for chunk in op['chunks']:
            i = chunk['index']
            profile = config['profiles'][(i % 8) // 2]
            name = f'chunk{i:03}'
            generated = work / name
            save(out / 'progress.json', {'phase': 'emit', 'index': i, 'stage': i // 8, 'completed': len(results), 'utc': now()})
            emit = command(out, name + '-emit', [profile['executor'], profile['plan'], profile['template'], case / chunk['path'], generated], 900, env)
            assert sha(generated / 'template_ir2.json') == profile['template_sha256']
            trace = generated / 'trace.leu32'
            assert trace.stat().st_size == 4096 * profile['width'] * 4
            raw_sha, raw_bytes = sha(trace), trace.stat().st_size
            proof_dir = out / name
            save(out / 'progress.json', {'phase': 'prove', 'index': i, 'stage': i // 8, 'completed': len(results), 'utc': now()})
            prove = command(out, name + '-prove', [config['native'], 'prove', config['linear_plan'], i, profile['template'], case, trace, proof_dir], 1800, env)
            proof = json.loads((proof_dir / 'proof.json').read_text())
            assert proof['verified'] and proof['index'] == i and proof['stage'] == i // 8
            assert proof['prime_index'] == (i % 8) // 2 and proof['rows'] == 4096 and proof['arity'] == 97
            assert proof['first_row'] == i * 4096 and proof['end_row_exclusive'] == (i + 1) * 4096
            assert proof['binding'] == op['binding'] and proof['width'] == profile['width']
            assert proof['public_rows_sha256'] == chunk['sha256'] and proof['template_sha256'] == profile['template_sha256']
            assert proof['proof_sha256'] == sha(proof_dir / 'proof.bin')
            compressed = trace.with_suffix('.leu32.zst')
            packing = command(out, name + '-compress', [config['zstd'], '-T1', '-3', '--no-progress', trace, '-o', compressed], 300, env)
            transport = {'path': str(compressed), 'bytes': compressed.stat().st_size, 'sha256': sha(compressed), 'raw_sha256': raw_sha, 'raw_bytes': raw_bytes}
            trace.unlink()
            result = {'index': i, 'proof': proof, 'costs': {'emit': emit, 'prove': prove, 'compress': packing}, 'witness_transport': transport}
            save(proof_dir / 'result.json', result)
            results.append(result)
            print(json.dumps({'chunk': i, 'stage': i // 8, 'proof_self_verified': True}), flush=True)
        check_pins(config['source_pins'])
        check_pins(case_pins)
        assert sha(config_path) == frozen['config_sha256']
        save(out / 'result.json', {'phase_complete': True, 'complete_infer_verified': False, 'chunks': results, 'binding': op['binding'], 'elapsed_seconds': time.monotonic() - started, 'finished_utc': now()})
        save(out / 'progress.json', {'phase': 'complete', 'completed': 88, 'utc': now()})
    except BaseException as e:
        save(out / 'failure.json', {'error': repr(e), 'completed': len(results), 'retried': False, 'utc': now()})
        raise


if __name__ == '__main__':
    main()
