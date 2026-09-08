#!/usr/bin/env python3
"""Prove the complete captured rescale in six sequential, fresh-verified chunks.

Usage: run.py CASE NEW_RUN
The approved emitter computes an untrusted witness; the pinned Lean-generated
relation and shared proof backend decide acceptance. No private input is read.
"""
import datetime
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def save(path, obj):
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(obj, indent=2) + '\n')
    tmp.replace(path)


def check_pins(pins):
    for path, digest in pins.items():
        if sha(path) != digest:
            raise RuntimeError('frozen input changed: ' + path)


def command(run, label, argv, timeout, env):
    record = {'argv': [str(x) for x in argv], 'started_utc': now(),
              'cwd': str(ROOT), 'timeout_seconds': timeout}
    started = time.monotonic()
    with (run / (label + '.stdout')).open('xb') as out, (run / (label + '.stderr')).open('xb') as err:
        p = subprocess.Popen(record['argv'], cwd=ROOT, env=env,
                             stdout=out, stderr=err, start_new_session=True)
        record['pid'] = p.pid
        save(run / (label + '.command.json'), record)
        timed_out = False
        while True:
            pid, status, usage = os.wait4(p.pid, os.WNOHANG)
            if pid:
                break
            if time.monotonic() - started > timeout:
                timed_out = True
                os.killpg(p.pid, signal.SIGKILL)
                _, status, usage = os.wait4(p.pid, 0)
                break
            time.sleep(0.05)
        p.returncode = os.waitstatus_to_exitcode(status)
    record.update(returncode=p.returncode, timed_out=timed_out,
                  finished_utc=now(), elapsed_seconds=time.monotonic() - started,
                  user_seconds=usage.ru_utime, system_seconds=usage.ru_stime,
                  max_rss_bytes=usage.ru_maxrss if sys.platform == 'darwin' else usage.ru_maxrss * 1024)
    save(run / (label + '.command.json'), record)
    if p.returncode or timed_out:
        raise RuntimeError('step failed; no retry: ' + label)
    return record


def main():
    if len(sys.argv) != 3:
        raise SystemExit(__doc__)
    case, run = (Path(x).resolve() for x in sys.argv[1:])
    config_path = ROOT / 'PIPELINE.json'
    config = json.loads(config_path.read_text())
    check_pins(config['source_pins'])
    op = json.loads((case / 'operation.json').read_text())
    assert op['chunk_count'] == 6 and op['chunk_rows'] == 4096
    assert op['total_positions'] == 24576 and op['exact_coverage_no_padding']
    assert op['public_tuple_width'] == 88 and op['output_residues'] == 98304
    assert len(op['chunks']) == 6
    case_pins = {str(p): sha(p) for p in case.rglob('*') if p.is_file()}
    # Check coverage against actual exported rows, not just operation metadata.
    for i, chunk in enumerate(op['chunks']):
        assert chunk['chunk'] == i and chunk['rows'] == 4096
        assert chunk['first_global_row'] == i * 4096
        assert chunk['end_global_row_exclusive'] == (i + 1) * 4096
        path = case / chunk['public_rows']
        assert sha(path) == chunk['sha256']
        rows = json.loads(path.read_text())
        assert len(rows) == 4096
        assert all(len(r) == 88 and r[0] == i * 4096 + j for j, r in enumerate(rows))
    run.mkdir()
    work = ROOT / 'work' / run.name
    work.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, RAYON_NUM_THREADS=str(config['rayon_threads']))
    frozen = {'schema': 'whole-rescale-six-chunks-v1', 'started_utc': now(),
              'case': str(case), 'pipeline_sha256': sha(config_path),
              'source_pins': config['source_pins'], 'case_pins': case_pins,
              'rayon_threads': config['rayon_threads'], 'work': str(work)}
    save(run / 'inputs.json', frozen)
    started = time.monotonic()
    results = []
    try:
        for chunk in op['chunks']:
            i = chunk['chunk']
            prefix = f'chunk{i:03}'
            save(run / 'progress.json', {'phase': 'emit', 'chunk': i, 'completed': len(results), 'utc': now()})
            generated = work / prefix
            rows = case / chunk['public_rows']
            emit = command(run, prefix + '-emit', [config['emitter'], config['plan'], config['template'], rows, generated], 900, env)
            assert sha(generated / 'template_ir2.json') == config['template_sha256']
            trace = generated / 'trace.leu32'
            assert trace.stat().st_size == 4096 * 24575 * 4
            trace_sha = sha(trace)
            save(run / 'progress.json', {'phase': 'prove', 'chunk': i, 'completed': len(results), 'utc': now()})
            proof_dir = run / prefix
            prove = command(run, prefix + '-prove', [config['native'], 'prove', config['template'], case, i, trace, proof_dir], 1800, env)
            proof = json.loads((proof_dir / 'proof.json').read_text())
            save(run / 'progress.json', {'phase': 'fresh_verify', 'chunk': i, 'completed': len(results), 'utc': now()})
            verify = command(run, prefix + '-verify', [config['native'], 'verify', config['template'], case, i, proof_dir / 'proof.bin'], 300, env)
            verified = json.loads((run / (prefix + '-verify.stdout')).read_text())
            assert proof['verified'] and verified['verified']
            for record in (proof, verified):
                assert record['chunk'] == i and record['rows'] == 4096
                assert record['first_global_row'] == i * 4096
                assert record['end_global_row_exclusive'] == (i + 1) * 4096
                assert record['public_rows_sha256'] == chunk['sha256']
                assert record['source_trace_sha256'] == op['source_trace_sha256']
                assert record['output_ciphertext_sha256'] == op['output_ciphertext_sha256']
                assert record['proof_sha256'] == sha(proof_dir / 'proof.bin')
            assert proof['template_sha256'] == config['template_sha256']
            assert proof['trace_width'] == 24575
            compressed = trace.with_suffix('.leu32.zst')
            packing = command(run, prefix + '-compress', [config['zstd'], '-T1', '-3', '--no-progress', str(trace), '-o', str(compressed)], 300, env)
            # The successful compressor leaves the original intact until its
            # exact hash/length and transport identity have been retained.
            transport = {'path': str(compressed), 'bytes': compressed.stat().st_size,
                         'sha256': sha(compressed), 'raw_bytes': trace.stat().st_size,
                         'raw_sha256': trace_sha, 'tracked_in_git': False}
            trace.unlink()
            result = {'chunk': i, 'proof': proof, 'fresh_verification': verified,
                      'costs': {'emit': emit, 'prove': prove, 'verify': verify, 'compress': packing},
                      'witness_transport': transport}
            save(proof_dir / 'result.json', result)
            results.append(result)
            save(run / 'progress.json', {'phase': 'chunk_complete', 'chunk': i, 'completed': len(results), 'utc': now()})
            print(json.dumps({'chunk': i, 'verified': True, 'proof_bytes': proof['proof_bytes'], 'prove_seconds': proof['prove_ns'] / 1e9}), flush=True)
        check_pins(config['source_pins'])
        check_pins(case_pins)
        assert sha(config_path) == frozen['pipeline_sha256']
        result = {'schema': 'whole-rescale-result-v1', 'verified': True,
                  'chunks': results, 'total_positions': 24576, 'output_residues': 98304,
                  'exact_coverage_no_padding': True, 'source_trace_sha256': op['source_trace_sha256'],
                  'output_ciphertext_sha256': op['output_ciphertext_sha256'],
                  'template_sha256': config['template_sha256'],
                  'pipeline_sha256': frozen['pipeline_sha256'],
                  'proof_bytes': sum(x['proof']['proof_bytes'] for x in results),
                  'elapsed_seconds': time.monotonic() - started, 'finished_utc': now(),
                  'private_files_read': 0,
                  'scope': 'Complete captured rescale only; extension, convolution, decoding/NTT, ciphertext provenance and whole ct-times-ct remain outside the arithmetic proof.'}
        save(run / 'result.json', result)
        save(run / 'progress.json', {'phase': 'complete', 'completed': 6, 'utc': now()})
    except BaseException as e:
        save(run / 'failure.json', {'error': repr(e), 'completed_chunks': len(results), 'utc': now(), 'retried': False})
        raise


if __name__ == '__main__':
    main()
