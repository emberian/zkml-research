#!/usr/bin/env python3
"""Freeze this declared backend and exactly five static public control tuples."""
from pathlib import Path
import datetime
import json
import subprocess
from prepare import HERE, FORMAL, metadata, sha


def main():
    inputs = json.loads((HERE / 'inputs.json').read_text())
    pins = json.loads((HERE / 'build_pins.json').read_text())
    assert len(inputs['cases']) == 5 and inputs['host_pairs'] == 5
    assert pins['compiler_tfhe_artifact']['features'] == ['boolean','experimental-force_fft_algo_dif4']
    binary = HERE / 'target/release/resident-emitted-bool-runtime'
    assert sha(binary) == pins['binary']['sha256']
    assert '8 passed; 0 failed' in (HERE / 'test.log').read_text()
    validation = {}
    for op in ['learn','infer']:
        argv = [str(binary),'validate',str(FORMAL / f'artifacts/{op}.json')]
        p = subprocess.run(argv,capture_output=True,text=True)
        validation[op] = {'argv':argv,'returncode':p.returncode,'stdout':p.stdout,'stderr':p.stderr}
        assert p.returncode == 0 and json.loads(p.stdout)['valid'] is True
    (HERE / 'validation.json').write_text(json.dumps(validation,indent=2)+'\n')
    named = ['Cargo.toml','Cargo.lock','CONTRACT.md','build_pins.json','build.events.jsonl','build.log',
             'test.log','features.txt','feature_source.txt','main_source.diff','prepare.py','pin_build.py',
             'freeze.py','run_controls.py','inputs.json','validation.json','target/release/resident-emitted-bool-runtime']
    paths = {str(HERE / name) for name in named}
    paths.update(str(p) for p in (HERE/'src').glob('*.rs'))
    paths.add(str(FORMAL / 'SCHEMA.md'))
    for case in inputs['cases']:
        for entry in case['read_inputs']:
            assert metadata(entry['path']) == entry
            paths.add(entry['path'])
    for entry in inputs['source_records']:
        assert metadata(entry['path']) == entry
        paths.add(entry['path'])
    document = {'schema':'fixed-fft-public-control-freeze-v1','claim':'EXECUTED',
                'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
                'files':[metadata(p) for p in sorted(paths)],'host_pairs':5,
                'private_reader_invocations':0,'old_failed_output_files_opened':False,
                'runtime_environment':{'RAYON_NUM_THREADS':'1'},
                'stop_at_first_failure_without_retry':True,
                'long_workload_authorized_by_this_freeze':False}
    with (HERE / 'freeze.json').open('x') as stream:
        stream.write(json.dumps(document,indent=2)+'\n')
    print(json.dumps({'claim':'EXECUTED','freeze_sha256':sha(HERE/'freeze.json'),'public_files':len(paths),'host_pairs':5}))


if __name__ == '__main__':
    main()
