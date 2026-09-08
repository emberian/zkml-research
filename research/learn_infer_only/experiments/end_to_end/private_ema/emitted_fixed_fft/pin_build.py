#!/usr/bin/env python3
"""Capture compiler-resolved features, local source excerpts and build identity."""
from pathlib import Path
import datetime
import difflib
import json
import os
import subprocess
import tarfile
from prepare import HERE, PRIOR, metadata, sha


def main():
    events = [json.loads(line) for line in (HERE / "build.events.jsonl").read_text().splitlines()]
    assert events[-1] == {"reason": "build-finished", "success": True}
    tfhe = next(e for e in events if e.get("reason") == "compiler-artifact" and e["target"]["name"] == "tfhe")
    assert sorted(tfhe["features"]) == ["boolean", "experimental-force_fft_algo_dif4"]
    assert (HERE / "Cargo.lock").read_bytes() == (PRIOR / "Cargo.lock").read_bytes()
    identical = {name: (HERE / name).read_bytes() == (PRIOR / name).read_bytes()
                 for name in ["src/lib.rs", "src/ciphertext.rs"]}
    assert all(identical.values())
    commands = [["rustc", "-Vv"], ["cargo", "-V"], ["uname", "-a"],
                ["sysctl", "-n", "machdep.cpu.brand_string"], ["git", "rev-parse", "HEAD"]]
    captures = []
    for argv in commands:
        p = subprocess.run(argv, cwd=HERE, capture_output=True, text=True)
        captures.append({"argv":argv,"returncode":p.returncode,"stdout":p.stdout,"stderr":p.stderr})
    registry = Path('/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
    cache = Path('/Users/ember/.cargo/registry/cache/index.crates.io-1949cf8c6b5b557f')
    sources = [
        ('tfhe-1.6.3','Cargo.toml',[(75,98)]),
        ('tfhe-1.6.3','src/core_crypto/fft_impl/fft64/math/fft/mod.rs',[(75,120),(161,197)]),
        ('tfhe-1.6.3','src/boolean/engine/bootstrapping.rs',[(94,163),(445,475)]),
        ('tfhe-fft-0.10.1','src/unordered.rs',[(495,540),(654,682),(768,779)]),
    ]
    records, excerpts = [], []
    for crate, relative, ranges in sources:
        path = registry / crate / relative
        raw = path.read_bytes()
        with tarfile.open(cache / f'{crate}.crate') as archive:
            same = archive.extractfile(f'{crate}/{relative}').read() == raw
        assert same
        record = metadata(path); record.update({'archive_bytes_match':same,'read_ranges':ranges})
        records.append(record)
        lines = raw.decode().splitlines()
        for start,end in ranges:
            excerpts.append(f'[SOURCE implementation] {path}:{start}-{end}\n' + '\n'.join(f'{i+1}: {lines[i]}' for i in range(start-1,end)) + '\n')
    (HERE / 'feature_source.txt').write_text('\n'.join(excerpts))
    search_argv = ['rg','-n','setup_custom_fft_plan','src']
    search = subprocess.run(search_argv,cwd=HERE,capture_output=True,text=True)
    assert search.returncode == 1 and search.stdout == ''
    difference = ''.join(difflib.unified_diff((PRIOR/'src/main.rs').read_text().splitlines(True),
                                               (HERE/'src/main.rs').read_text().splitlines(True),
                                               fromfile='emitted_runtime/src/main.rs',tofile='emitted_fixed_fft/src/main.rs'))
    (HERE / 'main_source.diff').write_text(difference)
    value = {'claim':'EXECUTED','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
             'build_command':['cargo','build','--release','--locked','--offline','-j','1','--message-format=json-render-diagnostics'],
             'test_command':['cargo','test','--locked','--offline','-j','1'],
             'compiler_tfhe_artifact':tfhe,'commands':captures,
             'build_environment':{k:os.environ.get(k) for k in ['RUSTFLAGS','CARGO_ENCODED_RUSTFLAGS','RUSTC_WRAPPER','CARGO_BUILD_TARGET','CARGO_TARGET_DIR']},
             'runtime_environment_contract':{'RAYON_NUM_THREADS':'1'},
             'same_cargo_lock_as_prior':True,'identical_source_files':identical,
             'binary':metadata(HERE/'target/release/resident-emitted-bool-runtime'),
             'source_evidence':records,
             'custom_plan_setter_search':{'argv':search_argv,'cwd':str(HERE),'returncode':search.returncode,'stdout':search.stdout,'stderr':search.stderr},
             'earlier_emitted_freeze':metadata(PRIOR/'freeze.json'),
             'no_past_failure_cause_inferred':True}
    assert value['earlier_emitted_freeze']['sha256'] == 'b45a38b01838b9b44bf8f8bcdd67c7e908bec0850b0f627d051d3a5e75785b3b'
    (HERE / 'build_pins.json').write_text(json.dumps(value,indent=2)+'\n')
    print(json.dumps({'claim':'EXECUTED','tfhe_compiled_features':tfhe['features'],'identical_generic_sources':identical,
                      'binary_sha256':value['binary']['sha256'],'source_archives_match':True}))


if __name__ == '__main__':
    main()
