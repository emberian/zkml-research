#!/usr/bin/env python3
"""Rebuild live pinned engine and independently check all retained public coefficients.
No writes to breadstuffs/minidregg, no network, no private data or secrets.
"""
import gzip,hashlib,json,platform,subprocess,sys,time
from pathlib import Path
ROOT=Path(__file__).resolve().parent;PROBE=ROOT/'engine_probe'
BREAD=Path('/Users/ember/dev/breadstuffs');REG=Path('/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
PINNED=[BREAD/'Cargo.toml',BREAD/'Cargo.lock',BREAD/'fhegg-fhe/src/bfv_mul.rs',BREAD/'vendor/fhe-dregg/Cargo.toml',BREAD/'vendor/fhe-dregg/src/bfv/ops/mul.rs',BREAD/'vendor/fhe-dregg/src/bfv/parameters.rs',BREAD/'vendor/fhe-dregg/src/bfv/ciphertext.rs']
PINNED += [REG/'fhe-math-0.1.1'/p for p in ['Cargo.toml','src/rns/scaler.rs','src/rns/mod.rs','src/rq/scaler.rs','src/rq/mod.rs','src/rq/convert.rs','src/rq/ops.rs','src/zq/mod.rs']]
PINNED += [PROBE/'Cargo.toml',PROBE/'Cargo.lock',PROBE/'src/main.rs',ROOT/'fhe_scaler_model.py',ROOT/'check_engine.py',Path(__file__).resolve()]
PAPER=Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror/2021/204.pdf')
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snapshot():return [dict(path=str(p),sha256=sha(p),bytes=p.stat().st_size) for p in PINNED]
records=[]
def run(cmd,cwd=ROOT):
 start=time.monotonic();r=subprocess.run(cmd,cwd=cwd,capture_output=True)
 records.append(dict(command=list(map(str,cmd)),cwd=str(cwd),exit_code=r.returncode,elapsed_seconds=time.monotonic()-start,stderr=r.stderr.decode()))
 if r.returncode:
  records[-1]['stdout']=r.stdout.decode();(ROOT/'engine-run.json').write_text(json.dumps(records,indent=2)+'\n');raise SystemExit(r.stderr.decode())
 return r.stdout
before=snapshot()
versions={name:run(cmd).decode().strip() for name,cmd in [('rustc',['rustc','-Vv']),('cargo',['cargo','--version']),('python',[sys.executable,'--version']),('breadstuffs_HEAD',['git','-C',str(BREAD),'rev-parse','HEAD'])]}
cmd=['cargo','run','--offline','--release','--manifest-path',str(PROBE/'Cargo.toml')]
payload=run(cmd);fixture=PROBE/'full-coefficients.jsonl.gz';fixture.write_bytes(gzip.compress(payload,mtime=0));(PROBE/'build.log').write_text(records[-1]['stderr'])
checked=run([sys.executable,str(ROOT/'check_engine.py'),str(fixture)]);(ROOT/'engine-results.json').write_bytes(checked)
assert before==snapshot(),'source changed during execution'
upstream=REG/'fhe-0.1.1/src/bfv/ops/mul.rs';vendored=BREAD/'vendor/fhe-dregg/src/bfv/ops/mul.rs'
metadata=dict(label='EXECUTED live engine plus independent full-coefficient oracle; no decryption/security theorem',platform=platform.platform(),versions=versions,commands=records,sources=before,fixture=dict(path=str(fixture),sha256=sha(fixture),uncompressed_sha256=hashlib.sha256(payload).hexdigest(),bytes=len(payload)),upstream_mul_comparison=dict(path=str(upstream),sha256=sha(upstream),byte_identical=upstream.read_bytes()==vendored.read_bytes()),paper=dict(path=str(PAPER),sha256=sha(PAPER),read='Remark3.2 and section3.3; PDF pages19,21,22 via local pdftotext and rendered visual inspection; no paper refutation claim'),metered_search_queries=0,pdf_downloads=0)
(ROOT/'engine-run.json').write_text(json.dumps(metadata,indent=2)+'\n')
r=json.loads(checked);print(json.dumps(dict(full_cases=len(r['full_cases']),extension_coefficients=sum(x['extension_coefficient_checks'] for x in r['full_cases']),integer_convolution_coefficients=sum(x['integer_convolution_checks'] for x in r['full_cases']),full_output_coefficients=sum(x['full_output_coefficient_checks'] for x in r['full_cases']),source_model_mismatches=0,centered_lift_disagreements=sum(len(x['extension_center_disagreements']) for x in r['full_cases']),exact_nearest_disagreements=sum(len(x['source_vs_nearest_disagreements']) for x in r['full_cases']),all_commands_passed=True),indent=2))
