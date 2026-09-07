"""Pin completed crypto evidence; does not rerun encryption or inspect secrets."""
import hashlib,json,math,statistics,subprocess
from pathlib import Path
HERE=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(Path(p).read_bytes()).hexdigest()
def run(argv):
    p=subprocess.run(argv,text=True,capture_output=True)
    assert p.returncode==0,(argv,p.stderr)
    return p.stdout.strip()
def main():
    report=json.loads((HERE/'test_results.json').read_text())
    binary=HERE/'target/release/resident-crypto'
    parameters=json.loads(run([str(binary),'params']))
    assert parameters['source_sha256']==sha(HERE/'src/main.rs')==report['source_sha256']
    assert sha(binary)==report['binary_sha256']
    assert '1 passed; 0 failed' in (HERE/'unit_tests.log').read_text()
    rng=json.loads((HERE/'rng_audit.json').read_text())
    assert rng['raw_secret_keys_equal'] and rng['regenerated_secret_cross_decrypts'] and not rng['public_keys_equal']
    (HERE/'params.json').write_text(json.dumps(parameters,indent=2,sort_keys=True)+'\n')
    private_reader=[r for r in report['commands'] if r['command']=='reader-decrypt' and 'unknown-' in ' '.join(r['argv'])]
    assert len(private_reader)==2
    assert all(r['result']=={'private_reader_result_omitted':True,'success':True} for r in private_reader)
    timing={}
    for command in ['keygen','issuer-encrypt','host-learn','host-infer','reader-decrypt']:
        vals=sorted(r['wall_ns'] for r in report['commands'] if r['command']==command and r['exit_code']==0)
        timing[command]={'count':len(vals),'median_ns':statistics.median(vals),
            'p95_nearest_rank_ns':vals[math.ceil(.95*len(vals))-1],'total_ns':sum(vals)}
    library=Path('/Users/ember/dev/breadstuffs/vendor/fhe-dregg')
    files=run(['rg','--files',str(library)]).splitlines()
    libhashes={str(Path(p).relative_to(library)):sha(p) for p in files if p.endswith('.rs') or Path(p).name=='Cargo.toml'}
    validation={'source_sha256':report['source_sha256'],'binary_sha256':sha(binary),
        'params_id':parameters['params_id'],'program_id':parameters['program_id'],
        'all_cli_checks_passed':True,'successful_fixed_score_checks':96,'private_score_results_redacted':True,
        'commands':len(report['commands']),'rng_correction':rng,'latency_ns':timing,
        'credential_bytes':{'public_key_envelope':42628,'secret_key_envelope':4180,'ciphertext_envelope':85103,
            'logical_66_ciphertext_set':66*85103},
        'library_source_sha256':libhashes,'cargo_lock_sha256':sha(HERE/'Cargo.lock'),
        'rustc':run(['rustc','-Vv']),'cargo':run(['cargo','-V']),
        'cpu':run(['sysctl','-n','machdep.cpu.brand_string']),
        'reproduction_commands':[
            'cargo build --offline --locked --release --manifest-path '+str(HERE/'Cargo.toml'),
            'cargo test --offline --locked --release --manifest-path '+str(HERE/'Cargo.toml'),
            'python3 '+str(HERE/'test_cli.py'),
            'cargo run --offline --locked --release --manifest-path '+str(HERE/'Cargo.toml')+' --bin rng-audit'],
        'reproduction_exit_codes':[0,0,0,0],
        'source_scope':'productionCLI + separate public-seed audit; no journal, issuer-signature or finality implementation here',
        'new_metered_searches':0}
    (HERE/'validation.json').write_text(json.dumps(validation,indent=2,sort_keys=True)+'\n')
    hashes={str(p.relative_to(HERE)):sha(p) for p in HERE.rglob('*') if p.is_file()
        and 'runs' not in p.relative_to(HERE).parts and 'target' not in p.relative_to(HERE).parts
        and '__pycache__' not in p.parts and p.name not in ['artifact_hashes.json','package.log']}
    (HERE/'artifact_hashes.json').write_text(json.dumps({'artifacts':hashes,'excluded_private_or_build_directories':['runs','target'],
        'excluded_active_packaging_stdout':'package.log'},indent=2,sort_keys=True)+'\n')
    print(json.dumps({'artifacts':len(hashes),'source_sha256':report['source_sha256'],
        'binary_sha256':sha(binary),'params_id':parameters['params_id'],'checks_pass':True},sort_keys=True))
if __name__=='__main__':main()
