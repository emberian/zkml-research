#!/usr/bin/env python3
"""Read public source only; never load a key, ciphertext, binary, or run a build."""
import hashlib
import json
import re
import subprocess
import tarfile
import tomllib
from datetime import datetime, timezone
from pathlib import Path

HERE = Path(__file__).resolve().parent
PRIVATE_EMA = HERE.parent
REGISTRY = Path('/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f')
CACHE = REGISTRY.parent.parent / 'cache' / REGISTRY.name
RANGES = {
    'tfhe-1.6.3/src/lib.rs': [(75, 87)],
    'tfhe-1.6.3/src/boolean/ciphertext/mod.rs': [(10, 20)],
    'tfhe-1.6.3/src/boolean/parameters/params.rs': [(45, 62)],
    'tfhe-1.6.3/src/boolean/engine/mod.rs': [(558, 593), (710, 747)],
    'tfhe-1.6.3/src/boolean/engine/bootstrapping.rs': [(43, 65), (94, 163), (191, 200), (224, 275), (349, 401), (449, 486), (488, 535), (578, 610)],
    'tfhe-1.6.3/src/core_crypto/algorithms/lwe_programmable_bootstrapping/mod.rs': [(1, 15)],
    'tfhe-1.6.3/src/core_crypto/algorithms/lwe_programmable_bootstrapping/karatsuba_pbs.rs': [(16, 210), (237, 310), (314, 415)],
    'tfhe-1.6.3/src/core_crypto/algorithms/polynomial_algorithms.rs': [(306, 339), (1066, 1088), (1106, 1206)],
    'tfhe-1.6.3/src/core_crypto/algorithms/modulus_switch.rs': [(1, 24)],
    'tfhe-1.6.3/src/core_crypto/fft_impl/common.rs': [(10, 23)],
    'tfhe-1.6.3/src/core_crypto/commons/math/decomposition/decomposer.rs': [(86, 96), (156, 185)],
    'tfhe-1.6.3/src/core_crypto/fft_impl/fft64/math/decomposition.rs': [(1, 100)],
    'tfhe-1.6.3/src/core_crypto/algorithms/lwe_bootstrap_key_conversion.rs': [(290, 365)],
    'tfhe-1.6.3/src/core_crypto/algorithms/lwe_programmable_bootstrapping/ntt64_pbs.rs': [(439, 550)],
    'tfhe-1.6.3/src/core_crypto/algorithms/lwe_programmable_bootstrapping/ntt64_bnf_pbs.rs': [(31, 44), (86, 103), (428, 537), (559, 582), (628, 672)],
    'tfhe-1.6.3/src/core_crypto/commons/math/ntt/ntt64.rs': [(34, 54), (112, 244)],
    'tfhe-1.6.3/src/core_crypto/algorithms/test/lwe_programmable_bootstrapping.rs': [(710, 730), (1004, 1016), (1158, 1173), (1248, 1253)],
    'tfhe-1.6.3/src/core_crypto/fft_impl/fft64/math/fft/mod.rs': [(161, 197)],
    'tfhe-ntt-0.7.1/README.md': [(1, 25), (54, 61)],
    'tfhe-ntt-0.7.1/src/lib.rs': [(447, 458)],
    'tfhe-ntt-0.7.1/src/native32.rs': [(6, 18), (334, 431)],
    'tfhe-ntt-0.7.1/src/prime32.rs': [(660, 685)],
    'tfhe-ntt-0.7.1/src/prime64.rs': [(715, 724), (761, 812), (883, 977)],
    'tfhe-fft-0.10.1/src/fft_simd.rs': [(219, 315)],
    'tfhe-fft-0.10.1/src/unordered.rs': [(295, 347), (654, 682)],
}

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    out = HERE / 'results'
    out.mkdir(exist_ok=True)
    lock_path = PRIVATE_EMA / 'emitted_fixed_fft/Cargo.lock'
    lock = tomllib.loads(lock_path.read_text())
    packages = {f"{p['name']}-{p['version']}": p for p in lock['package']}
    archives = {}
    files = []
    excerpts = []
    for name, ranges in RANGES.items():
        path = REGISTRY / name
        data = path.read_bytes()
        crate = name.split('/')[0]
        archive = CACHE / f'{crate}.crate'
        if crate not in archives:
            archive_sha = sha(archive.read_bytes())
            assert archive_sha == packages[crate]['checksum']
            archives[crate] = {'path': str(archive), 'sha256': archive_sha, 'matches_frozen_cargo_lock': True}
        with tarfile.open(archive) as tar:
            archive_data = tar.extractfile(name).read()
        assert data == archive_data
        files.append({'path': str(path), 'sha256': sha(data), 'bytes': len(data), 'archive_bytes_match': True, 'ranges': ranges})
        excerpts.append('\nSOURCE ' + str(path) + '\nSHA256 ' + sha(data))
        lines = data.decode().splitlines()
        for a, b in ranges:
            excerpts.extend(f'{n}: {lines[n-1]}' for n in range(a, min(b, len(lines)) + 1))
    pins_path = PRIVATE_EMA / 'emitted_fixed_fft/build_pins.json'
    fixed_pins = json.loads(pins_path.read_text())
    for pin in fixed_pins['source_evidence']:
        assert sha(Path(pin['path']).read_bytes()) == pin['sha256']
    public_paths = [lock_path, pins_path,
        PRIVATE_EMA / 'emitted_fixed_fft/Cargo.toml',
        PRIVATE_EMA / 'emitted_fixed_fft/SOURCE_AUDIT.md',
        PRIVATE_EMA / 'emitted_fixed_fft/CONTRACT.md',
        PRIVATE_EMA / 'emitted_fixed_fft/src/lib.rs',
        PRIVATE_EMA / 'emitted_fixed_fft/src/main.rs',
        PRIVATE_EMA / 'emitted_fixed_fft/src/ciphertext.rs',
        PRIVATE_EMA / 'emitted_fixed_fft/src/plan_observation.rs',
        PRIVATE_EMA / 'src/bin/setup.rs',
        PRIVATE_EMA / 'REPORT.md']
    public_pins = [{'path': str(p), 'sha256': sha(p.read_bytes())} for p in public_paths]
    commands = [
        ['rg', '-n', 'Ntt|ntt|karatsuba|deterministic', str(REGISTRY / 'tfhe-1.6.3/src/boolean')],
        ['rg', '-n', '-i', 'deterministic|reproducib|cross.platform|cross.arch', str(REGISTRY / 'tfhe-fft-0.10.1/README.md'), str(REGISTRY / 'tfhe-fft-0.10.1/src')],
        ['rg', '--files', str(REGISTRY / 'tfhe-1.6.3')],
        ['rg', '-n', 'native32', str(REGISTRY / 'tfhe-1.6.3/src')],
    ]
    searches = []
    for command in commands:
        p = subprocess.run(command, text=True, capture_output=True)
        output = p.stdout
        if command[1] == '--files':
            output = '\n'.join(x for x in output.splitlines() if '/benches/' in x)
        searches.append({'command': command, 'exit': p.returncode, 'stdout': output, 'stderr': p.stderr, 'postfilter': 'path contains /benches/' if command[1] == '--files' else None})
    text = (REGISTRY / 'tfhe-ntt-0.7.1/src/lib.rs').read_text().split('pub(crate) mod primes32 {', 1)[1]
    primes = [int(re.search(rf'pub const P{i}: u32 = (0b[01_]+);', text)[1].replace('_', ''), 2) for i in range(3)]
    product = primes[0] * primes[1] * primes[2]
    n, k, levels, N = 837, 2, 2, 1024
    polys = n * levels * (k + 1)**2
    leaves = 3**4
    derivation = {
        'scope': 'Pure integer arithmetic from source parameter and loop dimensions; no library execution or timing.',
        'parameters_source': 'tfhe-1.6.3/src/boolean/parameters/params.rs:46',
        'n': n, 'k': k, 'levels': levels, 'N': N,
        'standard_u32_bsk_coefficients': polys * N,
        'standard_u32_bsk_coefficient_bytes_excluding_ksk_metadata': polys * N * 4,
        'worst_case_nonzero_modswitched_mask_count': n,
        'polynomial_products_per_pbs_upper_bound': polys,
        'karatsuba_schoolbook_leaves_per_product': leaves,
        'u32_schoolbook_multiply_accumulates_per_product': leaves * 64**2,
        'u32_schoolbook_multiply_accumulates_per_pbs_upper_bound': polys * leaves * 64**2,
        'crt_primes': primes, 'crt_product': product,
        'single_unsigned_u32_negacyclic_product_coefficient_absolute_bound': N * (2**32 - 1)**2,
        'single_product_bound_strictly_below_half_crt_product': 2 * N * (2**32 - 1)**2 < product,
        'six_product_sum_bound_strictly_below_half_crt_product': 2 * 6 * N * (2**32 - 1)**2 < product,
    }
    assert derivation['single_product_bound_strictly_below_half_crt_product']
    assert derivation['six_product_sum_bound_strictly_below_half_crt_product']
    # Repeat public source reads after the audit, without touching runtime artifacts.
    assert all(sha(Path(p['path']).read_bytes()) == p['sha256'] for p in public_pins)
    report = {'scope': 'source-only audit; no key/ciphertext reads, crypto, library build, binary invocation, or frozen-file mutation',
        'created_utc': datetime.now(timezone.utc).isoformat(),
        'command': 'python3 ' + str(Path(__file__).resolve()),
        'archives': archives, 'source_files': files, 'existing_four_source_pins_match': True,
        'public_source_pins_before_and_after_equal': public_pins,
        'searches': searches, 'derivation': derivation}
    (out / 'source_excerpts.txt').write_text('\n'.join(excerpts) + '\n')
    (out / 'source_audit.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps({'source_files': len(files), 'archives': len(archives), 'frozen_source_pins_match': True, 'public_source_files_unchanged': len(public_pins), 'derivation': derivation}, indent=2))

if __name__ == '__main__':
    main()
