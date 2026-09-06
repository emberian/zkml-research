#!/usr/bin/env python3
"""Pinned source/size audit and exact standalone GMP decoder falsifier.

This does not build or run the RLWE encryption/sampler: those need x86 AVX2.
Only the unmodified round_extract_gmp function is extracted and compiled with the
already installed native GMP. No cryptographic code is silently ported.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def function(text, name):
    start = text.index('void ' + name + '(')
    # Ignore braces in comments/string literals while retaining source offsets.
    masked = re.sub(r'/\*.*?\*/|//[^\n]*|"(?:\\.|[^"\\])*"',
                    lambda m: ''.join('\n' if c == '\n' else ' ' for c in m[0]),
                    text, flags=re.S)
    brace = masked.index('{', start)
    depth = 1
    end = brace + 1
    while depth:
        depth += (masked[end] == '{') - (masked[end] == '}')
        end += 1
    return text[start:end]


def line_of(text, fragment):
    return text[:text.index(fragment)].count('\n') + 1


def parameter_records():
    source = HERE / 'vendor/IPFE-RLWE/src/params.h'
    text = source.read_text()
    branches = re.split(r'#(?:el)?if SEC_LEVEL==[012]', text)[1:]
    records = []
    for level, branch in enumerate(branches):
        def macro(name):
            return int(re.search(r'#define ' + name + r' (\d+)', branch)[1])
        def string(name):
            return int(re.search(name + r'\[\]\s*=\s*"(\d+)"', branch)[1])
        n, d, t = macro('SIFE_N'), macro('SIFE_L'), macro('SIFE_NMODULI')
        q, K, delta = string('SIFE_Q_str'), string('SIFE_P_str'), string('SIFE_SCALE_M_str')
        moduli = [int(x) for x in re.search(r'SIFE_MOD_Q_I.*?=\s*\{([^}]+)', branch)[1].split(',')]
        product = 1
        for value in moduli:
            product *= value
        assert product == q and delta == q // K
        ct_bytes = (d + 1) * t * n * 4
        records.append({
            'level': level, 'n': n, 'd': d, 'crt_moduli': moduli,
            'q': q, 'q_bits': q.bit_length(), 'K': K, 'delta_floor': delta,
            'q_mod_K': q % K, 'Bx': macro('SIFE_B_x'), 'By': macro('SIFE_B_y'),
            'public_key_bytes': ct_bytes, 'ciphertext_bytes': ct_bytes,
            'master_key_bytes': d * t * n * 4, 'function_key_bytes': t * n * 4,
            'state_plus_window8_bytes': 9 * ct_bytes,
            'fresh_enc_gaussian_coefficients': (d + 2) * n,
            'fresh_enc_forward_ntts': t, 'fresh_enc_inverse_ntts': (d + 1) * t,
            'fresh_enc_pointwise_modular_multiplies': (d + 1) * t * n,
            'additive_ciphertext_residue_additions': (d + 1) * t * n,
            'public_offset_additions': d * t * n,
            'keygen_residue_multiplies': d * t * n,
            'security_bits_verified': None,
        })
    return {'source': str(source), 'sha256': sha(source), 'sets': records}


def extract_and_run_rounding(repo):
    source = HERE / 'vendor' / repo / 'src/rlwe_sife.c'
    params = source.parent / 'params.h'
    text = source.read_text()
    exact = function(text, 'round_extract_gmp')
    # Default original params select the paper's medium set. 2023 also includes
    # seclevel.h relative to params.h, so use the absolute original parameter
    # header for both identical arithmetic algorithms. This scope is explicit.
    original_params = HERE / 'vendor/IPFE-RLWE/src/params.h'
    directory = HERE / 'build' / repo
    directory.mkdir(parents=True, exist_ok=True)
    harness = directory / 'rounding_extracted.c'
    upstream_license = (HERE / 'vendor/IPFE-RLWE/LICENSE').read_text()
    attribution = ('Exact round_extract_gmp excerpt from ' + repo + '/src/rlwe_sife.c.\n'
                   + 'Pinned source commit and hash: see results/rlwe_source_results.json.\n'
                   + 'See EXTRACTED_CODE_LICENSES.md for both upstream attributions.\n'
                   + ('Optimized2023 modifications have no separately recorded upstream license;\n'
                      + 'the following original MIT notice is retained for inherited code.\n'
                      if repo == 'IPFE-2023' else '') + '\n' + upstream_license)
    harness.write_text('/*\n' + attribution + '*/\n'
        + '#include <stdint.h>\n#include <stdio.h>\n#include <gmp.h>\n'
        + '#include "' + str(original_params) + '"\n' + exact + r'''
int main(void) {
  mpz_t a[SIFE_N], q, delta;
  mpz_init_set_str(q, SIFE_Q_str, 10);
  mpz_init_set_str(delta, SIFE_SCALE_M_str, 10);
  for (int i=0; i<SIFE_N; i++) { mpz_init(a[i]); mpz_sub_ui(a[i],q,1); }
  mpz_mul_ui(a[1],delta,5); mpz_add_ui(a[1],a[1],1);
  round_extract_gmp(a);
  gmp_printf("{\"phase_q_minus_one_decoded\": %Zd, \"positive_five_decoded\": %Zd}\n", a[0],a[1]);
  int ok=mpz_cmp_ui(a[0],50241)==0 && mpz_cmp_ui(a[1],5)==0;
  for(int i=0;i<SIFE_N;i++) mpz_clear(a[i]);
  mpz_clear(q); mpz_clear(delta); return ok?0:1;
}
''')
    executable = directory / 'rounding_extracted'
    command = ['clang', '-O1', '-Wno-unknown-pragmas', '-I/opt/homebrew/include',
               str(harness), '-L/opt/homebrew/lib', '-lgmp', '-o', str(executable)]
    build = subprocess.run(command, capture_output=True, text=True)
    (directory / 'build.log').write_text(build.stdout + build.stderr)
    build.check_returncode()
    run = subprocess.run([str(executable)], capture_output=True, text=True, check=True)
    (directory / 'run.log').write_text(run.stdout + run.stderr)
    outcome = json.loads(run.stdout)
    assert outcome == {'phase_q_minus_one_decoded': 50241, 'positive_five_decoded': 5}
    return {'source': str(source), 'source_sha256': sha(source),
            'function_start_line': line_of(text, 'void round_extract_gmp('),
            'parameter_scope': 'original medium params for both exact extracted functions; optimized OpenMP pragmas run serially',
            'harness_sha256': sha(harness), 'binary_sha256': sha(executable),
            'build_command': command, 'build_exit': build.returncode, 'run_exit': run.returncode,
            'result': outcome,
            'classification': 'EXECUTED exact decoder boundary falsifier for valid phase -1 mod q; not a sampled encryption or complete library run'}


def source_findings(repo):
    base = HERE / 'vendor' / repo
    path = base / 'src/rlwe_sife.c'
    text = path.read_text()
    setup = function(text, 'rlwe_sife_setup')
    encrypt = function(text, 'rlwe_sife_encrypt')
    assert '&state_secret' in setup and 'aes256ctr_init(&state_secret' not in setup
    assert '&state_s3' in encrypt and 'aes256ctr_init(&state_s3' not in encrypt
    return {'repository': repo,
            'commit': subprocess.check_output(['git', '-C', str(base), 'rev-parse', 'HEAD'], text=True).strip(),
            'files': {name: sha(base / 'src' / name) for name in
                      ('rlwe_sife.c', 'gauss.c', 'aes256ctr.c', 'params.h', 'Makefile')},
            'secret_sample_line': line_of(text, 'gaussian_sampler_S1(&state_secret'),
            'encryption_error_sample_line': line_of(text, 'gaussian_sampler_S3(&state_s3'),
            'uninitialized_contexts': ['setup.state_secret', 'encrypt.state_s3', 'encrypt_vec.state_s3'],
            'classification': 'SOURCE caller/callee inspection plus pinned syntactic assertions; no uninitialized-read runtime exploit',
            'shared_parallel_contexts': ['setup.state_secret', 'setup.state_error', 'encrypt.state_s2', 'encrypt.state_s3']
                                        if repo == 'IPFE-2023' else []}


def main():
    result = {
        'classification': 'Source/cost audit; complete cryptographic reproduction blocked by architecture',
        'full_library_build': {'command': 'make -C vendor/IPFE-RLWE/src', 'exit': 2,
                              'log_sha256': sha(HERE / 'rlwe_build.stdout.txt'),
                              'reason': 'unsupported -mavx2 for arm64-apple-darwin25.6.0',
                              'installation_path_stopped': True},
        'parameters': parameter_records(),
        'source_findings': [source_findings(name) for name in ('IPFE-RLWE', 'IPFE-2023')],
        'standalone_decoder_checks': [extract_and_run_rounding(name) for name in ('IPFE-RLWE', 'IPFE-2023')],
        'counts': {'additional_scry_queries': 0, 'additional_web_search_queries': 0,
                   'github_primary_pages_opened': 2, 'public_source_clones': 2},
        'not_executed': ['encryption', 'Gaussian sampling', 'ciphertext additive continuation',
                         'master-retention attack', 'parallel race or uninitialized-read exploit',
                         'security estimator', 'post-quantum reduction'],
    }
    (HERE / 'results/rlwe_source_results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
