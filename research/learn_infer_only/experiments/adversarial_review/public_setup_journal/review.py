#!/usr/bin/env python3
"""Read-only identities and ordinary public-record arithmetic; never imports runtime."""
from pathlib import Path
from fractions import Fraction
import hashlib
import json

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[4]
AUTHOR = ROOT / 'research/learn_infer_only/experiments/private_construction/designated_span/public_coin_setup/journal'
REPORTS = AUTHOR / 'reports/normal_002'
EXPECTED_GENESIS = '0c81dbc0158b6703c3cc50b1ba4b6ed4e4ad07aed2e7acd8b9c98909deb9e8d3'
EXPECTED_CONTEXT = 'b060f1ae45ae1df7d3ed31b20364a884aebdc537b8ad27036b817f04cc9757c6'


def read(path):
    path = Path(path)
    # Prevent this reviewer from opening private/runtime role material even
    # if a retained record is changed. The runtime root is only used for the
    # explicit public allowlist below, before the author exports it.
    assert '.private' not in path.parts
    return path.read_bytes()


def sha(path):
    return hashlib.sha256(read(path)).hexdigest()


def parse(path):
    return json.loads(read(path))


def canonical(obj):
    return json.dumps(obj, sort_keys=True, separators=(',', ':'), ensure_ascii=True,
                      allow_nan=False).encode()


def digest(obj):
    return hashlib.sha256(canonical(obj)).hexdigest()


def main():
    source_inventory = parse(AUTHOR / 'SOURCE_PINS.json')
    pins = parse(REPORTS / 'execution_pins.json')
    source_checks = []
    for rel, entry in source_inventory['files'].items():
        copy, origin = AUTHOR / rel, Path(entry['origin'])
        assert sha(copy) == sha(origin) == entry['sha256'], rel
        assert len(read(copy)) == entry['bytes']
        source_checks.append({'copy': str(copy), 'origin': str(origin), 'sha256': entry['sha256']})
    for rel, expected in pins['source_files_sha256'].items():
        assert sha(AUTHOR / rel) == expected, rel
    environment = [pins['interpreter'], pins['native_dependency']]
    for row in environment:
        assert sha(row['path']) == row['sha256'], row['path']
    for path, expected in pins['signature_dependency']['files_sha256'].items():
        assert sha(path) == expected, path

    previous = AUTHOR / 'reports/normal_001'
    previous_pins = parse(previous / 'execution_pins.json')['source_files_sha256']
    changed = []
    for rel, expected in previous_pins.items():
        snapshot = previous / 'source_snapshot' / rel
        assert sha(snapshot) == expected, rel
        if read(snapshot) != read(AUTHOR / rel):
            changed.append(rel)
    assert changed == ['setup_join.py']
    old_setup = read(previous / 'source_snapshot/setup_join.py')
    assert old_setup.replace(b"'reader','registration','pending'", b"'reader','pending'") == read(AUTHOR / 'setup_join.py')
    previous_commands = [json.loads(line) for line in read(previous / 'commands.jsonl').splitlines()]
    previous_command_results = [(c['command'][1], c['exit_code']) for c in previous_commands]
    assert previous_command_results == [('params', 0), ('auth-init', 1)]

    launch = parse(REPORTS / 'launched.json')
    assert launch['execution_pins_sha256'] == sha(REPORTS / 'execution_pins.json')
    runtime = Path(launch['runtime'])
    assert runtime == AUTHOR / 'runtime/normal_002'
    exported = (REPORTS / 'public_complete.json').exists()
    public_root = REPORTS if exported else runtime
    allowlist = ['genesis.json', 'public_context.json', 'registry.json',
                 'public_transcript.json', 'public_setup_verification.json',
                 'context_validation.json', 'setup_report.json']
    public = {name: parse(public_root / name) for name in allowlist}
    hashes = {name: sha(public_root / name) for name in allowlist}
    g, ctx, reg, t, ver, validation, setup = (public[name] for name in allowlist)
    assert digest(g) == EXPECTED_GENESIS
    assert digest(ctx) == hashes['public_context.json'] == EXPECTED_CONTEXT
    assert g['context_id'] == g['key_id'] == g['public_key_sha256'] == EXPECTED_CONTEXT
    b = g['public_coin_setup']
    # Export currently carries announcements inside the pinned transcript;
    # before export the identical individual public files are available too.
    for name, expected in b['public_artifacts_sha256'].items():
        if name.startswith('announcements/'):
            index = int(Path(name).stem[1:])
            assert digest(t['announcements'][index]) == expected
            if not exported:
                assert sha(runtime / name) == expected
        else:
            assert name in allowlist and hashes[name] == expected, name
    assert b['setup_source_sha256'] == sha(AUTHOR / 'source/public_setup/setup.py')
    assert b['join_source_sha256'] == sha(AUTHOR / 'setup_join.py')
    assert b['dependency_inventory_sha256'] == sha(AUTHOR / 'SOURCE_PINS.json')
    assert t['setup_source_sha256'] == b['setup_source_sha256']
    assert t['crypto_sources'] == g['crypto_sources']
    assert t['native_dependency'] == g['native_dependency']
    assert t['registry_sha256'] == digest(reg) == hashes['registry.json']
    assert t['context_id'] == ver['context_id'] == EXPECTED_CONTEXT
    assert ver['complete_context_byte_match'] is True
    assert ver['transcript_sha256'] == digest(t) == hashes['public_transcript.json']
    assert g['context_validation_sha256'] == hashes['context_validation.json']
    assert validation['validated'] is True and validation['context_id'] == EXPECTED_CONTEXT
    assert validation['source_sha256'] == g['crypto_sources']
    assert setup['genesis_sha256'] == EXPECTED_GENESIS
    assert setup['context_id'] == EXPECTED_CONTEXT
    assert setup['scalar_master_generated'] is False
    assert setup['scalar_projection_delivery_generated'] is False

    rows = parse(AUTHOR / 'source/crypto/rows.json')
    assert len(rows) == 16 and all(len(row) == 577 for row in rows)
    assert rows == ctx['rows'] and digest(rows) == t['rows_sha256']
    # Independent rational elimination, separate from author's integer Bareiss
    # and modular completion. No group arithmetic or crypto module is imported.
    matrix = [[Fraction(x) for x in row[:16]] for row in rows]
    determinant = Fraction(1)
    for column in range(16):
        pivot = next(i for i in range(column, 16) if matrix[i][column])
        if pivot != column:
            matrix[pivot], matrix[column] = matrix[column], matrix[pivot]
            determinant *= -1
        value = matrix[column][column]
        determinant *= value
        matrix[column] = [x / value for x in matrix[column]]
        for i in range(column + 1, 16):
            multiple = matrix[i][column]
            matrix[i] = [x - multiple * y for x, y in zip(matrix[i], matrix[column])]
    assert determinant == -812032080 == t['integer_pivot_determinant']
    assert t['pivot_columns'] == list(range(16))
    assert t['free_columns'] == list(range(16, 577))
    assert len(t['tau']) == len(t['announcements']) == len(reg['slots']) == 16
    assert len(t['U']) == 561
    assert len(g['query_bindings']) == len(g['query_policy']) == 16
    bounds = [32 * 127 * sum(map(abs, row)) for row in rows]
    assert bounds == g['crypto']['row_signed_score_bounds']
    assert int(g['crypto']['q_hex'], 16) > 2 * max(bounds)
    for i, recipient in enumerate(ctx['recipients']):
        assert recipient['A'] == t['announcements'][i]['payload']['A']
        assert recipient['tau'] == t['tau'][i]
        assert recipient['row_sha256'] == digest(rows[i]) == reg['slots'][i]['row_sha256']
        assert recipient['row_id'] == i
        assert recipient['recipient_id'] == digest({
            'domain': 'dedicated-designated-recipient-v1', 'setup_id': ctx['setup_id'],
            'row_id': i, 'row_sha256': digest(rows[i]), 'A': recipient['A']})
        assert recipient['token_sha256'] == digest({key: value for key, value in recipient.items()
                                                    if key != 'token_sha256'})
        binding = {'context_id': EXPECTED_CONTEXT, **{key: recipient[key] for key in
                   ['row_id', 'row_sha256', 'recipient_id', 'token_sha256']}}
        query = {'schema': 'resident-designated-query-v1', 'params_id': ctx['params_id'],
                 **binding, 'coefficients': rows[i]}
        assert g['query_bindings'][digest(query)] == binding
        assert {'query_ct': digest(query), 'route': 0} in g['query_policy']
    report = {'claim_kind': 'EXECUTED', 'scope': 'Source byte identities, public setup/genesis hash bindings and rational matrix arithmetic only; no signature verification, group operations, crypto/runtime import, private reads or execution',
              'normal_002_status': 'public exports available' if exported else 'running; setup-only evidence',
              'source_checks': source_checks,
              'execution_pins_sha256': sha(REPORTS / 'execution_pins.json'),
              'source_pins_sha256': sha(AUTHOR / 'SOURCE_PINS.json'),
              'source_file_hashes': pins['source_files_sha256'],
              'previous_attempt': {'snapshot_source_files_verified': len(previous_pins),
                                   'changed_source_files': changed,
                                   'exact_change': 'Remove premature registration directory creation from setup_join.py',
                                   'command_exit_codes': previous_command_results,
                                   'commands_sha256': sha(previous / 'commands.jsonl'),
                                   'execution_pins_sha256': sha(previous / 'execution_pins.json')},
              'public_root': str(public_root), 'public_files_sha256': hashes,
              'genesis_canonical_sha256': EXPECTED_GENESIS,
              'context_sha256': EXPECTED_CONTEXT,
              'checks': {'identical_dependency_copies': len(source_checks),
                         'execution_source_pins': len(pins['source_files_sha256']),
                         'signature_implementation_pins': len(pins['signature_dependency']['files_sha256']),
                         'environment_binaries': len(environment),
                         'public_setup_genesis_bindings': 'passed',
                         'independent_integer_pivot_determinant': int(determinant),
                         'registration_slots': 16, 'matrix_dimension': 577,
                         'exact_recipient_token_and_query_bindings': 16,
                         'public_bounded_integer_no_wrap': 'passed',
                         'source_and_public_record_only': True},
              'not_recomputed': ['group completion/subgroup or token equations', 'Ed25519 signatures',
                                 'ciphertext arithmetic', 'private integer comparisons', 'RNG security/erasure/OS isolation'],
              'activity': {'crypto_runtime': 0, 'model_runtime': 0, 'private_file_reads': 0,
                           'private_file_hashes': 0, 'network_queries': 0}}
    (BASE / 'source_review.json').write_text(json.dumps(report, indent=2) + '\n')
    print(json.dumps(report['checks'], indent=2))


if __name__ == '__main__':
    main()
