#!/usr/bin/env python3
"""Checkpoint completed public tranches; never execute Lean, crypto, model or private state.

Reuses the prior collectors' repository roots and evidence-map format. Explicit
schema adapters prevent guessing manifest roots. Hash records establish saved
byte consistency; saved proof/runtime assertions are not independently rerun.
Only this script and overnight_checkpoint_003.json are written.
"""
from pathlib import Path
import datetime
import hashlib
import json
import subprocess
import sys
import traceback
from collect_interrupted_run import HERE, REPO, SEEN

R = REPO / 'research/learn_infer_only'
REVIEW = R / 'experiments/adversarial_review'
FRONTIER = REPO / 'research/proof_frontier/2026-09-08/formal'
RUN017 = R / 'experiments/integration/results/run_017'
LONG = HERE / 'private_ema/emitted_long_run'
COUNTS = {}
FACTS = {}
COMMANDS = []
LONG_ALLOW = {LONG / 'freeze.json'}

# Observed frozen named anchors, fixed before this collector's first run.
ANCHORS = {
    "research/learn_infer_only/experiments/adversarial_review/cse_structure/MANIFEST.json": "087ea83cc9fb2db841ae82ed85fe50746580b335a5f88ea16b1ce9cf2e9e3298",
    "research/learn_infer_only/experiments/adversarial_review/cse_structure/REPORT.md": "97cade85451a4e76128a9eacda0c775889e17a1104ffbbfbab88241dff3ae0b9",
    "research/learn_infer_only/experiments/adversarial_review/emitted_schedule_execution/MANIFEST.json": "e9e9065822596283b5c542c5f2cb40cfc5f21b83aec381513b3c64d7cfb6b45f",
    "research/learn_infer_only/experiments/adversarial_review/emitted_schedule_execution/REPORT.md": "84fb1577069fee7f9888362bc26cc05753122a3eda8fdc3cfdff7662f08bf028",
    "research/learn_infer_only/experiments/adversarial_review/full_ud/REPORT.md": "65aaa22c832e21f8f52b90ffa0633fd0cfd9fb348ad7461658ee5eb38919b36a",
    "research/learn_infer_only/experiments/adversarial_review/full_ud/freeze.json": "52f76590a50dfa3db76cdb27d85506589cd9cac4b1aea6ce7f54f1f924f74ad2",
    "research/learn_infer_only/experiments/adversarial_review/full_ud_root_resolution/REPORT.md": "f657d2c8590f9ae53d72b57feaf45375360019f218589e38c1300da756c15698",
    "research/learn_infer_only/experiments/adversarial_review/full_ud_root_resolution/manifest.json": "90b852cefef76dfa6014a5c40f3c1284ac34f765c262592730bcd71ba89fea38",
    "research/learn_infer_only/experiments/adversarial_review/full_ud_sampling/REPORT.md": "d665fc454eb2b041968cde7c94838ad3a48be7a232edeb8abd015f4978fec9b5",
    "research/learn_infer_only/experiments/adversarial_review/full_ud_sampling/freeze.json": "8f75efc607cf316765b76744e24d2545777568c216597e956dbaee3b9ff0e1dd",
    "research/learn_infer_only/experiments/adversarial_review/live_semantic_bfv/manifest_v2.json": "a5cf1555edd15002103ea0da53f56b8036324ee5e90242074ac686a0fdf8fcf0",
    "research/learn_infer_only/experiments/adversarial_review/live_semantic_bfv/review_v2.json": "7216de925a3fd6fcdb818e6a8df0d63e821df1dcaf00a3bd8bbac40b70d314f9",
    "research/learn_infer_only/experiments/adversarial_review/pq_finite_costs/review_manifest.json": "5fbe76215c1b5eb8c5424fd9bd6fcbcd863e95a6cd741291f5e51ed3674dd71e",
    "research/learn_infer_only/experiments/adversarial_review/pq_finite_reduction/REPORT.md": "275000fbe4d485f0d31afff19e76ff5c05bc488cd66b85c547fae970e55aedfa",
    "research/learn_infer_only/experiments/adversarial_review/pq_finite_reduction/manifest.json": "f24f7888d41dd6a92ea626ce880326159740b6fc568e3136a9ea77b9dcaa46df",
    "research/learn_infer_only/experiments/adversarial_review/public_seed_setup/manifest.json": "e28e67d7b5dbaa8ec0c22d95b141417bdb89f228737d374a82d7718b283a4dbd",
    "research/learn_infer_only/experiments/adversarial_review/public_setup_pq/finite_reduction/MANIFEST.json": "2938fd3de8cf77bd80d2a8f2c17109f4d9dc8db8d6563763faf26c4dea435f01",
    "research/learn_infer_only/experiments/adversarial_review/public_setup_pq/finite_reduction/SEAL.json": "55f675f5c43e56961d81458a8453cc34cae48cf807d19a5300d3141f98553aa9",
    "research/learn_infer_only/experiments/adversarial_review/smudged_fixed_coordinate/review_manifest.json": "44ec8ccc1e772b7ca5f88f60b1c60fc934c697cc9ca18310a47e628000a2609b",
    "research/learn_infer_only/experiments/end_to_end/overnight_2026-09-08_baseline.json": "c3900b2f77cd701412c40622ecf790746722c9cbf96e92fdf53be1e1d5802e9a",
    "research/learn_infer_only/experiments/end_to_end/private_ema/emitted_long_run/freeze.json": "6cc20a07b75330c2fb7aaa19a2021c6b495096c6b477b1554eb4a2a14c7943e8",
    "research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_successor/encrypted_bfv/live_successor/REPORT.md": "75d9d0f94c078767f923d651141d87993a21bcd97b02da86efe9f830c399e1d8",
    "research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_successor/encrypted_bfv/live_successor/manifest.json": "9e04634c8e7346697035372e363de4fb6a1abd5efd92e552eef6e1e6f86dce9f",
    "research/learn_infer_only/experiments/end_to_end/utility/semantic_axis_successor/encrypted_bfv/live_successor/timing_addendum_manifest.json": "f1226c40feeab45bdf51554200c9a70f5da4c5ac20410efcef7b6e4c1edf0453",
    "research/learn_infer_only/experiments/integration/results/run_017/SUMMARY.md": "5877163fdd8dba5b0df1ef1b23571beada1ff12d4a5d60b35e592a46d71bb867",
    "research/learn_infer_only/experiments/integration/results/run_017/harness_archive_recovery.json": "bc8d12169a83a365672597b8cb33bc998f1cf4f00f5fe18763df18f662b0a1e2",
    "research/learn_infer_only/experiments/integration/results/run_017/report.json": "a043da7937d81a7f05a65f5be520b7325b5ce54a219fb5cdaf23010631e71536",
    "research/learn_infer_only/experiments/private_construction/designated_span/public_coin_setup/public_seed/MANIFEST.json": "441fd9012794a610c6a6bb7fd793303e894a832b1dea41cbaa7fcd0df04ed073",
    "research/learn_infer_only/experiments/private_construction/public_setup_pq/alternatives/MANIFEST.json": "0bf70a6a12442a02f3fced956a456722985d8279ee651e299a501fdff3741654",
    "research/learn_infer_only/formal/cse_structure/manifest.json": "aec59f6afbed5a180a2a023465e6fe2e4347464c8f8a29a5ecef0d6d585bbef6",
    "research/learn_infer_only/formal/emitted_schedule_execution/manifest.json": "cc5041fce37ac7cd72e05475291ff506a2ae8e95767f5565dbc61335d5cc0053",
    "research/learn_infer_only/formal/integration/minidregg-combined-resident-915.patch": "00175cda5228163b1626eabf94559ac3d8f406b7635f70dd01976b5301e5c3c6",
    "research/proof_frontier/2026-09-08/formal/full_ud/manifest.json": "4151a1b24f599cee25b339090028f3680a558906b85f805f53dec2de0a056ecb",
    "research/proof_frontier/2026-09-08/formal/full_ud_babybear/provenance.json": "8f3ad07e930aa41cfedd4242e4fe279b2ceadb0422684660f90d14db050bdf60",
    "research/proof_frontier/2026-09-08/formal/full_ud_commitment_timing/manifest.json": "cf81d803dea2e2a4f53ab2cdb9816ac2634b5c720819b2994e7e3934434b066e",
    "research/proof_frontier/2026-09-08/formal/full_ud_sampling_budget/manifest.json": "463d3efd156ff50cc991dd4dbe10ce2d6c2a7084040da4babb6518febe151bb9"
}


def allowed(path):
    path = Path(path).resolve()
    assert not any(part in path.parts for part in ('.private', '.private_fixture', 'private')), path
    assert path.name not in ('client_key.bin', 'secret_key.bin', 'bfv_secret.bin', 'signing.key'), path
    assert not any(word in str(path) for word in
                   ('signer_route', 'verified_route', '/hardness/', '/ring_candidate/',
                    '/babybear_folding_tower/', '/cse_structure_successor/',
                    '/root_resolution_future/', '/root_resolution_successor/', '/run_018/')), path
    if path.is_relative_to(LONG):
        assert path in LONG_ALLOW, ('Only the running lane\'s explicit public freeze inputs are allowed', path)
    assert path not in (R / 'experiments/integration/check_all_formal.py',
                        R / 'formal/integration/minidregg-combined-resident.patch',
                        R / 'experiments/integration/results/latest.json'), path
    return path


def pin_public(path, expected=None, expected_bytes=None):
    path = allowed(path)
    h = hashlib.sha256()
    size = 0
    with path.open('rb') as stream:
        while raw := stream.read(1024 * 1024):
            h.update(raw)
            size += len(raw)
    row = {'sha256': h.hexdigest(), 'bytes': size}
    if expected is not None:
        assert row['sha256'] == expected, (str(path), expected, row['sha256'])
    if expected_bytes is not None:
        assert size == expected_bytes, (str(path), expected_bytes, size)
    if str(path) in SEEN:
        assert SEEN[str(path)] == row, ('Changed during collection', str(path))
    SEEN[str(path)] = row
    return row


def read_public(path):
    pin_public(path)
    return json.loads(Path(path).read_bytes())


def inventory(label, base, entries):
    if isinstance(entries, dict):
        rows = []
        for name, value in entries.items():
            if isinstance(value, str):
                rows.append({'path': name, 'sha256': value})
            else:
                assert isinstance(value, dict) and 'sha256' in value
                if 'path' in value:
                    assert value['path'] == name, (label, name, value['path'])
                rows.append(dict(value, path=name))
    else:
        assert isinstance(entries, list)
        rows = entries
    for row in rows:
        assert set(row) >= {'path', 'sha256'}, (label, row)
        p = Path(row['path'])
        pin_public(p if p.is_absolute() else Path(base) / p, row['sha256'], row.get('bytes'))
    COUNTS[label] = len(rows)
    return len(rows)


def manifest(path, key='files', base=None, label=None):
    path = Path(path)
    data = read_public(path)
    inventory(label or str(path.relative_to(REPO)), path.parent if base is None else base, data[key])
    return data


def saved_check(record):
    assert record['exit_code'] == 0, record
    if 'source_unchanged' in record:
        assert record['source_unchanged']
    log = Path(record['log'])
    pin_public(log)
    if log.with_suffix('.json').exists():
        check = read_public(log.with_suffix('.json'))
        assert check['exit_code'] == 0
    return str(log)


def git_output(argv):
    done = subprocess.run(argv, capture_output=True, text=True)
    COMMANDS.append({'argv': argv, 'cwd': str(Path.cwd()), 'returncode': done.returncode,
                     'stdout': done.stdout, 'stderr': done.stderr})
    assert done.returncode == 0, argv
    return done.stdout


def collect_run017():
    report = read_public(RUN017 / 'report.json')
    assert report['status'] == 'passed' and report['module_count'] == 70 and report['theorem_pins'] == 915
    assert report['input_hashes_before'] == report['input_hashes_after']
    assert not report['changed_inputs'] and not report['changed_companion_sources']
    assert report['combined_patch_exact_content_verified'] and report['all_selected_modules_rooted']
    assert report['no_clean_full_build_claim']
    recovery = read_public(RUN017 / 'harness_archive_recovery.json')
    assert recovery['exact_match']
    harness_hash = '42d9ba6f2b064d8d2896e5c7d02f2732019388f1d13e82fddf1a78b1258b45b9'
    assert recovery['sha256'] == harness_hash
    pin_public(RUN017 / 'check_all_formal.py', harness_hash)
    patch_hash = report['combined_patch']['sha256']
    assert patch_hash == '00175cda5228163b1626eabf94559ac3d8f406b7635f70dd01976b5301e5c3c6'
    pin_public(RUN017 / 'minidregg-combined-resident.patch', patch_hash)
    pin_public(R / 'formal/integration/minidregg-combined-resident-915.patch', patch_hash)
    remaps = {
        R / 'experiments/integration/check_all_formal.py': RUN017 / 'check_all_formal.py',
        R / 'experiments/integration/modules_overnight_core.json': RUN017 / 'modules_overnight_core.json',
    }
    for name, expected in report['input_hashes_before'].items():
        original = Path(name).resolve()
        pin_public(remaps.get(original, original), expected)
    COUNTS['run017_inputs_with_exact_archive_substitution'] = len(report['input_hashes_before'])
    commands = report['commands']
    for record in commands:
        assert record['exit_code'] == 0
        saved = read_public(RUN017 / record['log'])
        assert saved['exit_code'] == 0
    COUNTS['run017_saved_command_records'] = len(commands)
    census = read_public(RUN017 / 'axiom_census.json')
    assert len(census) == 70 and sum(row['pin_count'] for row in census.values()) == 915
    assert sum(row['theorem_count'] for row in census.values()) == 915
    for row in census.values():
        pin_public(row['source'], row['sha256'])
        assert row['theorem_count'] == row['pin_count'] == len(row['pins'])
        assert not row['forbidden_constructs']
    objects = read_public(RUN017 / 'compiled_olean_hashes.json')
    inventory('run017_compiled_public_olean_artifacts', Path('/'), list(objects.values()))
    dependencies = read_public(RUN017 / 'cached_dependency_artifacts.json')
    # This saved cache census has sizes/mtimes, not content hashes. Do not invent pins.
    assert all(set(row) == {'path', 'size', 'mtime_ns'} for row in dependencies)
    completed = sorted(p for p in RUN017.iterdir() if p.is_file())
    for path in completed:
        assert path.suffix in ('.json', '.py', '.md', '.patch'), path
        pin_public(path)
    COUNTS['run017_completed_directory_files'] = len(completed)
    FACTS['run017'] = {'saved_status': report['status'], 'selected_modules': 70, 'exact_pins_in_saved_census': 915,
                       'umbrella_count': len(report['umbrella_builds']), 'elapsed_seconds_reported': report['elapsed_seconds'],
                       'recovered_harness_exact_hash': harness_hash, 'numbered_and_archived_patch_sha256': patch_hash,
                       'cached_dependency_metadata_rows': len(dependencies), 'cached_dependency_bytes_rehashed': False,
                       'admit_identifier_tokens_in_saved_census': sum(len(row['admit_identifier_tokens']) for row in census.values()),
                       'lexical_note': 'Ordinary admit identifiers are recorded separately from forbidden constructs; this collector does not reclassify Lean tokens.',
                       'input_archive_substitutions': {str(k): str(v) for k, v in remaps.items()},
                       'new_lean_runs': 0, 'clean_full_build_claim': False}


def collect_proofs():
    full = FRONTIER / 'full_ud'
    m = read_public(full / 'manifest.json')
    assert m['owned_pins'] == 38 and m['exact_byte_checks_complete'] and m['all_pins_standard_only']
    pin_public(full / 'full-ud.patch', m['patch_sha256'])
    inherited = {
        'Theory/PolynomialMatrixKernel.lean': FRONTIER / 'polynomial_kernel/all_pins_successor/PolynomialMatrixKernel.lean',
        'Theory/PolynomialBivariate.lean': FRONTIER / 'polynomial_gluing/universe_successor/PolynomialBivariate.lean',
        'Theory/PolynomialGluingStatement.lean': FRONTIER / 'polynomial_gluing/universe_successor/PolynomialGluingStatement.lean',
        'Theory/PolynomialGluing.lean': FRONTIER / 'polynomial_gluing/universe_successor/PolynomialGluing.lean',
    }
    for row in m['modules']:
        pin_public(full / 'src' / row['path'] if row['owned'] else inherited[row['path']], row['sha256'])
    COUNTS['full_ud_frozen_source_modules'] = len(m['modules'])
    manifest(REVIEW / 'full_ud/freeze.json')
    verified = read_public(REVIEW / 'full_ud/verification.json')
    assert verified['status'] == 'PASS' and verified['owned_theorems'] == 38 and verified['all_pins'] == 105
    assert verified['instrumentation_sha256'] == pin_public(RUN017 / 'check_all_formal.py')['sha256']
    for check, recorded in zip(m['checks'], verified['stored_lean_checks'], strict=True):
        assert Path(check['command'][-1]).with_suffix('').as_posix().replace('/', '.') == recorded['module']
        log = Path(saved_check(check))
        pin_public(log, recorded['log_sha256'])
        pin_public(log.with_suffix('.json'), recorded['record_sha256'])
    COUNTS['full_ud_saved_final_lean_checks'] = len(m['checks'])

    baby = FRONTIER / 'full_ud_babybear'
    p = read_public(baby / 'provenance.json')
    assert p['expected_pins'] == len(p['pins']) == 12 and p['frozen_core_all_14_hashes_unchanged']
    pin_public(baby / 'BabyBearFullUD.lean', p['source_sha256'])
    pin_public(baby / 'babybear-full-ud.patch', p['patch_sha256'])
    saved_check(p['check'])
    sampled = FRONTIER / 'full_ud_sampling_budget'
    s = read_public(sampled / 'manifest.json')
    assert s['pins'] == s['declarations'] == 25 and s['frozen']
    pin_public(sampled / 'FullUDSamplingBudget.lean', s['source_sha256'])
    pin_public(sampled / 'full-ud-sampling-budget.patch', s['patch_sha256'])
    saved_check(s['checked'])
    manifest(REVIEW / 'full_ud_sampling/freeze.json')
    sv = read_public(REVIEW / 'full_ud_sampling/source_verification.json')
    assert sv['status'] == 'PASS'
    for row in sv['checks'].values():
        pin_public(row['source'], row['source_sha256'])
        pin_public(row['patch'], row['patch_sha256'])
    inventory('sampling_review_public_read_sources', Path('/'), sv['read_source_pins'])

    timing = FRONTIER / 'full_ud_commitment_timing'
    t = read_public(timing / 'manifest.json')
    assert t['owned_pins'] == 36 and t['owned_modules'] == 5
    assert t['exact_guarded_checks_complete'] and t['all_16_frozen_dependency_hashes_unchanged']
    pin_public(timing / 'full-ud-commitment-timing.patch', t['patch_sha256'])
    for row in t['modules']:
        pin_public(timing / 'src' / row['path'], row['sha256'])
        saved_check(row['check'])
    COUNTS['timing_frozen_source_modules'] = len(t['modules'])
    manifest(REVIEW / 'full_ud_root_resolution/manifest.json')
    tv = read_public(REVIEW / 'full_ud_root_resolution/verification.json')
    assert tv['status'] == 'PASS' and tv['final_source_hashes_unchanged']
    for folder in (full, baby, sampled, timing):
        for name in ('README.md', 'integration_entry.json'):
            if (folder / name).exists():
                pin_public(folder / name)
    FACTS['full_ud_family'] = {'core_owned_pins_reported': 38, 'core_with_dependencies_pins_reported': 105,
                              'BabyBear_carrier_pins_reported': 12, 'sampling_budget_pins_reported': 25,
                              'timing_resolution_pins_reported': 36, 'new_lean_runs': 0,
                              'scope': 'Exact frozen source/patch/log links and saved review outcomes; no new theorem checking.'}

    for name, count in [('emitted_schedule_execution', 19), ('cse_structure', 18)]:
        base = R / 'formal' / name
        own = manifest(base / 'manifest.json')
        verification = read_public(base / 'results/verification.json')
        assert verification['all_package_checks_passed']
        assert verification['census']['pin_count'] == verification['census']['theorem_count'] == count
        assert own['source_sha256'] == verification['source_sha256'] and own['patch_sha256'] == verification['patch_sha256']
        reviewed = manifest(REVIEW / name / 'MANIFEST.json')
        assert reviewed['frozen'] and reviewed['source_sha256'] == own['source_sha256']
        assert reviewed['patch_sha256'] == own['patch_sha256']
        FACTS[name] = {'saved_package_passed': True, 'theorem_and_pin_count_reported': count,
                       'review_verdict_reported': reviewed['verdict'], 'new_lean_runs': 0}


def collect_source_reviews():
    finite = REVIEW / 'public_setup_pq/finite_reduction'
    fm = manifest(finite / 'MANIFEST.json', 'artifacts')
    assert fm['status'] == 'PASS'
    seal = read_public(finite / 'SEAL.json')
    assert seal['status'] == 'PASS' and seal['manifest_sha256'] == pin_public(finite / 'MANIFEST.json')['sha256']
    inventory('finite_reduction_frozen_note_inputs', Path('/'), fm['frozen_note_inputs'])
    source = fm['parameter_source']
    pin_public(source['path'], source['sha256'])
    sources = read_public(finite / 'SOURCES.json')['sources']
    for row in sources:
        pin_public(row['pdf_path'], row['pdf_sha256'])
        pin_public(row['extract_path'], row['extract_sha256'])
    COUNTS['finite_reduction_pdf_and_extract_pairs'] = len(sources)
    independent = read_public(REVIEW / 'pq_finite_reduction/manifest.json')
    inventory('finite_reduction_review_author_inputs', finite, independent['frozen_author_files'])
    inventory('finite_reduction_review_outputs', REVIEW / 'pq_finite_reduction', independent['review_files'])
    assert independent['theorem_source_unchanged_since_check']
    cost = manifest(REVIEW / 'pq_finite_costs/review_manifest.json', 'artifacts', REPO)
    subject_paths = {'FEASIBILITY.md': R / 'experiments/private_construction/public_setup_pq/costs/FEASIBILITY.md',
                     'BOUND.md': REVIEW / 'public_setup_pq/quantitative_regularity/BOUND.md'}
    assert set(cost['subjects_sha256']) == set(subject_paths)
    for name, expected in cost['subjects_sha256'].items():
        pin_public(subject_paths[name], expected)
    FACTS['finite_pq'] = {'author_saved_status': fm['status'], 'review_verdict_reported': independent['verdict'],
                          'cost_review_verdict_reported': cost['verdict'], 'crypto_or_estimator_runs': 0,
                          'scope': 'Source/math/error-budget notes and saved reviews, not a QPT implementation certificate.'}

    alternatives = R / 'experiments/private_construction/public_setup_pq/alternatives'
    am = read_public(alternatives / 'MANIFEST.json')
    for field in ('source_pdfs', 'reused_frozen_public_inputs', 'owned_artifacts'):
        inventory('smudged_author_' + field, Path('/'), am[field])
    sm = read_public(REVIEW / 'smudged_fixed_coordinate/review_manifest.json')
    assert sm['author_artifacts_unchanged']
    for field in ('frozen_subjects', 'all_author_manifest_links_rechecked', 'owned_artifacts'):
        inventory('smudged_review_' + field, Path('/'), sm[field])
    FACTS['smudged_fixed_coordinate'] = {'author_artifacts_unchanged_reported': True,
                                        'scope': sm['scope'], 'new_crypto_or_estimator_runs': 0}

    seed = R / 'experiments/private_construction/designated_span/public_coin_setup/public_seed'
    manifest(seed / 'MANIFEST.json')
    sr = manifest(REVIEW / 'public_seed_setup/manifest.json')
    pin_public(seed / 'PROPOSAL.md', sr['frozen_proposal_sha256'])
    verification = read_public(REVIEW / 'public_seed_setup/verification.json')
    assert verification['status'] == 'PASS' and verification['source_unchanged']
    FACTS['public_seed_setup'] = {'review_verdict_reported': sr['verdict'],
                                 'scope': 'Classical-ROM source proposal and finite witness records; not a setup implementation run.'}


def collect_live_bfv():
    live = HERE / 'utility/semantic_axis_successor/encrypted_bfv/live_successor'
    manifest(live / 'manifest.json')
    correction = manifest(live / 'timing_addendum_manifest.json')
    assert correction['original_manifest_sha256'] == pin_public(live / 'manifest.json')['sha256']
    # Completed correction files contain the external contention digest; do not
    # follow it into mutable records belonging to the still-running long lane.
    manifest(REVIEW / 'live_semantic_bfv/manifest_v2.json')
    accepted = read_public(REVIEW / 'live_semantic_bfv/review_v2.json')
    assert accepted['accepted'] and accepted['prior_integration_acceptance_unchanged']
    assert accepted['author_timing_addendum_manifest_sha256'] == pin_public(live / 'timing_addendum_manifest.json')['sha256']
    report = read_public(live / 'reports/run001/report.json')
    command = read_public(live / 'run.command.json')
    assert report['ok'] and report['all_oracle_matches'] and command['returncode'] == 0
    assert (report['learns'], report['infers'], report['events'], report['expiries']) == (1, 2, 3, 0)
    assert report['actual_model_forward_calls'] == 1 and report['actual_axis_examples'] == 2
    assert report['public_phase_decryptions'] == report['baseline_decryptions'] == 0
    assert report['verified_decryptions_after_public_verification'] == 2
    assert command['source_snapshot_and_model_bytes_unchanged']
    assert [r['phase'] for r in command['phases']] == ['public_phase', 'public_verify', 'private_drain', 'validate']
    assert all(r['returncode'] == 0 and r['process_group_absent'] and not r['timed_out'] for r in command['phases'])
    timing = read_public(live / 'timing_addendum.json')
    FACTS['live_bfv'] = {'saved_attempt_passed': True, 'learns_reported': 1, 'infers_reported': 2,
                         'model_forwards_reported': 1, 'private_integer_matches_reported': 2,
                         'public_phase_decryptions_reported': 0, 'later_private_decryptions_reported': 2,
                         'output_change_reported': report['output_changed_after_learning'],
                         'scope': 'Full reader key, trusted plaintext issuer, shared OS; fixed-mapping change boolean reveals selected score. Private results attributed.',
                         'timing_correction': {'last_infer_checkpoint_utc_reported': timing['last_infer_event']['updated_utc'],
                                               'live_start_utc': timing['actual_live_start_utc'],
                                               'outer_wall_ns': timing['live_outer_wall_ns'],
                                               'external_long_run_contention_record_followed': False},
                         'new_model_or_crypto_runs': 0, 'private_file_reads': 0}


def collect_running_freeze_only():
    freeze = read_public(LONG / 'freeze.json')
    entries = freeze['files']
    assert len(entries) == 39
    for name, row in entries.items():
        path = Path(name).resolve()
        assert path.is_absolute() and row['path'] == name
        assert not any(part in path.parts for part in ('.private', '.private_fixture', 'private'))
        assert path.name not in ('client_key.bin', 'secret_key.bin', 'bfv_secret.bin', 'signing.key')
        if 'keys' in path.parts:
            assert 'public' in path.parts and path.name in ('public_key.bin', 'server_key.bin')
        if path.is_relative_to(LONG):
            assert path.suffix == '.py' or path.name in ('CONTRACT.md', 'preflight.json'), path
    LONG_ALLOW.update(Path(name).resolve() for name in entries)
    inventory('running_emitted_long_run_public_freeze_inputs_only', Path('/'), entries)
    FACTS['running_emitted_long_run'] = {'scope': 'Only the immutable 39-entry public input freeze was hashchecked.',
                                       'workload_completed_claim': False, 'progress_or_runtime_record_read': False,
                                       'private_client_or_key_file_read': False, 'crypto_runs': 0}


def companion_baselines():
    baseline = read_public(HERE / 'overnight_2026-09-08_baseline.json')
    companions = {}
    for name in ('minidregg', 'breadstuffs'):
        item = baseline['repositories'][name]
        root = Path(item['path'])
        head = git_output(['git', '-C', str(root), 'rev-parse', 'HEAD']).strip()
        status = git_output(['git', '-C', str(root), 'status', '--porcelain=v1', '--untracked-files=all'])
        assert head == item['head'] and status == item['status'], name
        for relative, row in item['preexisting_dirty_content'].items():
            pin_public(root / relative, row['sha256'], row['bytes'])
        companions[name] = {'head_unchanged': True, 'head': head, 'status_unchanged': True,
                            'dirty_file_bytes_unchanged': True, 'dirty_files_checked': len(item['preexisting_dirty_content'])}
    return companions


def main():
    start = datetime.datetime.now(datetime.timezone.utc).isoformat()
    error = None
    companions = {}
    base_commit = current_head = None
    try:
        for relative, expected in ANCHORS.items():
            pin_public(REPO / relative, expected)
        pin_public(__file__)
        for name in ('collect_interrupted_run.py', 'overnight_checkpoint_001.py', 'overnight_checkpoint_002.py'):
            pin_public(HERE / name)
        base_commit = git_output(['git', '-C', str(REPO), 'rev-parse', 'cf0f91f^{commit}']).strip()
        current_head = git_output(['git', '-C', str(REPO), 'rev-parse', 'HEAD']).strip()
        collect_run017()
        collect_proofs()
        collect_source_reviews()
        collect_live_bfv()
        collect_running_freeze_only()
        companions = companion_baselines()
        # Hash-only final pass prevents a successful mixed-time artifact view.
        for path, recorded in list(SEEN.items()):
            pin_public(path, recorded['sha256'], recorded['bytes'])
    except Exception as exc:
        error = traceback.format_exc()
    summary = {'all_passed': error is None, 'files_hashed': len(SEEN), 'inventories': len(COUNTS),
               'named_frozen_anchors': len(ANCHORS), 'companion_repositories': len(companions)}
    stdout = json.dumps(summary, sort_keys=True) + '\n'
    stderr = '' if error is None else error + '\n'
    result = {'schema': 'completed-public-overnight-checkpoint-v3', 'started_utc': start,
              'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
              'all_passed': error is None, 'error': error,
              'collection_since_commit': base_commit, 'repository_head_observed': current_head,
              'scope': 'Completed named tranches only, plus immutable public inputs of the running emitted lane. Saved source/evidence hash verification only. Manifest/report booleans and private results are attributed records; no claims rerun.',
              'excluded': ['Stopped task paths', 'new hardness package/review deferred to separate collection; active ring and seed-adapter work', 'CSE successor and BabyBear tower/future root-resolution work',
                           'running integration run018 and mutable integration aliases', 'long-run mutable progress/results/coordination records',
                           'private client, input, key and answer files'],
              'counts': COUNTS, 'saved_record_observations': FACTS, 'companions': companions,
              'named_anchor_sha256': ANCHORS, 'files': dict(sorted(SEEN.items())),
              'commands_executed': COMMANDS,
              'collector_command': {'argv': sys.orig_argv, 'resolved_executable': sys.executable,
                                    'resolved_script': str(Path(__file__).resolve()), 'cwd': str(Path.cwd()),
                                    'returncode': 0 if error is None else 1, 'stdout': stdout, 'stderr': stderr},
              'new_lean_crypto_model_or_estimator_runs': 0, 'private_file_reads': 0,
              'external_queries': 0}
    (HERE / 'overnight_checkpoint_003.json').write_text(json.dumps(result, indent=2) + '\n')
    sys.stdout.write(stdout)
    sys.stderr.write(stderr)
    return 0 if error is None else 1


if __name__ == '__main__':
    raise SystemExit(main())
