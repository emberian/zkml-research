"""Independent standard-library-only public source/provenance checks; no imports from author code."""
import ast
import hashlib
import json
import tarfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
EXPERIMENTS = HERE.parents[1]
SEM = EXPERIMENTS / 'end_to_end/utility/semantic_axis_successor'
LIVE = SEM / 'encrypted_bfv/live_successor'
reads = {}

def read(path):
    path = Path(path)
    assert '.private' not in path.parts and not path.name.endswith('.sqlite3')
    raw = path.read_bytes()
    reads[str(path)] = hashlib.sha256(raw).hexdigest()
    return raw

def sha(path):
    read(path)
    return reads[str(Path(path))]

def load(path):
    return json.loads(read(path))

def live_class(source):
    node = next(n for n in ast.walk(ast.parse(source)) if isinstance(n, ast.ClassDef) and n.name == 'LiveRun')
    return ast.get_source_segment(source, node)

def main():
    freeze = load(LIVE / 'freeze.json')
    runtime = Path(freeze['runtime'])
    reports = Path(freeze['reports'])
    snap = runtime / 'e2e'
    assert not (LIVE / 'run_started.json').exists(), 'Prelaunch review only'
    for path, expected in freeze['public_source_dependencies'].items():
        assert sha(path) == expected, path
    for name, expected in freeze['snapshot_source_pins'].items():
        assert sha(snap / name) == expected, name
    assert load(reports / 'source_pins.json') == freeze['snapshot_source_pins']
    assert load(reports / 'frontend_dependencies.json') == freeze['public_source_dependencies']
    assert load(reports / 'public_query_pins.json') == freeze['query_vector_pins']
    for name, expected in freeze['query_vector_pins'].items():
        assert sha(runtime / 'public_query_inputs' / name) == expected, name
    assert load(runtime / 'public_query_inputs/q01.json') == [127] + [0] * 576
    policy = load(runtime / 'query_policy.json')
    assert len(policy) == 16
    for i, row in enumerate(policy):
        assert row == {'route': 0 if i < 8 else 1, 'path': str(runtime / 'public_query_inputs' / f'q{i:02d}.json')}
    old = read(EXPERIMENTS / 'end_to_end/verified_reader/live_driver.py').decode()
    adapted = read(LIVE / 'driver.py').decode()
    assert live_class(old) == live_class(adapted)
    assert read(snap / 'verified_reader/live_driver.py') == adapted.encode()
    expected = read(SEM / 'score.py').decode()
    for before, after in [("'new_test_texts':128", "'new_test_texts':1"), ("'semantic_bits_per_framing':256", "'semantic_bits_per_framing':2"), ("'pairs_per_framing':128", "'pairs_per_framing':1"), ("'heldout_inputs':128", "'heldout_inputs':1")]:
        assert expected.count(before) == 1
        expected = expected.replace(before, after)
    assert read(LIVE / 'encoder/score.py').decode() == expected
    python_files = [LIVE / n for n in ['prepare.py', 'run.py', 'driver.py', 'public_verify.py', 'drain.py', 'validate.py', 'issue_semantic_text.py', 'encoder/common.py', 'encoder/score.py']]
    for path in python_files:
        ast.parse(read(path), filename=str(path))
    parent_counts = {}
    for path, expected in freeze['parent_entries_preserved'].items():
        base = Path(path)
        entries = load(base / 'manifest.json')['files']
        for name, row in entries.items():
            assert sha(base / name) == row['sha256'], (base, name)
        assert len(entries) == expected
        parent_counts[path] = len(entries)
    archive_expected = {n: h for n, h in freeze['snapshot_source_pins'].items() if n != 'resident-crypto'}
    for name in ['issue_semantic_text.py', 'encoder/common.py', 'encoder/score.py', 'encoder_inventory.json', 'CONTRACT.md']:
        archive_expected['semantic_frontend/' + name] = sha(LIVE / name)
    archive_expected['semantic_frontend/public_framing_definitions.json'] = sha(SEM.parent / 'semantic_axis_selection/prompts.json')
    archive_path = reports / 'source_snapshot.tar.gz'
    sha(archive_path)
    with tarfile.open(archive_path) as tar:
        members = [m for m in tar.getmembers() if m.isfile()]
        assert len(members) == len(archive_expected) and {m.name for m in members} == set(archive_expected)
        for member in members:
            assert '.private' not in Path(member.name).parts
            assert hashlib.sha256(tar.extractfile(member).read()).hexdigest() == archive_expected[member.name], member.name
    previous_model_check = load(HERE / 'model_preflight.json')
    model_pins = load(reports / 'model_pins.json')
    inventory = load(LIVE / 'encoder_inventory.json')
    assert freeze['model_files'] == previous_model_check['model_files'] == model_pins['files'] == inventory['model_files']
    assert freeze['model_path'] == previous_model_check['model_path'] == model_pins['model_path'] == inventory['model_path']
    assert inventory['token_alternatives'] == [15, 16] and inventory['fixed_framing'] == 'A'
    assert inventory['expected_forward_calls'] == 1 and inventory['actual_partial_batch_size'] == 2
    assert inventory['maximum_batch_size'] == 8 and inventory['actual_scored_axes_planned'] == 2
    freshness = load(reports / 'freshness.json')
    texts = set()
    assert len(freshness['corpora']) == 5
    for row in freshness['corpora']:
        assert sha(row['path']) == row['sha256']
        corpus = load(row['path'])
        assert len(corpus) == row['records']
        texts.update(x['text'] for x in corpus)
    assert len(texts) == freshness['unique_prior_texts']
    result = {'schema': 'live-semantic-independent-source-check-v1', 'ok': True,
              'freeze_sha256': sha(LIVE / 'freeze.json'),
              'public_dependency_files': len(freeze['public_source_dependencies']),
              'snapshot_files': len(freeze['snapshot_source_pins']), 'archive_files': len(archive_expected),
              'query_files': len(freeze['query_vector_pins']), 'python_files_parsed': len(python_files),
              'parent_entries_preserved': parent_counts, 'LiveRun_class_identical': True,
              'scorer_only_four_output_count_changes': True, 'q01_first_basis_127': True,
              'model_files_independently_hashed_in_model_preflight': len(previous_model_check['model_files']),
              'freshness_public_corpus_files': len(freshness['corpora']), 'unique_prior_texts': len(texts),
              'private_text_freshness_independently_recomputed': False,
              'model_or_crypto_imports': 0, 'model_forwards': 0, 'private_file_reads': 0,
              'source_sha256': sha(__file__), 'public_file_sha256': reads}
    (HERE / 'source_preflight.json').write_text(json.dumps(result, sort_keys=True, indent=2) + '\n')
    print(json.dumps({k:v for k,v in result.items() if k != 'public_file_sha256'}, sort_keys=True))

if __name__ == '__main__':
    main()
