#!/usr/bin/env python3
"""Publishable records from the completed fixed public workload, excluding keys/proofs."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil

HERE = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def snapshot(root, output):
    root, output = root.resolve(), output.resolve()
    controller = root.with_name(root.name + '.workload')
    summary_path = controller / 'RESULT.json'
    summary = json.loads(summary_path.read_text())
    packed = summary['schema'] == 'packed-class-lifecycle-result-v1'
    corpus = HERE / 'packed/workload/corpus.json' if packed else HERE / 'workload.json'
    corpus_key = 'corpus_sha256' if packed else 'workload_sha256'
    if not summary['complete'] or summary[corpus_key] != sha(corpus):
        raise SystemExit('Snapshot requires a completed run of the fixed public workload.')
    if output.exists():
        raise SystemExit('Choose a new snapshot directory; retained records are not overwritten.')
    sources = {Path('RESULT.json'): summary_path,
               Path('identity.json'): controller / 'identity.json',
               Path('genesis.json'): root / 'journal/genesis.json'}
    signed = controller / 'engine_reference.json'
    if signed.exists():
        sources[Path('engine_reference.json')] = signed
    for path in sorted((controller / 'steps').glob('*/completed.json')):
        sources[path.relative_to(controller)] = path
        for attempt in sorted(path.parent.glob('attempt-*')):
            if attempt.suffix in ('.json', '.stdout', '.stderr'):
                sources[attempt.relative_to(controller)] = attempt
    # Only controller metadata and its terminal stdout/stderr enter this package.
    # Ciphertexts, evaluation/reader keys and the full proof corpus stay in runtime.
    for name in ('workload.stdout', 'workload.stderr'):
        path = root.parent / name
        if path.exists():
            sources[Path(name)] = path
    records = {}
    output.mkdir(parents=True)
    for relative, source in sources.items():
        target = output / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
        records[str(relative)] = {'sha256': sha(target), 'bytes': target.stat().st_size,
                                  'source': str(source)}
    manifest = {'schema': 'continuing-public-workload-snapshot-v1',
                'claim': 'EXECUTED', 'engine': summary.get('engine', {'score_kind': 'squared', 'proof_backend': 'compact'}),
                'source_controller': str(controller), 'files': records,
                'scope': 'Fixed public authored corpus. Execution records, not a portable verifier package. Full reader survives.',
                'source_note': 'Each worker command and backend genesis pins are retained. The original squared run began at commit 08581d0 and later processes reopened through the compatible engine integration.'}
    (output / 'MANIFEST.json').write_text(json.dumps(manifest, indent=2, sort_keys=True) + '\n')
    print(json.dumps({'snapshot': str(output), 'files': len(records),
                      'bytes': sum(r['bytes'] for r in records.values()), 'complete': True}))


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('root', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    snapshot(args.root, args.output)
