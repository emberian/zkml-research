#!/usr/bin/env python3
"""One newly encoded teach, fresh generated proof, accepted-state query and refusal."""
import argparse
import contextlib
import copy
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import shutil
import sys
import time

import live
from live import j

HERE = Path(__file__).resolve().parent
TEACH = 'My replacement bank card still has not arrived after three weeks.'
QUERY = 'The bank mailed my new card, but I am still waiting for it.'


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--run', default='live001')
    args = p.parse_args()
    assert args.run.isalnum()
    output, root = HERE / 'results' / args.run, HERE / 'runtime' / args.run
    assert not output.exists() and not root.exists()
    output.mkdir(parents=True)
    started = time.monotonic_ns()
    j.write_json(output / 'command.json', {'argv': [sys.executable, '-B', str(Path(__file__)), '--run', args.run],
        'fixture': {'classes': ['card_arrival', 'cash_withdrawal_charge'], 'teach': TEACH, 'label': 'card_arrival', 'query': QUERY},
        'source_sha256': j.sha(Path(__file__).read_bytes()), 'started_utc': datetime.now(timezone.utc).isoformat()})
    initialized = live.initialize(root, ['card_arrival', 'cash_withdrawal_charge'])
    model = live.Live(root)
    before = model.status()
    staged = model.stage('card_arrival', TEACH, 'new-card-teach')
    assert staged['committed'] is False and staged['visible_to_query'] is False
    assert model.status() == before, 'Fresh encoding/proof generation must not publish the tentative state'
    j.write_json(output / 'staged.json', staged)
    # Submit a proposed model-root substitution through the actual frozen gate.
    # This specifically checks the protocol's model binding before any commit.
    bad = copy.deepcopy(j.read(Path(staged['bundle'])))
    bad['request']['request_id'] = 'invalid-model-root'
    bad['request']['next_model_root'] = '0' * 64
    bad_path = root / 'invalid_model_proposal.json'
    j.write_json(bad_path, bad)
    refused = None
    try:
        model.service.submit(bad_path)
    except j.Refused as error:
        refused = {'ok': False, 'code': error.code}
    assert refused == {'ok': False, 'code': 'proposed_model_root'}
    assert model.status() == before
    j.write_json(output / 'failed_proposal.json', {'request': bad['request'], 'refusal': refused,
        'head_before': before, 'head_after': model.status(), 'scope': 'Actual proposed-model-root gate refusal; not a malformed-proof experiment.'})
    committed = model.commit('new-card-teach')
    assert committed['ok'] is True and committed['status'] == 'committed'
    assert committed['counts'] == {'card_arrival': 1, 'cash_withdrawal_charge': 0}
    after = model.status()
    assert after['head']['head']['revision'] == 1
    assert after['head']['head']['classes']['cash_withdrawal_charge'] == before['head']['head']['classes']['cash_withdrawal_charge']
    query = model.query(QUERY)
    assert query['head'] == committed['head']
    assert query['answer']['label'] == 'card_arrival' and query['answer']['revision'] == 1
    assert len(query['answer']['ranking']) == 1  # Other declared class is empty.
    assert model.encoder.stats['encoded_texts'] == 2 and model.encoder.stats['forward_batches'] == 2
    # This direct integer comparison occurs only after actual public completion
    # and private receive. Both vectors are this instance's newly encoded inputs.
    with contextlib.redirect_stdout(sys.stderr):
        teach_vector, query_vector = model.encoder.encode([TEACH, QUERY]).tolist()
    expected = sum(a * b for a, b in zip(teach_vector, query_vector))
    actual = query['answer']['ranking'][0]['sum_dot']
    assert actual == expected and actual > 0
    # A fresh adapter object rebuilds its accepted view from the durable journal,
    # without loading the model weights again or mutating the issuer model state.
    reopened = live.Live(root).status()
    assert reopened == after
    issuer_state = j.read(root / 'issuer/learner.json')
    assert issuer_state['revision'] == 0 and issuer_state['classes'] == {}
    proposal = root / 'proposals/new-card-teach'
    proof_result = j.read(proposal / 'proved/result.json')
    assert proof_result['verified'] is True
    for old in ('acf747cf42eff8171b2b774abae5572e8d7bdb7ace144754c7605128c15e5ba6',
                '365006cd229920b4cda7118fa51f89cc012124e8681eb2e7b75291e402407a01'):
        assert staged['proof_sha256'] != old
    # Keep a small public evidence packet; do not copy keys or feature caches.
    copies = {'config.json': root / 'config.json', 'checkpoint.json': root / 'checkpoint.json',
        'genesis.json': root / 'journal/genesis.json', 'pipeline_result.json': proposal / 'proved/result.json',
        'pipeline_command.json': proposal / 'pipeline_command.json', 'pipeline.stdout': proposal / 'pipeline.stdout',
        'pipeline.stderr': proposal / 'pipeline.stderr', 'proof.bin': proposal / 'proved/proof/proof.bin',
        'proof.json': proposal / 'proved/proof/proof.json', 'source_event.json': proposal / 'candidate/source_event.json',
        'request.json': proposal / 'request.json', 'public_query_complete.json': Path(query['public_query_record']),
        'public_operations.jsonl': root / 'issuer/operations.jsonl'}
    for name, source in copies.items():
        shutil.copyfile(source, output / name)
    for name in ['export', 'emit', 'prove', 'verify']:
        for ext in ('stdout', 'stderr'):
            shutil.copyfile(proposal / f'proved/logs/{name}.{ext}', output / f'pipeline_{name}.{ext}')
    for name, value in [('committed', committed), ('query', query), ('final_head', after),
                         ('history', model.service.dispatch({'op': 'history'})), ('encoder_stats', model.encoder.stats)]:
        j.write_json(output / (name + '.json'), value)
    model.check_pins()
    result = {'schema': 'live-proved-learner-demo-v1', 'claim': 'EXECUTED new text teach -> fresh proof -> durable commit -> accepted-model query',
        'completed_utc': datetime.now(timezone.utc).isoformat(), 'elapsed_ns': time.monotonic_ns() - started,
        'accepted_new_teaches': 1, 'fresh_generated_proofs': 1, 'committed_queries': 1,
        'proof_sha256': staged['proof_sha256'], 'proof_bytes': (output / 'proof.bin').stat().st_size,
        'proof_pipeline_seconds': proof_result['elapsed_seconds'], 'failed_proposal_refusal': refused['code'],
        'failed_proposal_preserved_head': True, 'staged_candidate_not_visible': True,
        'journal_revision': 1, 'unchanged_other_class': True, 'reopened_exact_head': True,
        'encoder_new_texts': 2, 'encoder_forward_batches': 2, 'model_loaded_once': True,
        'actual_reader_score': actual, 'direct_integer_dot_after_private_receive': expected, 'integer_comparison_match': True,
        'query_label': query['answer']['label'], 'active_classes': 1, 'declared_classes': 2,
        'public_pipeline_process_group_absent': j.read(output / 'pipeline_command.json')['public_process_group_absent'],
        'all_public_work_before_private_receive': True, 'full_reader_retained': True,
        'scope': 'Fresh isolated two-class zero checkpoint, one active class after teaching. Trusted plaintext encoder/local adapter/FIFO/reader. Native proof gates ciphertext update; query arithmetic and decoder are actual executions, not new proof statements. No accuracy benchmark or confidentiality claim.'}
    j.write_json(output / 'RESULT.json', result)
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
