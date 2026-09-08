#!/usr/bin/env python3
"""Import a selected-class checkpoint from public saved host-learn records.

This checks recorded provenance and exact selected accumulator bytes. It does
not rerun or prove the prefix arithmetic, class labels, encoder or FIFO policy.
"""
import argparse
from pathlib import Path
import re
import service as s


def create(operations, cases, at, output, files_output):
    raw = s.regular_bytes(operations, 100_000_000)
    records = {}
    for line_number, line in enumerate(raw.splitlines(), 1):
        row = s.parse(line)
        if row['command'] != 'host-learn':
            continue
        match = re.fullmatch(r'state-(\d+)-[a-f0-9]+\.ct', Path(row['arguments']['out']).name)
        s.need(match is not None, 'recorded_event_filename')
        event = int(match.group(1))
        s.need(event not in records and row['returncode'] == 0 and row['result']['canonical'] is True, 'recorded_event_identity')
        records[event] = {'event': event, 'source_line': line_number, 'record': row}
    prefix = [records[i] for i in range(1, at + 1)]
    by_output = {item['record']['arguments']['out']: item for item in prefix}
    s.need(len(by_output) == len(prefix), 'unique_recorded_outputs')
    selected, files, provenance = {}, {}, {}
    for case in cases:
        origin_bytes = s.regular_bytes(case / 'source_event.json')
        origin = s.parse(origin_bytes)
        label, prior, event = origin['class'], origin['prior_state_event'], origin['event']
        s.need(label not in selected and 0 < prior <= at < event, 'selected_class_checkpoint')
        s.need(origin['public_operation_record'] == records[event]['record'], 'actual_recorded_successor')
        prior_record = records[prior]['record']
        acc = s.regular_bytes(case / 'acc.ct')
        h = s.sha(acc)
        s.need(h == origin['files']['acc']['sha256'] == prior_record['result']['sha256'], 'selected_accumulator_bytes')
        s.need(origin['public_operation_record']['arguments']['acc'] == prior_record['arguments']['out'], 'selected_accumulator_path')
        later_uses = [item['event'] for item in prefix if item['event'] > prior
                      and item['record']['arguments']['acc'] == prior_record['arguments']['out']]
        s.need(not later_uses, 'selected_head_consumed_before_checkpoint')
        # Follow the saved accumulator lineage back to public zero.ct. These are
        # consistency checks on records, not verification of the old arithmetic.
        chain, cursor = [], records[prior]
        while True:
            chain.append(cursor['event'])
            parent = cursor['record']['arguments']['acc']
            if Path(parent).name == 'zero.ct':
                break
            s.need(parent in by_output, 'recorded_parent_exists')
            previous = by_output[parent]
            s.need(previous['event'] < cursor['event']
                   and previous['record']['result']['sha256'] == cursor['record']['result']['acc_sha256'], 'recorded_parent_hash_chain')
            cursor = previous
        selected[label] = {'acc_sha256': h, 'learner_event': prior}
        files[label] = str((case / 'acc.ct').resolve())
        provenance[label] = {'source_event_sha256': s.sha(origin_bytes), 'successor_event': event,
            'selected_prior_event': prior, 'recorded_lineage_events': list(reversed(chain)),
            'later_consumptions_through_checkpoint': later_uses}
    public_records = {'schema': 'public-host-learn-checkpoint-prefix-v1', 'source_path': str(operations),
        'source_sha256': s.sha(raw), 'through_event': at, 'prefix': prefix,
        'selected_successor_records': [records[s.read(case / 'source_event.json')['event']] for case in cases],
        'scope': 'Saved public host-learn records only; other operation types and private files are excluded.'}
    records_path = output.parent / 'checkpoint_public_records.json'
    s.write_json(records_path, public_records)
    checkpoint = {'schema': 'proved-model-checkpoint-v1', 'global_learner_event': at, 'classes': selected,
        'provenance': {'public_records_sha256': s.sha(records_path.read_bytes()),
            'operations_source_sha256': s.sha(raw), 'selected_classes': provenance,
            'scope': 'Imported selected-class checkpoint from recorded public provenance and exact current ciphertext bytes. Earlier arithmetic, labels, FIFO and full original model history are not proved here.'}}
    s.write_json(output, checkpoint)
    s.write_json(files_output, files)
    return {'ok': True, 'checkpoint_sha256': s.sha(output.read_bytes()), 'model_root': s.model_root(selected),
        'global_learner_event': at, 'selected_classes': sorted(selected), 'public_prefix_records': len(prefix)}


if __name__ == '__main__':
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--operations', type=Path, required=True)
    p.add_argument('--case', type=Path, action='append', required=True)
    p.add_argument('--at', type=int, required=True)
    p.add_argument('--out', type=Path, required=True)
    p.add_argument('--initial-files', type=Path, required=True)
    args = p.parse_args()
    print(s.canonical(create(args.operations, args.case, args.at, args.out, args.initial_files)).decode())
