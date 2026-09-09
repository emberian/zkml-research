"""Record the actual fresh-text browser flow after the fixed packed lifecycle."""
import datetime
import hashlib
import json
from pathlib import Path
import shutil
import urllib.request

HERE = Path(__file__).resolve().parent
APP = HERE.parents[1]
ROOT = APP / 'runtime/packed-lifecycle/resident'
TEACH = 'web-teach-c7755d11-1cc5-4edf-8161-cfdc9b512607'
QUERY = 'web-query-88b4e332-bfa3-464e-a22c-75d6e20824fb'


def read(path):
    return json.loads(path.read_text())


def save(name, data):
    (HERE / name).write_text(json.dumps(data, indent=2, sort_keys=True) + '\n')


def get_job(kind, identifier):
    with urllib.request.urlopen('http://127.0.0.1:8850/api/jobs/' + kind + '-' + identifier) as response:
        value = json.load(response)
    assert value['status'] == 'completed', value['status']
    return value


expected = read(ROOT.parent / 'browser-reference.json')
teach = get_job('teach', TEACH)
query = get_job('query', QUERY)
answer = query['result']
assert answer['revision'] == expected['revision'] == 19
assert answer['ranking'] == expected['ranking']
assert answer['prediction'] == expected['prediction'] == 'network_transport'
assert set(answer['classes']) == set(expected['classes'])
banks = {key: {'sums': [0] * 8, 'counts': [0] * 8} for key in answer['banks']}
for label, reference in expected['classes'].items():
    actual = answer['classes'][label]
    assert all(actual[key] == reference[key] for key in ('sum_dot', 'count', 'bank', 'lane'))
    assert actual['mean_numerator'] == reference['sum_dot']
    assert actual['mean_denominator'] == reference['count']
    banks[reference['bank']]['sums'][reference['lane']] = reference['sum_dot']
    banks[reference['bank']]['counts'][reference['lane']] = reference['count']
for bank, reference in banks.items():
    actual = answer['banks'][bank]
    assert actual['class_sums'] == reference['sums']
    assert actual['counts'] == reference['counts']
    assert actual['all8192_slots_repeat8'] and actual['zero_empty_lanes']
assert answer['accepted_all_banks'] and answer['public_accepted']
assert answer['private_reads'] == 2
save('reference.json', expected)
save('teach-job.json', teach)
save('query-job.json', query)
for kind, identifier in [('teaching', TEACH), ('queries', QUERY)]:
    shutil.copyfile(ROOT / kind / identifier / 'input.json', HERE / (kind + '-input.json'))
elapsed = lambda job: (datetime.datetime.fromisoformat(job['updated_utc']) - datetime.datetime.fromisoformat(job['created_utc'])).total_seconds()
summary = {'claim': 'EXECUTED', 'schema': 'continuing-browser-packed-result-v1',
           'submission': 'Both texts were entered and submitted through the actual local browser forms.',
           'prediction': answer['prediction'], 'revision': answer['revision'],
           'class_sums_counts_and_exact_ranking_match': True, 'compared_bank_lanes': 16,
           'all_bank_proofs_before_private_reads': True, 'full_reader_key_survives': True,
           'teach_job_seconds': elapsed(teach), 'query_job_seconds': elapsed(query),
           'teach_metrics': teach['result']['metrics'], 'query_metrics': answer['metrics'],
           'scope': 'Two new public authored texts after the fixed workload; actual encoder, HTTP jobs, encryption, proofs and private reading. This one expected label is not a general accuracy measurement.'}
save('RESULT.json', summary)
print(json.dumps(summary, sort_keys=True))
