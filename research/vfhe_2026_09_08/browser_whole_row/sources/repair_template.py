#!/usr/bin/env python3
"""Migrate a selected row-local AIR template to existing IR2 whole-domain gates.

This changes scope deliberately, not polynomial bodies. Use only for emitter
families whose source constraints are meant to hold on every row. Other IR2
constraints and metadata are preserved. This is not a native-parser theorem.
"""
from pathlib import Path
import argparse, copy, hashlib, json, sys

P = 2013265921
sys.setrecursionlimit(20000)

def object_unique(pairs):
    result = {}
    for k, v in pairs:
        if k in result:
            raise ValueError('duplicate JSON key: '+k)
        result[k] = v
    return result

def natural(x, limit, label):
    if type(x) is not int or not 0 <= x < limit:
        raise ValueError('invalid '+label)
    return x

def localize(e, width):
    if not isinstance(e, dict):
        raise ValueError('arithmetic body is not an object')
    tag = e.get('t')
    if tag == 'var' and set(e) == {'t', 'v'}:
        return {'t': 'loc', 'c': natural(e['v'], width, 'column')}
    if tag == 'const' and set(e) == {'t', 'v'}:
        return {'t': 'const', 'v': natural(e['v'], P, 'canonical constant')}
    if tag in ('add', 'mul') and set(e) == {'t', 'l', 'r'}:
        return {'t': tag, 'l': localize(e['l'], width), 'r': localize(e['r'], width)}
    raise ValueError('unrecognized row-local body syntax: '+str(tag))

def normalize(e):
    tag = e['t']
    if tag == 'loc':
        return {'t': 'var', 'v': e['c']}
    if tag in ('add', 'mul'):
        return {'t': tag, 'l': normalize(e['l']), 'r': normalize(e['r'])}
    return e

def repair(template):
    if template.get('ir') != 2 or type(template.get('trace_width')) is not int:
        raise ValueError('expected IR2 template with a natural trace width')
    width = natural(template['trace_width'], 1 << 63, 'trace width')
    if width == 0 or not isinstance(template.get('constraints'), list):
        raise ValueError('missing trace/constraints')
    result = copy.deepcopy(template)
    changed = []
    for i, old in enumerate(template['constraints']):
        if not isinstance(old, dict) or old.get('t') != 'gate':
            continue
        if set(old) != {'t', 'body'}:
            raise ValueError('unknown gate fields at '+str(i))
        body = localize(old['body'], width)
        if normalize(body) != old['body']:
            raise AssertionError('polynomial changed')
        result['constraints'][i] = {'t': 'window_gate', 'on_transition': False, 'body': body}
        changed.append(i)
    if not changed:
        raise ValueError('no base gates to repair; no implicit pass for unknown profiles')
    rest = copy.deepcopy(result)
    for i in changed:
        rest['constraints'][i] = template['constraints'][i]
    assert rest == template
    return result, changed

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    args = parser.parse_args()
    raw = args.source.read_bytes()
    template = json.loads(raw, object_pairs_hook=object_unique)
    result, changed = repair(template)
    encoded = (json.dumps(result, separators=(',', ':'))+'\n').encode()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open('xb') as f:
        f.write(encoded)
    report = {
        'classification': 'EXECUTED',
        'source': str(args.source.resolve()), 'source_sha256': hashlib.sha256(raw).hexdigest(),
        'output': str(args.output.resolve()), 'output_sha256': hashlib.sha256(encoded).hexdigest(),
        'trace_width': template['trace_width'], 'arithmetic_gates_repaired': len(changed),
        'constraint_count_preserved': len(result['constraints']),
        'normalized_polynomial_bodies_equal': True,
        'all_other_constraints_and_metadata_equal': True,
        'new_scope': 'window_gate/on_transition=false on every row, loc/c leaves',
        'limit': 'selected row-local emitter families; no cryptographic or native-parser proof'}
    report_path = args.output.with_suffix(args.output.suffix+'.repair.json')
    with report_path.open('x') as f:
        json.dump(report, f, indent=2)
        f.write('\n')
    print(json.dumps(report))

if __name__ == '__main__':
    main()
