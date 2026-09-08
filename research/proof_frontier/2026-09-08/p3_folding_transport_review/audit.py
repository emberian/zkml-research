#!/usr/bin/env python3
"""Bounded artifact/patch checks and pure arithmetic. Never invokes Lean or Rust."""
import hashlib
import itertools
import json
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
AUTHOR = HERE.parent / 'p3_folding_transport'
COMPANION = Path('/Users/ember/dev/minidregg')
BASE = '6937394e1dc2c2aaff986c7d4b3a258aca5d16fd'
P = 2013265921
ZERO = (0, 0, 0, 0)
ONE = (1, 0, 0, 0)
COMMANDS = []


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(args, cwd):
    r = subprocess.run(args, cwd=cwd, capture_output=True, text=True, check=False)
    COMMANDS.append(dict(command=args, cwd=str(cwd), exit_code=r.returncode,
                         stdout=r.stdout, stderr=r.stderr))
    assert r.returncode == 0, COMMANDS[-1]
    return r.stdout


def add(a, b):
    return tuple((x + y) % P for x, y in zip(a, b))


def scale(a, b):
    return tuple(x * b % P for x in a)


def sub(a, b):
    return add(a, scale(b, -1))


def mul(a, b):
    # Direct basis multiplication: U^(i+j) = 11^floor((i+j)/4)*U^((i+j)%4).
    out = [0] * 4
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[(i + j) % 4] += x * y * (11 if i + j >= 4 else 1)
    return tuple(x % P for x in out)


def power(a, n):
    r = ONE
    while n:
        if n & 1:
            r = mul(r, a)
        a, n = mul(a, a), n // 2
    return r


def evaluate(poly, x):
    # Sum of monomials, independent of the author's Horner loop.
    return tuple(sum(c[j] * pow(x, i, P) for i, c in enumerate(poly)) % P for j in range(4))


def rev(index, bits):
    return sum(((index >> i) & 1) << (bits - i - 1) for i in range(bits))


def root(bits):
    return pow(31, (P - 1) // (1 << bits), P)


def word(poly, bits):
    return [evaluate(poly, pow(root(bits), rev(i, bits), P)) for i in range(1 << bits)]


def coefficient_fold(poly, beta, arity):
    out = []
    for offset in range(0, len(poly), arity):
        value = ZERO
        for j, c in enumerate(poly[offset:offset + arity]):
            value = add(value, mul(c, power(beta, j)))
        out.append(value)
    return out


def row_fold(row, row_index, bits, beta):
    arity = len(row)
    a = arity.bit_length() - 1
    start = pow(root(bits), rev(row_index, bits - a), P)
    points = [start * pow(root(a), rev(i, a), P) % P for i in range(arity)]
    answer = ZERO
    for i, value in enumerate(row):
        weight = ONE
        for j, point in enumerate(points):
            if i != j:
                weight = scale(mul(weight, sub(beta, (point, 0, 0, 0))),
                               pow((points[i] - point) % P, -1, P))
        answer = add(answer, mul(value, weight))
    return answer


def independent_controls():
    index_cases = composition_cases = 0
    for bits in range(9):
        for q in range(1 << bits):
            for total in range(bits + 1):
                assert rev(q >> total, bits - total) == rev(q, bits) % (1 << (bits - total))
                index_cases += 1
                for first in range(total + 1):
                    assert rev(q >> first, bits - first) % (1 << (bits - total)) == rev(q >> total, bits - total)
                    composition_cases += 1
    assert rev(181 >> 3, 5) == 13 != 181 % 32
    actual = {0, (1 << 20) - 1}
    for j in range(20):
        actual.update(x for x in ((1 << j) - 1, 1 << j, (1 << j) + 1) if x < 1 << 20)
    for q in actual:
        for j in range(19):
            assert rev(q >> 1, 19) % (1 << (19 - j)) == rev(q >> (j + 1), 19 - j)
    assert root(27) == 440564289 and root(20) == 195061667
    assert power((0, 1, 0, 0), 4) == (11, 0, 0, 0)
    # Same presentation, different full-degree coefficients and extension challenge.
    poly = [((i ** 3 + 17) % P, (5 * i + 11) % P, (i * i + 23) % P, (7 * i ** 3 + 31) % P)
            for i in range(32)]
    values = word(poly, 5)
    fold_rows = 0
    for beta in (ZERO, (P - 1, 0, 0, 0), (2, 3, 5, 7)):
        for a in (1, 2, 3):
            arity = 1 << a
            expected = word(coefficient_fold(poly, beta, arity), 5 - a)
            for r, value in enumerate(expected):
                assert row_fold(values[r * arity:(r + 1) * arity], r, 5, beta) == value
                fold_rows += 1
    # Independently recompute old and new twiddles from primitive roots at each pass.
    twiddle_cases = 0
    for bits in range(2, 9):
        old = [pow(2 * pow(root(bits), rev(i, bits - 1), P), -1, P) for i in range(1 << (bits - 1))]
        for j in range(1 << (bits - 2)):
            new = pow(2 * pow(root(bits - 1), rev(j, bits - 2), P), -1, P)
            assert 2 * old[2 * j] ** 2 % P == new
            twiddle_cases += 1
    # Different mixed-height example: 64 -> 8 -> 2, two injections, all 64 queries.
    heights = [6, 3, 1]
    polys = {h: [(i + h, 3 * i + 2, i * i + 5, 7 * i + h) for i in range(1 << (h - 1))] for h in heights}
    values = word(polys[6], 6)
    current_poly = polys[6]
    rounds = []
    for bits, next_bits, beta in ((6, 3, (13, 2, 1, 9)), (3, 1, (7, 11, 3, 5))):
        arity = 1 << (bits - next_bits)
        folded = coefficient_fold(current_poly, beta, arity)
        weight = power(beta, arity)
        current_poly = [add(c, mul(weight, d)) for c, d in zip(folded, polys[next_bits])]
        expected = word(current_poly, next_bits)
        injected = word(polys[next_bits], next_bits)
        rounds.append((bits, arity, beta, values, injected, expected))
        values = expected
    for query in range(64):
        index = query
        current = rounds[0][3][query]
        for bits, arity, beta, before, injected, after in rounds:
            parent, member = divmod(index, arity)
            row = before[parent * arity:(parent + 1) * arity]
            siblings = row[:member] + row[member + 1:]
            reconstructed = siblings[:member] + [current] + siblings[member:]
            assert reconstructed == row
            current = add(row_fold(reconstructed, parent, bits, beta), mul(power(beta, arity), injected[parent]))
            assert current == after[parent]
            index = parent
        assert current == current_poly[0]
    return dict(index_cases=index_cases, composition_cases=composition_cases,
                actual20_boundary_queries=len(actual), actual20_round_cases=len(actual) * 19,
                full_degree_ext4_row_equalities=fold_rows, twiddle_recurrence_cases=twiddle_cases,
                mixed_height_queries=64, mixed_height_rounds=128,
                mixed_height_schedule=[8, 4], all_passed=True)


def main():
    assert sha(AUTHOR / 'MANIFEST.json') == '17b4f5a087248c521eb25e7ca8d44ee859f67f2a22dac7a54dfaca43602327f5'
    formal = AUTHOR / 'formal'
    checked = []
    for base in (AUTHOR, formal):
        for name, digest in json.loads((base / 'MANIFEST.json').read_text())['files'].items():
            assert sha(base / name) == digest, name
            checked.append(dict(path=str((base / name).relative_to(AUTHOR)), sha256=digest))
    sources = json.loads((AUTHOR / 'SOURCES.json').read_text())['sources']
    for name, data in sources.items():
        assert sha(Path(name)) == data['sha256'], name
    verification = json.loads((formal / 'verification.json').read_text())
    modules = list(verification['source_sha256'])
    census = []
    for module in modules:
        text = (formal / 'src' / module).read_text()
        code = re.sub(r'/\-.*?\-/|--[^\n]*', '', text, flags=re.S)
        assert not re.search(r'\b(sorry|sorryAx|axiom|admit|native_decide|unsafe)\b', code)
        names = re.findall(r'^theorem\s+(\w+)', code, re.M)
        pins = re.findall(r"/-- info: '([^']+)' depends on axioms: \[([^\]]*)\] -/\s*#guard_msgs \(whitespace := lax\) in #print axioms (\w+)", text)
        assert names == [name for _, _, name in pins]
        expected = [x for x in verification['census'] if x['module'] == module]
        assert [(q, a.split(', ')) for q, a, _ in pins] == [(x['name'], x['axioms']) for x in expected]
        census += expected
        log = json.loads((formal / verification['clean_lean_checks'][module]).read_text())
        assert log['exit_code'] == 0 and log['stdout'] == '' and log['stderr'] == ''
        assert log['source_sha256'] == log['source_sha256_after'] == sha(formal / 'src' / module)
        assert sha((formal / verification['clean_lean_checks'][module]).with_suffix('.lean')) == sha(formal / 'src' / module)
    assert len(census) == 15
    patch = formal / 'minidregg-p3-query-transport.patch'
    assert sha(patch) == 'a853d61feffbe71802b46ddaf086b93a378246116abf429feef5fed870d48bca'
    touched = re.findall(r'^\+\+\+ b/(.+)$', patch.read_text(), re.M)
    assert set(touched) == {'Theory.lean', 'Selvage.lean', *modules}
    base_pins = {}
    with tempfile.TemporaryDirectory(dir=HERE, prefix='patch_') as tmp:
        tmp = Path(tmp)
        originals = {}
        for umbrella in ('Theory.lean', 'Selvage.lean'):
            originals[umbrella] = run(['git', 'show', f'{BASE}:{umbrella}'], COMPANION)
            (tmp / umbrella).write_text(originals[umbrella])
            base_pins[umbrella] = sha(tmp / umbrella)
        run(['git', 'init', '-q'], tmp)
        run(['git', 'apply', '--check', str(patch)], tmp)
        run(['git', 'apply', str(patch)], tmp)
        for module in modules:
            assert (tmp / module).read_bytes() == (formal / 'src' / module).read_bytes()
        for umbrella, module in [('Theory.lean', 'Theory.BitReverseFriTransport'), ('Selvage.lean', 'Selvage.P3FriQueryTransport')]:
            assert (tmp / umbrella).read_text() == originals[umbrella].rstrip('\n') + '\n\nimport ' + module + '\n'
    # Replay the author's pure checker in an owned temporary directory; retain output only.
    with tempfile.TemporaryDirectory(dir=HERE, prefix='arithmetic_') as tmp:
        tmp = Path(tmp)
        for name in ('check_transport.py', 'SOURCES.json'):
            shutil.copyfile(AUTHOR / name, tmp / name)
        stdout = run([sys.executable, str(tmp / 'check_transport.py')], tmp)
        replay = json.loads(stdout)
        expected = json.loads((AUTHOR / 'RESULTS.json').read_text())
        assert {k: v for k, v in replay.items() if k != 'seconds'} == {k: v for k, v in expected.items() if k != 'seconds'}
        (HERE / 'author_replay.json').write_text(json.dumps(replay, indent=2) + '\n')
    extra = independent_controls()
    result = dict(all_passed=True, manifest_entries_checked=len(checked),
                  unique_artifacts_checked=len({x['path'] for x in checked}),
                  source_files_checked=len(sources), theorem_pins_checked=len(census),
                  exact_patch_replay=True, base_umbrella_pins=base_pins,
                  author_replay_matches_except_seconds=True, independent_controls=extra,
                  lean_runs=0, rust_runs=0, crypto_protocol_runs=0)
    (HERE / 'RESULTS.json').write_text(json.dumps(result, indent=2) + '\n')
    # Store concise command records; git-show bodies are already pinned, not copied public source.
    for command in COMMANDS:
        if command['command'][:2] == ['git', 'show']:
            command['stdout'] = '<baseline umbrella bytes checked and hashed>'
        if command['command'][0] == sys.executable:
            command['stdout'] = '<retained in author_replay.json>'
    (HERE / 'commands.json').write_text(json.dumps(COMMANDS, indent=2) + '\n')
    (HERE / 'INPUTS.json').write_text(json.dumps(dict(artifacts=checked, sources=sources), indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
