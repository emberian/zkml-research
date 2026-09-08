#!/usr/bin/env python3
"""Independent compact-TMRE source and finite index/runtime controls."""
from pathlib import Path
import hashlib
import json
import subprocess

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[4]
AUTHOR = ROOT / 'research/learn_infer_only/experiments/pq_composition/base_fe_audit/compact_tmre'
EXPECTED = 'af5e6acb0feb544b739c08838dcc8c88dff63244d33c16e18792d992e662a445'


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def author_state():
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(AUTHOR.rglob('*'))
            if p.is_file() and '__pycache__' not in p.parts}


def main():
    before = author_state()
    assert digest(AUTHOR / 'COMPACT_TMRE.md') == EXPECTED
    pins = json.loads((AUTHOR / 'inputs.json').read_text())['inputs']
    verified, extractions = [], []
    (BASE / 'texts').mkdir(exist_ok=True)
    for row in pins:
        p = Path(row['path'])
        assert digest(p) == row['sha256'], p
        verified.append({'path': str(p), 'sha256': digest(p)})
        if p.suffix == '.pdf':
            stem = p.parent.name + '_' + p.stem
            out = BASE / 'texts' / (stem + '.txt')
            argv = ['pdftotext', '-layout', str(p), str(out)]
            run = subprocess.run(argv, capture_output=True, text=True)
            assert run.returncode == 0, run.stderr
            text_pin = next(r for r in pins if r['path'].endswith('/' + stem + '.txt'))
            assert digest(out) == text_pin['sha256'], out
            extractions.append({'argv': argv, 'exit_code': run.returncode,
                                'stdout': run.stdout, 'stderr': run.stderr,
                                'sha256': digest(out)})

    steps, off_point_checks, bad_tails, coefficient_rows = 0, 0, 0, []
    for length in range(1, 65):
        domain = 1 << max(1, (length - 1).bit_length())
        # Explicit tags for encodings, not only their decoded output bits.
        tape = tuple(('tape', i) for i in range(domain))

        def hybrid(j, i):
            return ('fixed',) if i >= length else ('H', int(i < j), i, tape[i])

        for j in range(length):
            full = tuple(hybrid(j, i) for i in range(domain))
            point = full[j]
            punctured = {i: tape[i] for i in range(domain) if i != j}
            reconstructed = tuple(point if i == j else
                                  (('fixed',) if i >= length else
                                   ('H', int(i < j), i, punctured[i]))
                                  for i in range(domain))
            assert reconstructed == full
            changed = [i for i in range(domain) if hybrid(j, i) != hybrid(j + 1, i)]
            assert changed == [j]
            steps += 1
            off_point_checks += domain - 1
        assert tuple(hybrid(length, i) for i in range(domain)) == tuple(
            ('H', 1, i, tape[i]) if i < length else ('fixed',) for i in range(domain))
        if length < domain:
            # Equal decoded out-of-range bits do not imply equal encodings.
            assert ('H', 0, length, tape[length]) != ('H', 1, length, tape[length])
            bad_tails += 1
        # Count the actual five-step sequence, then compare coefficients.
        sequence = ['O', 'P', 'H', 'P', 'O'] * length
        coeffs = {name: sequence.count(name) for name in ['O', 'P', 'H']}
        assert coeffs == {'O': 2 * length, 'P': 2 * length, 'H': length}
        coefficient_rows.append({'output_bits': length, 'coefficients': coeffs})

    # This finite arithmetic illustrates the proved quantifier gap in REPORT,
    # and is not a lower bound on arbitrary encodings or an H execution.
    clocks = [{'original_actual_steps': 2, 'declared_T': 1 << exponent,
               'pad_to_declared_clock_steps': 1 << exponent,
               'padding_ratio': (1 << exponent) // 2}
              for exponent in [4, 8, 16, 32]]
    assert all(r['pad_to_declared_clock_steps'] > r['original_actual_steps'] for r in clocks)
    after = author_state()
    assert before == after
    result = {
        'scope': 'Source identity, finite exact generator indexing/puncturing and clock arithmetic only; no cryptography or adversary runtime',
        'reviewed_note_sha256': EXPECTED, 'source_pins': verified,
        'extractions': extractions,
        'checks': {'output_lengths': 64, 'adjacent_index_hybrids': steps,
                   'off_point_equalities': off_point_checks,
                   'out_of_range_encoding_negative_controls': bad_tails,
                   'author_files_unchanged': True, 'author_file_count': len(before)},
        'clock_gap_controls': clocks, 'coefficient_rows': coefficient_rows,
        'author_hashes_before': before, 'author_hashes_after': after,
        'activity': {'local_pdf_extractions': len(extractions), 'pdf_downloads': 0,
                     'web_queries': 0, 'scry_sql_queries': 0, 'scry_schema_queries': 0,
                     'kagi_queries': 0, 'crypto_runtime': 0, 'attack_runtime': 0}}
    (BASE / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result['checks'], indent=2))


if __name__ == '__main__':
    main()
