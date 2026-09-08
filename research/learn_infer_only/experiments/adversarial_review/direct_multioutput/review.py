#!/usr/bin/env python3
"""Independent source identities and finite admissibility controls, not crypto."""
from pathlib import Path
import hashlib
import json
import subprocess

BASE = Path(__file__).resolve().parent
ROOT = BASE.parents[4]
AUTHOR = ROOT / 'research/learn_infer_only/experiments/pq_composition/base_fe_audit/direct_multioutput'
EXPECTED = 'a72f903330f4b4504947cb2cd49592619912f168b375a8abb4532fd373caf828'


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def author_state():
    return {str(p.relative_to(ROOT)): digest(p) for p in sorted(AUTHOR.rglob('*'))
            if p.is_file() and '__pycache__' not in p.parts}


def main():
    before = author_state()
    assert digest(AUTHOR / 'DIRECT_MULTIOUTPUT.md') == EXPECTED
    pins = json.loads((AUTHOR / 'inputs.json').read_text())['sources']
    verified, extractions = [], []
    (BASE / 'texts').mkdir(exist_ok=True)
    for row in pins:
        p = Path(row['path'])
        if not p.is_absolute():
            p = ROOT / p
        assert digest(p) == row['sha256'], p
        verified.append({'path': str(p), 'sha256': digest(p)})
        if p.suffix == '.pdf':
            out = BASE / 'texts' / (p.parent.name + '_' + p.stem + '.txt')
            argv = ['pdftotext', '-layout', str(p), str(out)]
            run = subprocess.run(argv, capture_output=True, text=True)
            assert run.returncode == 0, run.stderr
            assert digest(out) == row['extract_sha256'], out
            extractions.append({'argv': argv, 'exit_code': run.returncode,
                                'stdout': run.stdout, 'stderr': run.stderr,
                                'sha256': digest(out)})

    # Every deterministic Boolean decoder on L-bit strings, L <= 3.
    # Distinct outputs force some differing input coordinate, regardless of
    # correlations in the process that generated those two strings.
    opposite_pairs = 0
    for width in range(1, 4):
        size = 1 << width
        for truth_table in range(1 << size):
            zero = [z for z in range(size) if not ((truth_table >> z) & 1)]
            one = [z for z in range(size) if (truth_table >> z) & 1]
            for z in zero:
                for o in one:
                    assert z != o and any(((z >> i) & 1) != ((o >> i) & 1)
                                          for i in range(width))
                    opposite_pairs += 1

    # The source hidden-branch replacement preserves the sole selected label
    # at each independent (output, ciphertext-bit) instance for arbitrary
    # selected-bit vectors. Reusing an instance with both selections fails it.
    selections = 0
    for outputs in range(1, 4):
        for width in range(1, 4):
            count = outputs * width
            for bits in range(1 << count):
                for slot in range(count):
                    selected = (bits >> slot) & 1
                    old = (('label', slot, 0), ('label', slot, 1))
                    new = (old[selected], old[selected])
                    assert old[selected] == new[selected]
                    assert old[1 - selected] != new[1 - selected]
                selections += 1
    old, shared_replacement = ('L0', 'L1'), ('L0', 'L0')
    assert old[0] == shared_replacement[0]
    assert old[1] != shared_replacement[1]

    # Pointwise union inequality: no independence premise can enter here.
    masks = 0
    for count in range(1, 13):
        for mask in range(1 << count):
            assert int(bool(mask)) <= mask.bit_count()
            masks += 1

    after = author_state()
    assert before == after
    result = {
        'scope': 'Source identity, deterministic label-game and union-bound controls only; no cryptography, encryption, model, or adversary runtime',
        'reviewed_note_sha256': EXPECTED, 'source_pins': verified,
        'extractions': extractions,
        'checks': {'opposite_output_decoder_pairs': opposite_pairs,
                   'independent_label_selection_vectors': selections,
                   'shared_label_game_negative_control': 'both issued selections cannot preserve the changed branch',
                   'pointwise_union_masks': masks,
                   'author_files_unchanged': True, 'author_file_count': len(before)},
        'author_hashes_before': before, 'author_hashes_after': after,
        'activity': {'local_pdf_extractions': len(extractions), 'pdf_downloads': 0,
                     'web_queries': 0, 'scry_sql_queries': 0, 'scry_schema_queries': 0,
                     'kagi_queries': 0, 'crypto_runtime': 0, 'attack_runtime': 0}}
    (BASE / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result['checks'], indent=2))


if __name__ == '__main__':
    main()
