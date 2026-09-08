"""Pure algebra/adapter controls; does not evaluate utility or sample crypto."""
import itertools
import json
from pathlib import Path
from tempfile import TemporaryDirectory
import subprocess
import sys
import kernel as K

HERE = Path(__file__).resolve().parent

def main():
    checked = 0
    # Exhaustive two-coordinate cross-term controls embedded in the 32D map.
    for a, b, c, d in itertools.product(range(-4, 5), repeat=4):
        x = [a, b] + [0] * 30
        q = [c, d] + [0] * 30
        assert sum(v * w for v, w in zip(K.lift(x), K.query_coefficients(q))) == K.kernel(x, q)
        checked += 1
    x = [4] * 32
    q = [4] * 32
    assert K.kernel(x, q) == 262144
    assert max(K.lift(x)) == 16 and max(K.query_coefficients(q)) == 32
    assert 2 * K.kernel(x, q) == 524288
    assert 32 * K.kernel(x, q) == 8388608 < 28439893 // 2
    assert K.compact([0] * 577) == [0] * 32
    assert K.compact([127] + [0] * 576) == [4 * row[0] for row in K.SIGNS]
    # Synthetic issuer I/O only; no cached benchmark scores are reevaluated.
    with TemporaryDirectory(prefix='kernel-public-algebra-') as temp:
        temp = Path(temp)
        source = [127] + [0] * 576
        (temp / 'input.json').write_text(json.dumps(source))
        cmd = [sys.executable, '-B', str(HERE / 'issuer.py'), '--registry', str(HERE / 'registry.json'),
               '--input', str(temp / 'input.json'), '--out', str(temp / 'out.json')]
        run = subprocess.run(cmd, check=True, capture_output=True, text=True)
        assert json.loads((temp / 'out.json').read_text()) == [v % 28439893 for v in K.encode_source(source)]
        assert json.loads(run.stdout)['output_coordinates'] == 577
    result = {'status': 'PASS', 'exhaustive_two_coordinate_identity_controls': checked,
              'tight_dimension32_bound_controls': True, 'zero_and_one_source_coordinate_controls': True,
              'synthetic_plaintext_issuer_cli': True, 'benchmark_utility_reevaluations': 0,
              'cryptographic_runs': 0}
    (HERE / 'ALGEBRA.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result))

if __name__ == '__main__':
    main()
