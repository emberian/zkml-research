"""Honest plaintext adapter into the unchanged canonical field-vector interface."""
import argparse
import hashlib
import json
from pathlib import Path
from basis import load
from kernel import compact, lift

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--registry', type=Path, required=True)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    basis, registry_hash = load(args.registry)
    expected = basis.registry['feature_map']['kernel_sha256']
    if hashlib.sha256(Path(__file__).with_name('kernel.py').read_bytes()).hexdigest() != expected:
        raise ValueError('Registry feature-map mismatch')
    original = json.loads(args.input.read_text())
    values = lift(compact(original))
    # No overwrite: these are plaintext issuer outputs, never secret keys.
    with args.out.open('x') as stream:
        json.dump([v % basis.p for v in values], stream)
        stream.write('\n')
    print(json.dumps({'registry_sha256': registry_hash, 'output_coordinates': len(values),
                      'scope': 'Trusted plaintext feature arithmetic; no cryptography'}))

if __name__ == '__main__':
    main()
