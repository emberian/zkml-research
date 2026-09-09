"""Exact, fixed degree-two TensorSketch and explicit integer postprocessing.

Pham/Pagh KDD2013 sec4.1: H(i,j)=(h1(i)+h2(j)) mod D, S(i,j)=s1(i)s2(j).
Sec4.2 embeds an inhomogeneous polynomial by appending sqrt(c).
No distributional approximation theorem is asserted for the frozen seed,
quantized/clipped/capped map, or this one empirical evaluation.
"""
import hashlib
import json
import math
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
POLICY = json.loads((HERE / 'policy.json').read_text())
D = POLICY['sketch_dimension']


def _word(domain, index, counter=0):
    payload = json.dumps([POLICY['seed'], domain, index, counter],
                         separators=(',', ':'), ensure_ascii=True).encode()
    return hashlib.shake_256(payload).digest(4)


def tables():
    hashes, signs = [], []
    cutoff = (1 << 32) // D * D
    for factor in [1, 2]:
        h, s = [], []
        for i in range(POLICY['input_dimension'] + 1):
            counter = 0
            while True:
                word = int.from_bytes(_word(f'h{factor}', i, counter), 'little')
                if word < cutoff:
                    h.append(word % D)
                    break
                counter += 1
            s.append(1 if _word(f's{factor}', i)[0] & 1 else -1)
        hashes.append(np.array(h, dtype=np.int64))
        signs.append(np.array(s, dtype=np.int64))
    return hashes, signs


HASHES, SIGNS = tables()


def admitted_original(vector):
    values = list(vector)
    if len(values) != 577 or any(not isinstance(v, (int, np.integer)) or
                                isinstance(v, (bool, np.bool_)) for v in values):
        raise ValueError('Expected577 original integer coordinates')
    if int(values[-1]) != 0 or any(abs(int(v)) > 127 for v in values[:-1]):
        raise ValueError('Expected original signed127 coordinates and trailing zero')
    return np.array(values[:-1] + [POLICY['augmentation_integer']], dtype=np.int64)


def count_sketches(vector):
    augmented = admitted_original(vector)
    counts = []
    for h, s in zip(HASHES, SIGNS):
        out = np.zeros(D, dtype=np.int64)
        np.add.at(out, h, augmented * s)
        counts.append(out)
    return counts


def raw_sketch(vector):
    left, right = count_sketches(vector)
    full = np.convolve(left, right)
    out = full[:D].copy()
    out[:D-1] += full[D:]
    return out


def nearest_even(values, divisor):
    if divisor <= 0:
        raise ValueError('Positive divisor required')
    values = np.asarray(values, dtype=np.int64)
    magnitudes = np.abs(values)
    quotient, remainder = np.divmod(magnitudes, divisor)
    increment = (2 * remainder > divisor) | ((2 * remainder == divisor) &
                                           (quotient % 2 == 1))
    return np.sign(values) * (quotient + increment.astype(np.int64))


def quantize(raw):
    rounded = nearest_even(raw, POLICY['quantization_divisor'])
    clipped = np.clip(rounded, -POLICY['coordinate_clip'], POLICY['coordinate_clip'])
    norm_squared = int(clipped @ clipped)
    limit = POLICY['norm_cap']
    capped = norm_squared > limit * limit
    result = clipped
    if capped:
        denominator = math.isqrt(norm_squared)
        denominator += denominator * denominator < norm_squared
        result = np.sign(clipped) * (np.abs(clipped) * limit // denominator)
    result = np.append(result, 0).astype(np.int64)
    assert max(abs(result)) <= 127 and int(result @ result) <= limit * limit
    return result, {
        'clipped_coordinates': int(np.count_nonzero(rounded != clipped)),
        'norm_capped': bool(capped),
        'rounded_max_abs': int(np.max(abs(rounded))),
        'before_cap_norm_squared': norm_squared,
        'output_norm_squared': int(result @ result),
        'postprocessing_l1_error_numerator': int(np.sum(abs(
            raw - result[:-1] * POLICY['quantization_divisor']))),
    }


def transform(vector):
    return quantize(raw_sketch(vector))[0]


def transform_many(vectors):
    results, stats = [], []
    for vector in vectors:
        result, stat = quantize(raw_sketch(vector))
        results.append(result)
        stats.append(stat)
    return np.array(results, dtype=np.int64), {
        'vectors': len(stats),
        'clipped_vectors': sum(s['clipped_coordinates'] > 0 for s in stats),
        'clipped_coordinates': sum(s['clipped_coordinates'] for s in stats),
        'norm_capped_vectors': sum(s['norm_capped'] for s in stats),
        'max_rounded_abs': max(s['rounded_max_abs'] for s in stats),
        'max_before_cap_norm_squared': max(s['before_cap_norm_squared'] for s in stats),
        'max_output_norm_squared': max(s['output_norm_squared'] for s in stats),
        'max_postprocessing_l1_error_numerator': max(
            s['postprocessing_l1_error_numerator'] for s in stats),
    }
