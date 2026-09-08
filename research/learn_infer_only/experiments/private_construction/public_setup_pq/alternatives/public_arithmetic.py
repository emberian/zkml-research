"""Public integer inequalities and storage only: no crypto/sampling/estimator."""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
D, R, W, T, P = 577, 16, 32, 384, 28_439_893
X = (P - 1) // 2
N, M, QLO_BITS, QHI_BITS = 1024, 16384, 288, 289
SIGMA_K_BITS, SIGMA_E_BITS, F_BITS = 32, 10, 244
BK, BE, FLOOD = 8 * 2**SIGMA_K_BITS, 8 * 2**SIGMA_E_BITS, 2**F_BITS
DENOM = D * X
DELTA_LO = 2**QLO_BITS // DENOM
PHASE = FLOOD + M * BK * BE
assert 2 * W * X < DENOM
assert 2 * W * PHASE < DELTA_LO
assert 2 * W * (DELTA_LO * X + PHASE) < 2**QLO_BITS
# General MP expectation bound with eps0=2^-192, etaZ<8, sigmaK=2^32.
# etaZ^2 < (ceil_log2 M + 194)/4 < 64, since ln2/pi < 1/4.
assert (M - 1).bit_length() + 194 < 4 * 64
regularity_exponents = {
    str(ncols): QHI_BITS * ncols - 29 * M for ncols in [N, N + 1]
}
assert all(v < -193 for v in regularity_exponents.values())
# S<2^-193, R<2^-191; rank failure is far below 2^-192.
# Thus delta_h < h*2^-189 for h>=1, by the general expectation lemma.
regularity_num = 2 * (D - R) + 2 * T * D
smudge_num = 2 * T * D
smudge_den_bits = F_BITS + 1 - 62  # M BK BE = 2^62
assert M * BK * BE == 2**62
assert smudge_num < 2**(smudge_den_bits - 164)
assert regularity_num < 2**(189 - 170)
# Elementary prior tail: Pr(|G|>=8 sigma)<=3 sigma 2^-256.
key_tail_num = 3 * D * M
key_tail_den_bits = 256 - SIGMA_K_BITS
error_tail_num = 3 * M
error_tail_den_bits = 256 - SIGMA_E_BITS
assert key_tail_num < 2**(key_tail_den_bits - 199)
assert error_tail_num < 2**(error_tail_den_bits - 230)
# Even paying both tails for all 2T switches remains <2^-188.
assert 2 * T * key_tail_num < 2**(key_tail_den_bits - 189)
assert 2 * T * error_tail_num < 2**(error_tail_den_bits - 220)
assert 2**56 + 2**50 + 2**31 + 1 < 2**57
def packed(entries, bits):
    return (entries * bits + 7) // 8
ct_entries = M + D
pk_entries = (M + D) * N
key_bits = (BK - 1).bit_length() + 1
assert key_bits == 36
profiles = []
for s in [16, 32, 155]:
    lam = s * s
    nn, ll, lp, qbits = 11 * lam, lam * lam, lam * lam - 2 * lam, 7 * s + 1
    # Bertrand interval gives a prime 2^(7s)<q<2^(7s+1).
    profiles.append({
        'sqrt_lambda': s, 'lambda': lam, 'n': nn, 'l': ll, 'l_prime': lp,
        'theorem3_required_l_prime_lower': 2 * nn * (7*s),
        'q_bit_upper': qbits, 'theorem3_required_l_prime_upper': 2 * nn * qbits,
        'theorem3_sufficient_check': lp >= 2 * nn * qbits,
        'single_block_ciphertext_byte_upper': packed(ll + D, qbits),
        'single_block_public_key_byte_upper': packed((ll + D) * nn, qbits),
        'single_block_encrypt_products': (ll + D) * nn,
    })
out = {
    'scope': 'Public arithmetic only. Derived conditional tuple; no security level or crypto execution.',
    'fixture': {'d': D, 'r': R, 'window': W, 'issued_inputs': T, 'p': P,
                'centered_coordinate_bound': X, 'window_centered_sum_bound': W * X,
                'scale_denominator': DENOM},
    'derived': {'n': N, 'l': M, 'q_prime_interval_exponents': [QLO_BITS,QHI_BITS],
                'q_bit_upper': QHI_BITS, 'sigma_K_exponent': SIGMA_K_BITS,
                'sigma_LWE_exponent': SIGMA_E_BITS, 'flood_exponent': F_BITS,
                'key_tail_cut': 8, 'error_tail_cut': 8,
                'BK': BK, 'BL': BE, 'delta_lower': DELTA_LO,
                'individual_phase_error_bound': PHASE,
                'correctness_2WE_less_delta': 2*W*PHASE < DELTA_LO,
                'regularity_S_exponent_upper': regularity_exponents,
                'regularity_total_numerator_over_2pow189': regularity_num,
                'smudge_total_numerator': smudge_num,
                'smudge_total_denominator_power': smudge_den_bits,
                'statistical_total_less_2pow_minus163': True,
                'LWE_advantage_multiplier': 2*T,
                'ciphertext_entries': ct_entries, 'public_key_entries': pk_entries,
                'ciphertext_byte_upper': packed(ct_entries,QHI_BITS),
                'public_key_byte_upper': packed(pk_entries,QHI_BITS),
                'recipient_key_high_probability_bytes': packed(M,key_bits),
                'all_recipient_keys_high_probability_bytes': packed(R*M,key_bits),
                'encryption_modular_products': pk_entries,
                'decryption_modular_products_per_coordinate': M,
                'scalar_add_residue_additions': ct_entries,
                'live_66_ciphertexts_byte_upper': 66*packed(ct_entries,QHI_BITS),
                'T384_ciphertexts_byte_upper': T*packed(ct_entries,QHI_BITS)},
    'source_table_mechanical_profiles_not_security_parameters': profiles,
}
text = json.dumps(out, indent=2) + '\n'
(HERE/'results.json').write_text(text)
print(text, end='')
