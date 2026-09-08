#!/usr/bin/env python3
"""[EXECUTED] Deterministic public probability/resource arithmetic only."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PQ = HERE.parent


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def ratio(value):
    return {"numerator": str(value.numerator), "denominator": str(value.denominator)}


def main():
    N, w, d, r, T = 16384, 64, 577, 16, 384
    q = 4294967767 * (1 << 256) + 1
    sigma_K, sigma_e, flood = 1 << 25, 1 << 10, 1 << 247
    L, C = w * N, w * N * (8 * sigma_K) * (8 * sigma_e)
    h0, public_rows = d-r, w+d-r
    nu = F(68, 1 << 256)
    U_red = T * (N+d)
    query_budget = 1 << 64
    seed_loss = F(2 * query_budget, 1 << 256)
    cap_loss_bound = F(2 * public_rows, 1 << 5461)
    private_uniform_loss = F(4 * T * U_red, 1 << 512)
    smudge = F(d * C, 2 * flood+1)
    def delta(h):
        return F(2*h+1, 1 << 192) if h else F(0)
    bit_count = (q-1).bit_length()
    word_bytes = (bit_count+7)//8
    chunks = (4*N+1023)//1024+16
    candidates = 1024*chunks
    # Exact cross-multiplied Markov comparison; never draw any candidate.
    cap_markov_below = ((1 << (N+5461)) * pow(3,candidates)
                        < pow(4,candidates))
    assert cap_markov_below
    rows=[]
    for j in range(r+1):
        hj=d-j
        gaussian = (2*h0*L + 2*T*(1+hj)*L) * nu
        regularity = 2*delta(h0)+2*T*delta(hj)
        flooding = 2*T*smudge
        total=(gaussian+regularity+flooding+seed_loss+
               cap_loss_bound+private_uniform_loss)
        assert total < F(1,1<<168)
        rows.append({"coalition_size":j,"missing_setup_rows":h0,
                     "augmented_replaced_rows":hj,
                     "gaussian_coefficient_multiplier":2*h0*L+2*T*(1+hj)*L,
                     "regularity_loss":ratio(regularity),
                     "gaussian_loss":ratio(gaussian),
                     "non_RLWE_loss_below_2_minus_168":True})
    gaussian_key_coefficients=d*L
    gaussian_error_allowance=T*L
    key_bits_per_output=4096*(25+4+256)
    error_bits_per_output=4096*(10+4+256)
    grid=json.loads((PQ/'ring_candidate/hardness/GRID.json').read_text())
    # Search only this known public JSON structure for the repaired profile.
    def dicts(value):
        if isinstance(value,dict):
            yield value
            for sub in value.values(): yield from dicts(sub)
        elif isinstance(value,list):
            for sub in value: yield from dicts(sub)
    profile=next(v for v in dicts(grid) if v.get('N')==N and str(v.get('q'))==str(q))
    assert profile['sigma_K_width_pow2']==25
    assert profile['sigma_e_width_pow2']==10
    out={
        "scope":"[EXECUTED] Deterministic exact rational/integer ledger; no random samples or cryptographic execution",
        "status":"PASS",
        "parameters":{"N":N,"w":w,"d":d,"r":r,"T":T,"q":str(q),
                      "sigma_K":sigma_K,"sigma_e":sigma_e,"F":str(flood),"L":L,"C":C},
        "query_budget":str(query_budget),"RLWE_multiplier":2*T,
        "seed_guess_loss":ratio(seed_loss),
        "public_expansion_cap_loss_bound":{"numerator":2*public_rows,"denominator_power_of_two":5461},
        "private_uniform_cap_loss":ratio(private_uniform_loss),
        "one_challenge_flooding_loss":ratio(smudge),
        "all_coalition_ledgers":rows,
        "public_oracle_resources":{"distinct_rows":public_rows,"word_bytes":word_bytes,
           "candidate_bits":bit_count,"ignored_high_bits":8*word_bytes-bit_count,
           "chunks_per_row":chunks,"candidates_per_row":candidates,
           "full_cap_random_bytes_per_row":word_bytes*candidates,
           "full_cap_random_bytes_all_rows":public_rows*word_bytes*candidates,
           "expected_lazy_preparation_bytes_strict_upper":public_rows*word_bytes*(2*N+1024),
           "cap_markov_bound_below_2_minus_5461":cap_markov_below},
        "strict_target_reduction_resources":{
           "Gaussian_key_coefficients":gaussian_key_coefficients,
           "Gaussian_error_coefficient_allowance":gaussian_error_allowance,
           "private_uniform_outputs":U_red,
           "Gaussian_maximum_attempts":4096*(gaussian_key_coefficients+gaussian_error_allowance),
           "Gaussian_reserved_independent_bits":gaussian_key_coefficients*key_bits_per_output+gaussian_error_allowance*error_bits_per_output,
           "Gaussian_direct_threshold_integer_product_upper":4096*179*(gaussian_key_coefficients+gaussian_error_allowance),
           "private_uniform_reserved_bits_upper":U_red*512*max(bit_count,(2*flood).bit_length())},
        "public_inputs":{"ring_candidate/hardness/GRID.json":digest(PQ/'ring_candidate/hardness/GRID.json')},
        "query_meter":{"Scry_SQL":0,"web_searches":0,"web_opens":0,"PDF_downloads":0},
    }
    (HERE/'CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({"status":"PASS","coalitions":len(rows),
                      "all_non_RLWE_bounds_below_2_minus_168":True,
                      "full_cap_oracle_bytes":out['public_oracle_resources']['full_cap_random_bytes_all_rows'],
                      "private_uniform_outputs_per_reduction":U_red}))


if __name__=='__main__': main()
