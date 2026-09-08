#!/usr/bin/env python3
"""[EXECUTED] Deterministic query-loss and simulation-resource arithmetic."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
PQ=HERE.parent

def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def read_ratio(row):return F(int(row['numerator']),int(row['denominator']))

def main():
    oldpath=PQ/'ring_seed_security_successor/CHECKS.json'
    old=json.loads(oldpath.read_text())
    worst=old['all_coalition_ledgers'][0]
    assert worst['coalition_size']==0
    T=384; Q=1<<64
    # Monotonicity in d-j makes coalition j=0 sufficient; no repeated grid.
    cap=F(1250,1<<5461)
    base=(read_ratio(worst['regularity_loss'])+
          read_ratio(worst['gaussian_loss'])+
          2*T*read_ratio(old['one_challenge_flooding_loss'])+
          read_ratio(old['private_uniform_cap_loss'])+cap)
    assert base<F(1,1<<168)
    rows=[]
    for seed_bytes,status in [(32,'actual frozen transport'),
                              (48,'future unsupported seed/format'),
                              (64,'future transport; expander alone accepts length')]:
        lam=8*seed_bytes
        # g(Q,2^-lambda) twice, then two privacy-bit worlds.
        # sqrt(Q)=2^32 exactly, so no floating root certificate is needed.
        leading_exp=lam//2-34
        correction_exp=lam-65
        quantum=F(1,1<<leading_exp)+F(1,1<<correction_exp)
        assert quantum==4*F(1<<32,1<<(lam//2))+2*F(Q,1<<lam)
        rows.append({'seed_bytes_each':seed_bytes,'lambda_each':lam,'encoding_status':status,
                     'two_world_programming_exact_upper':f'2^-{leading_exp} + 2^-{correction_exp}',
                     'programming_upper_decimal_display_only':float(quantum),
                     'base_statistical_upper':'2^-168',
                     'full_non_RLWE_upper_below_2_minus_168':base+quantum<F(1,1<<168)})
    chunks=80; chunk_bytes=1024*37; A_rows=64; missing_rows=561
    n_example=8*466+9
    ell_example=8*chunk_bytes
    m_example=1 << (max(n_example,65)-1).bit_length()
    lanes=(ell_example+m_example-1)//m_example
    k=2*Q
    resource={
      'source_only_block_oracles':{
        'A_output_bytes':A_rows*chunks*chunk_bytes,
        'A_output_bits':8*A_rows*chunks*chunk_bytes,
        'missing_output_bytes':missing_rows*chunks*chunk_bytes,
        'missing_output_bits':8*missing_rows*chunks*chunk_bytes,
        'queries_to_target_family_per_adversarial_query':1,
        'honest_A_reads_counted_against_missing_oracle':0},
      'ordinary_domain_wrapper':{
        'table_chunk_entries':(A_rows+missing_rows)*chunks,
        'table_bytes':(A_rows+missing_rows)*chunks*chunk_bytes,
        'table_bits':8*(A_rows+missing_rows)*chunks*chunk_bytes,
        'fallback_queries_per_adversarial_query':1,
        'finite_independence_degree_parameter_k':'max(1,2Q)',
        'example_input_cap_bytes':466,'example_address_width_bits':n_example,
        'example_max_output_bits':ell_example,'example_field_degree_m':m_example,
        'example_output_lanes':lanes,
        'at_Q_2_pow_64_independent_field_coefficient_bits':str(k*lanes*m_example),
        'at_Q_2_pow_64_compute_uncompute_lane_polynomial_evaluations':str(2*Q*lanes),
        'at_Q_2_pow_64_Horner_field_step_upper_scale':str(2*Q*lanes*k),
        'at_Q_2_pow_64_schoolbook_bit_work_scale_without_gate_constant':str(2*Q*lanes*k*m_example*m_example),
        'no_QRAM_overlay_scan_bit_work_scale_per_query_without_gate_constant':
             (A_rows+missing_rows)*chunks*(n_example+ell_example),
        'example_limits':'Larger input/output registers require corresponding n,ell,m; field modulus must be public/certified; scales are not exact gate counts'}
    }
    assert resource['source_only_block_oracles']['missing_output_bits']==13603307520
    assert resource['ordinary_domain_wrapper']['table_bytes']==1894400000
    out={'scope':'[EXECUTED] Public exact arithmetic only; no quantum, Gaussian, crypto or estimator execution',
         'status':'PASS','source_query_budget_each_pre_stage':str(Q),
         'RLWE_multiplier':768,'base_worst_coalition':0,
         'base_non_RLWE_loss_including_caps_below_2_minus_168':True,
         'seed_length_corollaries':rows,'simulation_resources':resource,
         'input_sha256':{str(oldpath):sha(oldpath)}}
    (HERE/'BOUNDS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'status':'PASS','actual_seed_programming_upper':'2^-94 + 2^-191',
                      'base_statistical_upper':'2^-168','future_seed_lengths_bytes':[48,64],
                      'largest_source_block_bits':13603307520,
                      'ordinary_wrapper_table_bytes':1894400000}))

if __name__=='__main__':main()
