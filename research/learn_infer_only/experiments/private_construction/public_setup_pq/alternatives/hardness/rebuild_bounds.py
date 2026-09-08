"""Exact public proof/cost checks and estimator-log summary, no crypto."""
from pathlib import Path
import json
import math

HERE=Path(__file__).resolve().parent
mods=json.loads((HERE/'moduli_repair.json').read_text())
qlo,qhi=int(mods['low']),int(mods['high'])
d,r,W,T,p=577,16,32,384,28439893
X=(p-1)//2;D=d*X;l=2**18;BK=2**35;BL=2**13;F=2**248
E=F+l*BK*BL
assert l*BK*BL==2**66
assert D>=2*W*X+1
assert qlo//D>2*W*E
assert 2**292<qlo<qhi<2**293
# etaZ<8 for eps0=2^-192: ln2/pi<1/4.
assert 18+194<4*64
rows=[]
for n in [8192,16384,20480,24576]:
    reg_exponent=293*(n+1)-29*l
    assert reg_exponent < -193
    assert 2*(d-r)+2*T*d<2**19
    assert 2*T*d<2**19
    # Smudging total < (2T d)*2^66/2^249 = (2T d)/2^183 <2^-164.
    # Key/error 8sigma tails: denominators 2^224 and 2^246.
    assert 2*T*3*d*l<2**(224-185)
    assert 2*T*3*l<2**(246-216)
    assert 2**52+2**46+2**31+1<2**53  # losses <2^-164+2^-170+2^-185+2^-216 <2^-163
    ce=l+d;pe=ce*n
    cb=(ce*293+7)//8;pb=(pe*293+7)//8;kb=l*36//8
    rows.append({'n':n,'l':l,'q_low_exact':str(qlo),'q_high_exact':str(qhi),
                 'q_selected':str(qlo),'q_bits':293,'sigma_e_width':1024,'sigma_K_width':2**32,
                 'flood_radius_exponent':248,'BK':BK,'BL':BL,
                 'scale_denominator':D,'delta_at_q_low':qlo//D,
                 'per_coordinate_error_bound':E,'strict_key_storage_bits':36,
                 'correctness_2WE_less_delta':True,'regularity_augmented_S_exponent_upper':reg_exponent,
                 'theorem_statistical_bound_less_2pow_minus163':True,
                 'theorem_LWE_multiplier':768,
                 'ct_bytes':cb,'public_key_bytes':pb,'recipient_key_bytes_on_strict_event':kb,
                 'all_16_recipient_keys_bytes':16*kb,'dense_q_matrix_vector_products':pe,
                 'additional_q_message_scale_products':d,
                 'coordinate_decryption_modular_products':l,'scalar_add_modular_additions':ce,
                 'live_66_ct_bytes':66*cb,'T384_ct_bytes':T*cb})
all_results=[];coverage={}
for fn in ['baseline.jsonl','repair_grid.jsonl','repair_validation.jsonl','baseline_beta2.jsonl',
           'normalized_dual_low.jsonl','normalized_dual_high.jsonl',
           'normalized_dual_final_low.jsonl','normalized_dual_final_high.jsonl']:
    data=[json.loads(s) for s in (HERE/fn).read_text().splitlines()]
    for x in data:x['source_file']=fn
    all_results+=data
    coverage[fn]={'calls':len(data),
                  'errors':sum(x['status']=='ERROR' for x in data),
                  'timeouts':sum(x['status']=='TIMEOUT' for x in data),
                  'nonfinite_rop':sum(x.get('log2_fields',{}).get('rop') in ['+Infinity','-Infinity'] for x in data)}
assert coverage['baseline.jsonl']['calls']==24
assert sum(v['calls'] for k,v in coverage.items() if k in
           ['repair_grid.jsonl','repair_validation.jsonl','baseline_beta2.jsonl'])==40
assert sum(v['calls'] for k,v in coverage.items() if k.startswith('normalized_dual_final'))==6
assert sum(v['calls'] for k,v in coverage.items())==76
excluded=[]
minima={}
for x in all_results:
    if x['attack']=='dual' and x['source_file'] in ['baseline.jsonl','repair_grid.jsonl','repair_validation.jsonl']:
        excluded.append({'source_file':x['source_file'],'n':x['n'],'q_label':x['q_label'],
                         'model':x['model'],'reason':'raw dual API precondition requires normalized input'})
        continue
    val=x.get('log2_fields',{}).get('rop')
    if x['status']!='EXECUTED' or not isinstance(val,(int,float)):continue
    key=f"n{x['n']}_m{x['m_input']}_{x['q_label']}_{x['model']}"
    if key not in minima or val<minima[key]['log2_rop']:
        minima[key]={'log2_rop':val,'attack':x['attack'],'beta':x['fields'].get('beta'),
                     'log2_rop_minus_log2_768':val-math.log2(768)}
out={'scope':'Heuristic repair candidate; exact finite proof arithmetic, no cryptographic execution.',
     'rows':rows,'driver_attempt_coverage':coverage,
     'total_driver_attempts':76,'pre_estimator_assertion_failures':6,
     'total_estimator_entries':70,'raw_dual_excluded':excluded,
     'finite_named_model_minima':minima}
text=json.dumps(out,indent=2)+'\n'
(HERE/'REBUILT.json').write_text(text);print(text,end='')
