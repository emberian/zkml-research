"""Independent retained-record, source and public-arithmetic audit.

No Sage/estimator import or invocation; no cryptographic objects or samples.
"""
from collections import Counter
from fractions import Fraction
from hashlib import sha256
from itertools import product
import json
import math
from pathlib import Path
import tarfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
AUTHOR = ROOT/'research/learn_infer_only/experiments/private_construction/public_setup_pq/alternatives/hardness'
EST = ROOT/'research/learn_infer_only/experiments/he_closure_costs/estimator'
SNAP = EST/'runtime/pinned-estimator'
COMMIT = '53da5982597709ba0fdf94ea37a84d822310fd84'


def read_public(path):
    path = Path(path).resolve()
    assert not {'.private', 'private', 'signer_route', 'verified_route'}.intersection(path.parts)
    if 'runtime' in path.parts:
        assert path.is_relative_to(SNAP) or path == EST/'runtime/estimator-src.tar' or path == EST/'runtime/sage/lib/python3.12/site-packages/sage/rings/integer.pyx'
    assert path.is_relative_to(ROOT) or path.is_relative_to('/Users/ember/dev/gh/forks/IACR-eprint-mirror')
    return path.read_bytes()


def record(path):
    data = read_public(path)
    return {'path': str(Path(path).resolve()), 'bytes': len(data), 'sha256': sha256(data).hexdigest()}


inputs = json.loads((HERE/'INPUTS.json').read_text())
for expected in inputs['frozen_public_artifacts']:
    assert record(expected['path']) == expected

provenance = json.loads(read_public(EST/'environment-final-provenance.json'))
archive_path = EST/'runtime/estimator-src.tar'
assert record(archive_path)['sha256'] == provenance['estimator_archive_sha256']
archive_sources = []
with tarfile.open(archive_path) as archive:
    assert archive.pax_headers['comment'] == COMMIT
    for member in archive.getmembers():
        if member.isfile() and member.name.startswith('estimator/'):
            archived_bytes = archive.extractfile(member).read()
            assert archived_bytes == read_public(SNAP/member.name)
            archive_sources.append(record(SNAP/member.name))
assert len(archive_sources) == 25
for item in provenance['source_files']:
    assert record(SNAP/'estimator'/item['name'])['sha256'] == item['sha256']

mods = json.loads(read_public(AUTHOR/'moduli.json'))
repair_mods = json.loads(read_public(AUTHOR/'moduli_repair.json'))
for values, exponent, low_offset, high_offset in [(mods,288,127,493), (repair_mods,292,13,601)]:
    assert int(values['low']) == 2**exponent+low_offset
    assert int(values['high']) == 2**(exponent+1)-high_offset
    assert values['low_is_prime_proof_true'] and values['high_is_prime_proof_true']
    assert 2**exponent < int(values['low']) < int(values['high']) < 2**(exponent+1)
    assert values['sage_version'] == '10.8'

models = ['MATZOV_classical', 'ADPS16_classical', 'ADPS16_quantum_core_svp', 'MATZOV_quantum_depth_width']
grid_models = [models[0], models[2]]
validation_models = [models[1], models[3]]
attacks = ['dual', 'usvp', 'bdd']
config = {
    'baseline': ([1024],['low','high'],models,attacks,16384,mods),
    'repair_grid': ([8192,16384,20480,24576],['low'],grid_models,attacks,262144,repair_mods),
    'repair_validation': ([16384],['low','high'],validation_models,attacks,262144,repair_mods),
    'baseline_beta2': ([1024],['low'],models,['dual_fixed_beta2'],16384,mods),
    'normalized_dual_low': ([16384],['low'],models,['dual'],262144,repair_mods),
    'normalized_dual_high': ([16384],['high'],validation_models,['dual'],262144,repair_mods),
    'normalized_dual_final_low': ([16384],['low'],models,['dual'],262144,repair_mods),
    'normalized_dual_final_high': ([16384],['high'],validation_models,['dual'],262144,repair_mods),
}
preflight_groups = {'normalized_dual_low', 'normalized_dual_high'}
raw_dual_groups = {'baseline', 'repair_grid', 'repair_validation'}
rows = []
coverage = {}
operative = []
log_fields_checked = 0
for name, (ns,qs,model_names,attack_names,m,moduli) in config.items():
    group = [json.loads(line) for line in read_public(AUTHOR/(name+'.jsonl')).decode().splitlines()]
    identities = [(x['n'], x['q_label'], x['model'], x['attack']) for x in group]
    assert set(identities) == set(product(ns,qs,model_names,attack_names))
    assert len(identities) == len(set(identities))
    call_manifest = json.loads(read_public(AUTHOR/(name+'.manifest.json')))
    assert call_manifest['estimator_commit'] == COMMIT and call_manifest['source_path'] == str(SNAP)
    assert call_manifest['sage_version'] == '10.8' and call_manifest['red_shape_model'] == 'gsa'
    for file, expected in call_manifest['source_hashes'].items():
        assert record(SNAP/'estimator'/file)['sha256'] == expected
    call_log = read_public(AUTHOR/(name+'.log')).decode()
    assert sum(line.startswith('START ') for line in call_log.splitlines()) == len(group)
    assert sum(line.startswith('RESULT ') for line in call_log.splitlines()) == len(group)
    assert read_public(AUTHOR/(name+'.stderr.log')) == b''
    excluded_raw = 0
    for x in group:
        assert x['m_input'] == m and x['sigma_width_exponent'] == 10
        assert x['q_exact'] == moduli[x['q_label']]
        assert math.isclose(float(x['error_stddev_estimator']),1024/math.sqrt(2*math.pi),rel_tol=0,abs_tol=1e-10)
        assert f"n={x['n']}, q={x['q_exact']}" in x['input_repr']
        assert f'm={m}, tag=None' in x['input_repr']
        assert f"n={x['n']}, q={x['q_exact']}" in x['normalized_repr']
        assert 'Xs=D(σ=408.52), Xe=D(σ=408.52)' in x['normalized_repr']
        assert f"m={m-x['n']}, tag=None" in x['normalized_repr']
        is_raw = name in raw_dual_groups and x['attack']=='dual'
        excluded_raw += is_raw
        if name in preflight_groups:
            assert x['status']=='ERROR' and 'assert normalized.Xs==normalized.Xe' in x['traceback']
        elif name == 'baseline_beta2':
            assert x['status']=='ERROR' and "'mem'" in x['exception'] and 'lwe_dual.py' in x['traceback']
        else:
            assert x['status']=='EXECUTED'
            for key, value in x['log2_fields'].items():
                if isinstance(value,(float,int)):
                    raw = float(x['fields'][key])
                    assert raw>0 and math.isfinite(raw)
                    assert math.isclose(math.log2(raw),value,rel_tol=0,abs_tol=1e-9)
                    log_fields_checked += 1
            if not is_raw:
                assert isinstance(x['log2_fields']['rop'],(float,int))
                assert int(x['fields']['beta']) <= int(x['fields']['d']) <= m+1
                if x['attack']=='dual':
                    assert int(x['fields']['m']) <= m-x['n']
                if x['attack']=='usvp' and x['model'] in [models[1],models[2]]:
                    coefficient = .292 if x['model']==models[1] else .265
                    assert math.isclose(x['log2_fields']['rop'],coefficient*int(x['fields']['beta']),abs_tol=1e-9)
                operative.append({**x, 'source_file': name+'.jsonl'})
        rows.append({**x, 'source_file': name+'.jsonl'})
    coverage[name+'.jsonl'] = {'driver_attempts':len(group),
        'estimator_entries':0 if name in preflight_groups else len(group),
        'status_counts':dict(Counter(x['status'] for x in group)),
        'excluded_raw_dual':excluded_raw,
        'nonfinite_rop':sum(x.get('log2_fields',{}).get('rop')=='+Infinity' for x in group)}
assert len(rows)==76 and len(operative)==46
assert sum(x['estimator_entries'] for x in coverage.values())==70
assert sum(x['excluded_raw_dual'] for x in coverage.values())==20
assert sum(x['nonfinite_rop'] for x in coverage.values())==4
assert Counter(x['status'] for x in rows)=={'EXECUTED':66,'ERROR':10}
minima={}
for x in operative:
    key=f"n{x['n']}_m{x['m_input']}_{x['q_label']}_{x['model']}"
    if key not in minima or x['log2_fields']['rop']<minima[key]['log2_rop']:
        minima[key]={'log2_rop':x['log2_fields']['rop'], 'attack':x['attack'],
                     'beta':x['fields']['beta'], 'source_file':x['source_file'],
                     'informal_minus_log2_768':x['log2_fields']['rop']-math.log2(768)}

# Rebuild finite theorem inequalities and storage using exact integer/rational
# bounds. No new estimator computation or attack-parameter optimization.
d,r,W,T,p,height=577,16,32,384,28439893,262144
X=(p-1)//2;D=d*X;BK=2**35;BL=2**13;flood=2**248
qlo,qhi=int(repair_mods['low']),int(repair_mods['high'])
E=flood+height*BK*BL
assert height*BK*BL==2**66
assert D>=2*W*X+1 and qlo//D>2*W*E
assert Fraction(2*W*X,D)+Fraction(2*W*E,qlo)<1
assert 18+194<4*64  # etaZ<8 using 4 ln 2<pi
reg_bound=Fraction(2*(d-r)+2*T*d,2**189)
smudge_bound=Fraction(2*T*d,2**183)
tail_key=Fraction(3*d*height,2**224)
tail_error=Fraction(3*height,2**246)
assert reg_bound<Fraction(1,2**170) and smudge_bound<Fraction(1,2**164)
assert 2*T*tail_key<Fraction(1,2**185) and 2*T*tail_error<Fraction(1,2**216)
assert reg_bound+smudge_bound+2*T*(tail_key+tail_error)<Fraction(1,2**163)
assert tail_key+T*tail_error<Fraction(1,2**194)
eps=Fraction(1,2**192)
assert eps+(1+eps)*Fraction(1,2**193)<Fraction(1,2**191)
rebuilt=json.loads(read_public(AUTHOR/'REBUILT.json'))
checked_rebuilt_fields=0
independent_rows=[]
for n in [8192,16384,20480,24576]:
    exponent=293*(n+1)-29*height
    assert exponent < -193 and 292*(height-(n+1))>193
    ce=height+d;pe=ce*n;ct=(293*ce+7)//8;pk=(293*pe+7)//8;key=36*height//8
    expected={'n':n,'l':height,'q_low_exact':str(qlo),'q_high_exact':str(qhi),
      'q_selected':str(qlo),'q_bits':293,'sigma_e_width':1024,'sigma_K_width':2**32,
      'flood_radius_exponent':248,'BK':BK,'BL':BL,'scale_denominator':D,
      'delta_at_q_low':qlo//D,'per_coordinate_error_bound':E,'strict_key_storage_bits':36,
      'correctness_2WE_less_delta':True,'regularity_augmented_S_exponent_upper':exponent,
      'theorem_statistical_bound_less_2pow_minus163':True,'theorem_LWE_multiplier':768,
      'ct_bytes':ct,'public_key_bytes':pk,'recipient_key_bytes_on_strict_event':key,
      'all_16_recipient_keys_bytes':16*key,'dense_q_matrix_vector_products':pe,
      'additional_q_message_scale_products':d,
      'coordinate_decryption_modular_products':height,'scalar_add_modular_additions':ce,
      'live_66_ct_bytes':66*ct,'T384_ct_bytes':T*ct}
    authored=next(row for row in rebuilt['rows'] if row['n']==n)
    for key,value in expected.items():
        assert authored[key]==value,(n,key,authored[key],value)
        checked_rebuilt_fields+=1
    independent_rows.append(expected)
for key,value in minima.items():
    authored=rebuilt['finite_named_model_minima'][key]
    assert authored['attack']==value['attack'] and authored['beta']==value['beta']
    assert math.isclose(authored['log2_rop'],value['log2_rop'],abs_tol=1e-10)
    assert math.isclose(authored['log2_rop_minus_log2_768'],value['informal_minus_log2_768'],abs_tol=1e-10)
assert set(minima)==set(rebuilt['finite_named_model_minima'])
assert rebuilt['total_driver_attempts']==76 and rebuilt['total_estimator_entries']==70
assert rebuilt['pre_estimator_assertion_failures']==6
expected_excluded={(x['source_file'],x['n'],x['q_label'],x['model']) for x in rows
                   if x['source_file'].removesuffix('.jsonl') in raw_dual_groups and x['attack']=='dual'}
assert {(x['source_file'],x['n'],x['q_label'],x['model']) for x in rebuilt['raw_dual_excluded']}==expected_excluded
for name,counts in coverage.items():
    assert rebuilt['driver_attempt_coverage'][name]=={'calls':counts['driver_attempts'],
        'errors':counts['status_counts'].get('ERROR',0),'timeouts':0,
        'nonfinite_rop':counts['nonfinite_rop']}

# Check the retained analytic formula arithmetic only, with no lattice formed.
analytic=json.loads(read_public(AUTHOR/'analytic_dual.json'))
for row in analytic['endpoint_formula_evaluations']:
    qb=row['log2q_endpoint'];k=row['heuristic_optimal_k'];kw=row['worst_case_LLL_optimal_k']
    a=math.log2(1.0219)
    norm=k*a+1024*qb/k
    assert math.isclose(norm,row['heuristic_log2_dual_norm'],abs_tol=1e-10)
    # Analytic derivative isolates the two possible minimizing integers.
    real_opt=math.sqrt(1024*qb/a)
    assert k in [math.floor(real_opt),math.ceil(real_opt)]
    assert norm <= min((k-1)*a+1024*qb/(k-1),(k+1)*a+1024*qb/(k+1))
    worst=(kw-1)/4+1024*qb/kw
    assert math.isclose(worst,row['worst_case_LLL_log2_norm_bound'],abs_tol=1e-10)
    assert row['sufficient_norm_log2_upper']==qb-16
    assert norm<qb-16<worst
    assert math.isclose(row['modeled_log2_LLL_d3'],3*math.log2(k),abs_tol=1e-10)
    assert math.isclose(row['modeled_log2_LLL_d3_B2'],3*math.log2(k)+2*math.log2(qb),abs_tol=1e-10)

for expected in inputs['frozen_public_artifacts']:
    assert record(expected['path'])==expected
out={'status':'PASS','scope':'Read-only retained estimator records/source; independent public arithmetic only. No estimator, Sage, lattice or cryptographic execution.',
 'frozen_subjects':inputs['frozen_public_artifacts'],'estimator_archive_matches_commit':COMMIT,
 'archive_estimator_files_matched':len(archive_sources),'source_archive_pins':archive_sources,
 'attempt_coverage':coverage,'driver_attempts':len(rows),'estimator_entries':70,
 'operative_finite_records':len(operative),'excluded_raw_dual':20,'retained_errors':10,
 'retained_raw_Infinity':4,'log_fields_recomputed':log_fields_checked,
 'error_stddev':1024/math.sqrt(2*math.pi),'finite_named_model_minima':minima,
 'rebuilt_fields_matched':checked_rebuilt_fields,'independent_parameter_rows':independent_rows,
 'correctness_all_T_less_2pow_minus194':True,'statistical_total_less_2pow_minus163':True,
 'prime_status':'Author retained proof=True results and reviewed Sage/PARI source; not independently rerun or an exported certificate.',
 'author_files_unchanged':True,'new_estimator_calls':0,'new_crypto_calls':0,
 'remote_queries':0,'PDF_downloads':0}
text=json.dumps(out,indent=2)+'\n';(HERE/'results.json').write_text(text);print(text,end='')
