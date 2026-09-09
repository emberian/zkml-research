#!/usr/bin/env python3
"""[EXECUTED] Cheap deterministic header contract checks; no expansion/setup."""
import ast
import copy
import hashlib
import json
from pathlib import Path
import transport as t

HERE=Path(__file__).resolve().parent

def forbidden(*args,**kwargs):raise AssertionError('cryptographic generation forbidden in header checks')

def main():
    t.os.urandom=forbidden
    t.PublicExpander.row=forbidden
    t.uniform_below=forbidden
    t.GaussianSampler.sample=forbidden
    t.configure_basis(HERE/'registry.json')
    h=t.basic_header('candidate_full','a','01'*32,a_seed='02'*48)
    h['a_binding']=t.a_binding(h); t.validate_header(h)
    ph=t.basic_header('candidate_full','public',h['setup_id'],a_seed=h['a_seed'],a_binding=h['a_binding'],
       a_sha256=t.descriptor_digest(h),products_sha256='03'*32,missing_seed='04'*48)
    ph['missing_binding']=t.missing_binding(ph);t.validate_header(ph)
    failures=[]
    changes=[('seed_bits',256),('seed_policy','honest-dual-seed-256-v1'),('a_seed','02'*32),
             ('missing_seed','04'*32),('format_version',2),('registry_sha256','05'*32)]
    for name,value in changes:
        wrong=copy.deepcopy(ph);wrong[name]=value
        try:t.validate_header(wrong)
        except ValueError:failures.append(name)
        else:raise AssertionError('invalid/downgraded public header accepted: '+name)
    raw=t.canonical(h)
    assert t.descriptor_digest(ph)==hashlib.sha256(t.MAGIC+len(raw).to_bytes(4,'big')+raw).hexdigest()
    def functions(path):
        return {node.name:ast.dump(node,include_attributes=False) for node in ast.parse(path.read_text()).body if isinstance(node,ast.FunctionDef)}
    before=functions(HERE/'source/semantic_transport.original.py');after=functions(HERE/'transport.py')
    unchanged=['command_decode','command_query','command_combine','command_window','evaluate','load_ciphertext']
    assert all(before[name]==after[name] for name in unchanged)
    out={'status':'PASS','scope':'[EXECUTED] Deterministic synthetic header checks, not actual setup artifacts',
         'mandatory_seed_bits':384,'magic':t.MAGIC.decode(),'format_version':t.FORMAT_VERSION,
         'downgrade_or_context_mutations_rejected':failures,'A_descriptor_roundtrip':True,
         'postprocessing_functions_AST_unchanged':unchanged,
         'registered_basis_rank':len(t.BASIS.pivots),'basis_dimension':t.BASIS.d,
         'whole_two_input_score_bound':2*max(t.BASIS.bounds),
         'Gaussian_samples':0,'expansion_rows':0,'setup_runs':0,'crypto_runs':0}
    (HERE/'HEADER_CHECKS.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out))

if __name__=='__main__':main()
