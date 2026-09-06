"""Verify disjoint histories/results and derive scalar-circuit role counts, not HE timings."""
import csv,hashlib,json
from pathlib import Path
import numpy as np
ROOT=Path(__file__).resolve().parent

def main():
    manifest=json.loads((ROOT/'model_manifest.json').read_text())
    result=json.loads((ROOT/'results.json').read_text())
    histories=json.loads((ROOT/'histories.json').read_text())
    fixed=json.loads((ROOT/'fixed_point_results.json').read_text())
    config=manifest['config'];d=config['hidden_size'];f=config['intermediate_size']
    L=config['num_hidden_layers'];heads=config['num_attention_heads']
    kv=config['num_key_value_heads']*(d//heads);n=14
    assert set(manifest['prompt_token_length_counts'])=={'14'}
    teach=set(histories['teach_indices']);query=set(histories['query_indices'])
    assert not teach&query
    for hs in histories['groups'].values():
        for h in hs:
            assert len(h['obs'])==len(set(h['obs']))==96 and set(h['obs'])<=teach
    assert not set(fixed['seeds']) & {h['seed'] for hs in histories['groups'].values() for h in hs}
    decisions=json.loads((ROOT/'decisions.json').read_text())
    for name,rows in decisions.items():
        for row in rows:
            H=next(h for h in histories['groups']['test'] if h['seed']==row['seed'])
            current=-np.array(H['labels'])[histories['query_indices']]
            assert np.array_equal(current,row['current_target'])
            assert len(row['after_change'])==97
            recorded=next(r for r in result['results'][name]['per_history'] if r['seed']==row['seed'])
            assert np.mean(np.array(row['after_change'])==current)==recorded['after_change']
    rows=[]
    def add(scope,term,unit,count,formula,visibility,notes):
        rows.append(dict(scope=scope,term=term,unit=unit,count=count,formula=formula,
                         visibility=visibility,status='DERIVED scalar circuit accounting',notes=notes))
    scope='one private 14-token feature extraction; public weights'
    add(scope,'Q/K/V/O and gated-MLP linear maps','private_public_multiply',L*n*(2*d*d+2*d*kv+3*d*f),
        'L*n*(2*d^2+2*d*kv+3*d*f)','private activation; public weights','Dense matrix products; scalar multiplication term only')
    add(scope,'linear-map reductions','private_add',L*n*(2*d*d+2*d*kv+3*d*f-(3*d+2*kv+2*f)),
        'linear multiplies - L*n*(3d+2kv+2f)','private weighted activations','Naive scalar dot-product reductions; machine instruction count differs')
    add(scope,'attention QK and probability V','private_private_multiply',2*L*n*n*d,
        '2*L*n^2*d','both operands tainted','Eager dense n-by-n attention including masked positions')
    add(scope,'attention matrix reductions','private_add',L*(n*n*heads*(d//heads-1)+n*d*(n-1)),
        'L*(n^2*heads*(head_dim-1)+n*d*(n-1))','private scores and values','Dense scalar expansion')
    add(scope,'attention scale','private_public_multiply',L*heads*n*n,'L*heads*n^2',
        'private scores; public head scale','Mask addition and stable-softmax internals are additional')
    add(scope,'gated MLP element product','private_private_multiply',L*n*f,
        'L*n*f','SiLU(gate) and up projection tainted','SiLU internal operations counted as separate primitive below')
    add(scope,'SiLU','private_silu',L*n*f,'L*n*f','private gate vector','No exact integer refinement or HE realization supplied')
    add(scope,'RMSNorm square','private_private_multiply',(2*L+1)*n*d,
        '(2L+1)*n*d','private activations','Mean sums, public scaling and epsilon also required')
    add(scope,'RMSNorm apply inverse root','private_private_multiply',(2*L+1)*n*d,
        '(2L+1)*n*d','private activations and reciprocal root','Learned RMS weights are public; multiply count separate')
    add(scope,'RMSNorm root','private_rsqrt',(2*L+1)*n,'(2L+1)*n','private variance','Nonlinear reciprocal-square-root; not a free gate')
    add(scope,'RMSNorm sum and epsilon','private_add',(2*L+1)*n*d,'(2L+1)*n*((d-1)+1)',
        'private variance','Mean scaling by 1/d also requires a public-scalar multiplication per row')
    add(scope,'attention softmax','private_softmax_vector',L*heads*n,'L*heads*n vectors of n elements','private scores',
        'Each vector requires max/sum/exp/division or a specified alternative; no HE cost claimed')
    add(scope,'RoPE multiply','private_public_multiply',2*L*n*(d+kv),'2*L*n*(d+kv)','private Q/K; public position sin/cos','Public positions/length assumed')
    add(scope,'RoPE add','private_add',L*n*(d+kv),'L*n*(d+kv)','private rotated coordinates','Negation and public trig table generation separate')
    add(scope,'RMS learned weight multiply','private_public_multiply',(2*L+1)*n*d,'(2L+1)*n*d','private normalized activations; public weights','In addition to inverse-root application')
    add(scope,'residual add','private_add',2*L*n*d,'2*L*n*d','private residual branches','Other matrix-reduction/addition work is NOT included in this row')
    add(scope,'embedding lookup','private_token_lookup',n,'n','private token IDs; public embedding table','Oblivious lookup/address hiding required if host must not learn input')
    add(scope,'base A/B head (baseline only)','private_public_multiply',2*d,'2*d','private final hidden; public head','Adaptive heads replace this task output; no full vocabulary emitted')
    add(scope,'full vocabulary alternative head','private_public_multiply',d*config['vocab_size'],'d*vocab','private hidden; public full head',
        'NOT executed here; needed if replacing binary task output with full logits; selection/release separate')
    add('private model feature to full readout','public center subtraction','private_add',576,'d',
        'private hidden; public center','Bias insertion is public; chosen scale uses public unlabeled teaching-domain statistics')
    add('private model feature to full readout','public normalization scale','private_public_multiply',577,'d+1',
        'private centered hidden; public scale','Fixed-point importer adds round-even and clamp per coordinate; unproved from float kernel')
    add('private model feature to projected readout','fixed projection','private_public_multiply',576*64,'d*64',
        'private centered hidden; public Rademacher matrix','Plus d centering additions,64*(d-1) projection additions and65 public scaling multiplications')
    add('private sensor to quadratic features','quadratic monomials','private_private_multiply',3,'xy,x^2,y^2',
        'private normalized x,y','Input/output public scaling, fixed-point import rounding and proof of feature provenance also required')
    for r in (577,65,6):
        scope=f'exact fixed-point LMS Learn dimension {r}; private feature and label'
        add(scope,'dot and error-feature update','private_private_multiply',2*r,'2r','private M and P; private error',
            'Chosen eta=1; public rho scaling is separate')
        add(scope,'rho scaling','private_public_multiply',r,'r','private M; public R','Can specialize R=Q when rho=1')
        add(scope,'integer additions','private_add',3*r+1,'(r-1) dot adds +1 rounding +1 error +r update sums +r rounding',
            'private operands','Clamp selection adds/muxes excluded and listed separately')
        add(scope,'nearest-ties-up rounding','private_floor_power_two',r+1,'r+1','private dot and update numerators',
            'Secure exact division/floor by public Q; modular inverse is not this operation')
        add(scope,'state saturation','private_clamp',r,'r to [-16Q,16Q]','private update','Comparison/selection mechanism unimplemented')
        scope=f'exact fixed-point LMS Infer dimension {r}; public query feature'
        add(scope,'score dot','private_public_multiply',r,'r','private M; public query P','If query is private this becomes private_private')
        add(scope,'score sum','private_add',r-1,'r-1','private products','Plus one private sign and authorized recipient release')
        add(scope,'binary answer','private_sign',1,'1','private score','No score or logits may be released by this task interface')
        add(scope,'state storage in executed int64/float64 readout','plaintext_bytes',8*r,'8r','private semantic state; plaintext in experiment',
            'Ciphertext size/key material/commitments/proofs absent; this is not encrypted state size')
    add('generic 64-item 576-feature kNN; query public','dot products using precomputed private key norms',
        'private_public_multiply',64*576,'M*r','private stored keys; public query',
        'Learn must compute each key norm with r private_private squares; generic representation, not precomputed public-domain shortcut')
    add('generic 64-item 576-feature kNN; query public','argmin comparisons','private_compare',63,'M-1','private distances',
        'Selected label and index need oblivious selection, not host-visible index')
    add('executed finite-grid kNN state','64 index and 64 label int64 arrays','plaintext_bytes',1024,'64*2*8','indices and labels private semantically',
        'Additional globally cached public-domain distance table: 289^2*8 bytes; secret-index lookup has no protected implementation')
    add('executed finite-grid distance table','one method distance matrix','public_bytes',289*289*8,'289^2*8','public finite coordinate universe',
        'Two matrices cached for utility evaluator; addresses into them reveal private input IDs if exposed')
    with open(ROOT/'costs.csv','w',newline='') as f:
        w=csv.DictWriter(f,fieldnames=rows[0]);w.writeheader();w.writerows(rows)
    audit={'passed':True,'audits':['teaching/query coordinate disjointness','history-seed disjointness including fixed-point follow-on',
        'saved target/prediction arrays recompute every main held-out accuracy','all 289 actual model prompts have 14 tokens'],
        'counts_source':{'L':L,'d':d,'f':config['intermediate_size'],'kv':kv,'heads':heads,'n':n},
        'model_fp32_parameter_bytes':manifest['model_parameter_count']*4,
        'fixed_point_largest_universal_numerator_bound':fixed['exact_checks']['largest_universal_numerator_bound'],
        'hashes':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [ROOT/'costs.csv',Path(__file__),ROOT/'MODEL_CARD.md',
          ROOT/'.venv/lib/python3.14/site-packages/transformers/models/llama/modeling_llama.py']}}
    (ROOT/'audit.json').write_text(json.dumps(audit,indent=2,sort_keys=True)+'\n')
    print(json.dumps(audit,indent=2))

if __name__=='__main__':main()
