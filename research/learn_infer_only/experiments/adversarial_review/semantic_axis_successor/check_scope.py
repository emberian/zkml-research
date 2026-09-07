#!/usr/bin/env python3
"""Public text/source/tokenizer bookkeeping only: no model class or forward."""
from pathlib import Path
import ast
import hashlib
import json
import tokenizers
import numpy as np

HERE=Path(__file__).resolve().parent
EXP=HERE.parents[1]
ROOT=EXP/'end_to_end/utility/semantic_axis_successor'
BASE=EXP/'adaptation_utility'

def load(p):return json.loads(p.read_text())
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()

def constants(p):
    out={}
    for node in ast.parse(p.read_text()).body:
        if isinstance(node,ast.Assign):
            for target in node.targets:
                if isinstance(target,ast.Name) and target.id in ('NAMES','TEMPLATES','CUES'):
                    out[target.id]=ast.literal_eval(node.value)
    assert set(out)=={'NAMES','TEMPLATES','CUES'}
    return out

def main():
    new=constants(ROOT/'surfaces.py')
    old=[constants(BASE/n) for n in ('text_transfer_data.py','representation_data.py')]
    prior=[constants(ROOT.parent/p) for p in ('attribute_calibration/data.py','e5_successor/surfaces.py')]
    disjoint=[]
    for s in (0,1):
        names={v for d in old for pool in d['NAMES'].values() for v in pool[s]}
        templates={v for d in old for pool in d['TEMPLATES'].values() for v in pool[s]}
        cues={v for d in old for pool in d['CUES'].values() for pair in pool[s] for v in pair}
        for d in prior:
            names.update(d['NAMES'][s]);templates.update(d['TEMPLATES'][s])
            cues.update(v for template in d['CUES'][s] for pair in template for v in pair)
        nc={v for template in new['CUES'][s] for pair in template for v in pair}
        assert set(new['NAMES'][s]).isdisjoint(names|{'Marigold'})
        assert set(new['TEMPLATES'][s]).isdisjoint(templates) and nc.isdisjoint(cues)
        disjoint.append({'task':s,'new_names':len(new['NAMES'][s]),'new_full_templates':len(new['TEMPLATES'][s]),
                         'new_full_cues':len(nc),'prior_name_count':len(names),'prior_template_count':len(templates),
                         'prior_cue_count':len(cues),'exact_string_overlaps':0})
    records=load(ROOT/'records.json');oracle=load(ROOT/'test_oracle.json')
    for r,o in zip(records[256:],oracle,strict=True):
        assert o=={'record_id':r['id'],'task':('plant','letter')[r['skill']],'a':r['a'],'b':r['b']}
        s=r['skill'];t=r['template']
        assert r['entity'] in new['NAMES'][s]
        assert r['text']==new['TEMPLATES'][s][t].format(name=r['entity'],a=new['CUES'][s][t][0][r['a']],b=new['CUES'][s][t][1][r['b']])

    for H in load(ROOT/'histories.json')['histories']:
        rng=np.random.default_rng(H['seed']);rules=[]
        for _ in range(2):
            rule=[-1]*4
            for i in rng.choice(4,2,replace=False):rule[int(i)]=1
            rules.append(rule)
        phases=[]
        for s in (0,1,0):
            teacher_ids=[r['id'] for r in records[:128] if r['skill']==s]
            phases.append(rng.permutation(teacher_ids).tolist())
        assert rules==H['rules'] and phases==H['phases']

    freeze=load(ROOT/'freeze.json');path=Path(freeze['model_path'])/'tokenizer.json'
    assert sha(path)==freeze['model_files']['tokenizer.json']['sha256']
    tokenizer=tokenizers.Tokenizer.from_file(str(path))
    prompt_checks=suffix_checks=0
    for r in load(ROOT/'issuer_inputs.json'):
        text=r['rendered_prompt']
        assert tokenizer.encode(text,add_special_tokens=False).ids==r['token_ids']
        prompt_checks+=1
        for literal,tid in [('0',15),('1',16)]:
            assert tokenizer.encode(text+literal,add_special_tokens=False).ids==r['token_ids']+[tid]
            suffix_checks+=1

    batches=load(ROOT/'batch_costs.json');smol=load(ROOT/'smol_test.extraction.json');cost=load(ROOT/'score_results.json')
    assert len(batches)==32 and sum(x['examples'] for x in batches)==256
    assert [x['first_example_index'] for x in batches]==list(range(0,256,8))
    assert sum(x['nonpadding_tokens'] for x in batches)==cost['nonpadding_tokens']==45312
    assert sum(x['padded_tokens'] for x in batches)==cost['padded_tokens']==46304
    assert abs(sum(x['forward_wall_seconds'] for x in batches)-cost['forward_wall_seconds'])<1e-12
    assert len(smol['batches'])==8 and sum(x['records'] for x in smol['batches'])==128
    assert smol['unpadded_tokens']==4376 and smol['padded_tokens']==4704
    assert cost['new_test_texts']==128 and 'teacher_texts' not in cost
    assert cost['actual_model_forward_calls']==32 and cost['generated_tokens']==0 and cost['weight_updates']==0
    result={'schema':'semantic-successor-public-scope-review-v1','passed':True,'script_sha256':sha(Path(__file__)),
            'source_surface_hash':sha(ROOT/'surfaces.py'),'exact_string_disjointness':disjoint,
            'new_record_template_and_oracle_equalities':128,'backend_tokenizer_prompt_id_checks':prompt_checks,
            'exact_seeded_history_regenerations':64,'numpy_version':np.__version__,
            'backend_single_token_suffix_checks':suffix_checks,'tokenizer_sha256':sha(path),'tokenizers_version':tokenizers.__version__,
            'source_batches':32,'source_axis_examples':256,'source_real_padded_tokens':[45312,46304],
            'baseline_batches':8,'baseline_texts':128,'baseline_real_padded_tokens':[4376,4704],
            'replayed_model_forwards':0,'crypto_or_privacy_experiments':0,
            'scope':'Exact string novelty within the named source corpus; known meanings/ordinary words are shared. Tokenization only, no model loading or inference.'}
    (HERE/'scope_results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
