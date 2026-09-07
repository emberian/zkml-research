#!/usr/bin/env python3
"""Independent replay of public synthetic records; no model/crypto imports.

NumPy is used only to load saved numeric arrays and reproduce fixed baseline
quantization. All learner dot products and retained-queue sums use Python ints.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json
import math
import statistics
import time
import numpy as np

HERE = Path(__file__).resolve().parent
EXP = HERE.parents[1]
ROOT = EXP / "end_to_end/utility/semantic_axis_successor"
UTILITY = ROOT.parent
BASE = EXP / "adaptation_utility"
SELECTED = UTILITY / "semantic_axis_selection"


def load(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    start = time.monotonic()
    freeze = load(ROOT / "freeze.json")
    assert sha(ROOT / "freeze.json") == load(ROOT / "score_started.json")["freeze_sha256"]
    checked_sources = []
    for p, expected in freeze["source_sha256"].items():
        assert sha(Path(p)) == expected, p
        checked_sources.append(p)
    oldscore = (SELECTED / "score.py").read_text()
    expected = oldscore.replace("'teacher_texts'", "'new_test_texts'").replace("'framings':2", "'framings':1").replace("'heldout_inputs':0", "'heldout_inputs':128").replace("'oracle_opened_by_scoring_process'", "'oracle_parsed_by_scoring_process'")
    assert (ROOT / "score.py").read_text() == expected
    assert load(SELECTED / "results.json")["selected_framing"] == "A"

    records = load(ROOT / "records.json")
    histories = load(ROOT / "histories.json")["histories"]
    report = load(ROOT / "results.json")
    raw = load(ROOT / "raw_scores.json")
    oracle = {r["record_id"]: r for r in load(ROOT / "test_oracle.json")}
    inputs = load(ROOT / "issuer_inputs.json")
    prompts = load(SELECTED / "prompts.json")
    assert [r["id"] for r in records] == list(range(384))
    assert len({r["text"] for r in records}) == 384
    assert [h["seed"] for h in histories] == list(range(67000, 67064))
    assert records[:256] == load(BASE / "representation_records.json")[:256]
    prior_text_files = [BASE / "text_transfer_records.json", BASE / "representation_records.json",
                        UTILITY / "attribute_calibration/records.json", UTILITY / "e5_successor/records.json"]
    new_texts = {r["text"] for r in records[256:]}
    overlaps = {}
    for p in prior_text_files:
        old = {r["text"] for r in load(p)}
        overlap = len(new_texts & old)
        assert overlap == 0
        overlaps[str(p)] = overlap
    assert Counter((r["skill"], r["a"], r["b"]) for r in records[256:]) == { (s,a,b):16 for s in range(2) for a in range(2) for b in range(2) }

    assert len(inputs) == len(raw) == 256
    assert {(r["record_id"],r["axis"]) for r in raw} == {(i,a) for i in range(256,384) for a in ("a","b")}
    for entry in inputs:
        r = records[entry["record_id"]]
        assert r["pool"] == "test" and entry["text"] == r["text"]
        task = ("plant", "letter")[r["skill"]]
        axis = prompts["axes"][task][entry["axis"]]
        expected_user = prompts["framings"]["A"]["user_template"].format(task=task,text=r["text"],**axis)
        assert entry["messages"] == [{"role":"system","content":prompts["framings"]["A"]["system"]},{"role":"user","content":expected_user}]
        assert entry["alternative_token_ids_in_bit_order"] == [15,16]
        assert len(entry["token_ids"]) == entry["token_count"]
        assert hashlib.sha256(entry["rendered_prompt"].encode()).hexdigest() == entry["rendered_prompt_sha256"]
        assert entry["framing"] == "A" and not ({"a","b","oracle_bit","label"} & set(entry))
    assert sum(x["token_count"] for x in inputs) == 45312
    assert sum(8*max(x["token_count"] for x in inputs[i:i+8]) for i in range(0,256,8)) == 46304
    tokenizer = load(Path(freeze["model_path"]) / "tokenizer.json")
    assert tokenizer["model"]["vocab"]["0"] == 15 and tokenizer["model"]["vocab"]["1"] == 16

    teacher = load(ROOT / "teacher_predictions.json")
    old_predictions = {}
    for r in load(SELECTED / "raw_scores.json"):
        if r["framing"] == "A":
            old_predictions.setdefault(r["record_id"], {})[r["axis"]] = r["predicted_bit"]
    for r in teacher:
        assert {"a":r["a"],"b":r["b"]} == old_predictions[r["record_id"]]
    bits = {i:{} for i in range(256,384)}
    errors = []
    factual_correct = Counter()
    for row in raw:
        i = row["record_id"]
        predicted = int(row["logits_in_bit_order"][1] > row["logits_in_bit_order"][0])
        assert predicted == row["predicted_bit"]
        assert row["exact_tie"] == (row["logits_in_bit_order"][0] == row["logits_in_bit_order"][1])
        assert row["alternative_token_ids_in_bit_order"] == [15,16]
        bits[i][row["axis"]] = predicted
        if predicted == oracle[i][row["axis"]]:
            factual_correct[(row["task"],row["axis"])] += 1
        else:
            errors.append(i)
            assert row["task"] == "plant" and row["axis"] == "b"
            assert oracle[i]["b"] == 0 and predicted == 1 and records[i]["template"] == 0
    assert len(errors) == 15 and errors == [r["record_id"] for r in report["factual"]["errors"]]
    assert factual_correct == {("plant","a"):64,("plant","b"):49,("letter","a"):64,("letter","b"):64}
    assert all(str(i) in (ROOT / "ERRORS.md").read_text() for i in errors)
    complete_pairs = sum(bits[i] == {"a":oracle[i]["a"],"b":oracle[i]["b"]} for i in bits)
    assert complete_pairs == 113

    arrays = np.load(ROOT / "features.npz", allow_pickle=False)
    states = np.load(ROOT / "checkpoint_states.npz", allow_pickle=False)
    methods = list(report["results"])
    q = {name: arrays[name].tolist() for name in methods}
    expected_primary = [[0]*577 for _ in range(384)]
    for pred in teacher + [{"record_id":i,**b} for i,b in bits.items()]:
        i=pred["record_id"];s=records[i]["skill"]
        expected_primary[i][4*s+2*pred["a"]+pred["b"]]=127
    assert q["semantic577"] == expected_primary
    for i,r in enumerate(records):
        expected_gold=[0]*577;expected_gold[4*r["skill"]+2*r["a"]+r["b"]]=127
        assert q["attribute8"][i] == expected_gold
    # Reproduce the original fixed calibration without fitting anything new.
    hidden=np.concatenate([np.load(BASE/'representation_features.npz',allow_pickle=False)['mean_10'][:256],np.load(ROOT/'smol_test.npz',allow_pickle=False)['features']]).astype(np.float64)
    policy=load(UTILITY/'encoder_policy.json')['policies_by_public_route']
    for i,r in enumerate(records):
        p=policy[str(r['skill'])]
        x=(hidden[i]-np.array(p['center']))/p['scale']
        expected_row=np.clip(np.rint(127*np.append(x,1/p['scale'])),-127,127).astype(np.int8).tolist()
        assert expected_row == q['original577'][i]
    assert np.array_equal(arrays['original577'][:256],np.load(UTILITY/'e5_successor/features.npz',allow_pickle=False)['original577'][:256])

    nonzero={name:[[(j,x) for j,x in enumerate(row) if x] for row in Q] for name,Q in q.items()}
    verified_scores=Counter();correct_phases={n:[0,0,0] for n in methods}
    final_by_history={n:[] for n in methods};final_task={n:[0,0] for n in methods}
    retention=0;primary_updates=0;primary_expiries=0;primary_vectors=0
    strata={n:Counter() for n in methods};attributes={n:Counter() for n in methods};rule_types=Counter()
    skill_types=Counter();skill_correct={n:Counter() for n in methods};maxima=Counter()
    for hi,H in enumerate(histories):
        assert all(sorted(rule)==[-1,-1,1,1] for rule in H['rules'])
        types=['nonlinear' if rule[0]==rule[3] and rule[1]==rule[2] else 'linear' for rule in H['rules']]
        stratum='/'.join(types);rule_types[stratum]+=1;skill_types.update(types)
        queues=[[],[]];running_counts=[[0]*4,[0]*4]
        checked_states={n:[] for n in methods};checked_scores={n:[] for n in methods}
        for phase,ids in enumerate(H['phases']):
            skill=(0,1,0)[phase]
            assert len(ids)==64 and set(ids)=={r['id'] for r in records[:128] if r['skill']==skill}
            for rid in ids:
                r=records[rid];s=r['skill'];label=H['rules'][s][2*r['a']+r['b']]
                if phase==2 and s==0:label=-label
                queues[s].append((rid,label))
                coord=nonzero['semantic577'][rid][0][0]-4*s
                running_counts[s][coord]+=label
                if len(queues[s])>32:
                    oldrid,oldlabel=queues[s].pop(0)
                    running_counts[s][nonzero['semantic577'][oldrid][0][0]-4*s]-=oldlabel
                    primary_expiries+=1
                direct=[sum(y for j,y in queues[s] if nonzero['semantic577'][j][0][0]==4*s+k) for k in range(4)]
                assert direct==running_counts[s] and sum(abs(x) for x in direct)<=len(queues[s])
                assert (sum(direct)-len(queues[s]))%2==0
                primary_updates+=1
            for name in methods:
                dense=[]
                for s in range(2):
                    # A direct functional sum over retained entries, not an incremental update.
                    v=[0]*577
                    for rid,label in queues[s]:
                        for j,x in nonzero[name][rid]:v[j]+=label*x
                    assert v==states[name][hi,phase,s].tolist()
                    assert all(-4064<=x<=4064 for x in v)
                    dense.append(v)
                    if name=='semantic577':primary_vectors+=1
                checked_states[name].append(dense)
                out=[];right=0
                author=report['results'][name]['per_history'][hi]
                assert author['seed']==H['seed'] and author['query_ids']==list(range(256,384))
                assert author['rule_types']==types and author['joint_stratum']==stratum
                for qi,r in enumerate(records[256:]):
                    s=r['skill'];target=H['rules'][s][2*r['a']+r['b']]
                    if phase==2 and s==0:target=-target
                    value=sum(dense[s][j]*x for j,x in nonzero[name][r['id']])
                    predicted=1 if value>=0 else -1
                    assert value==author['scores'][phase][qi]
                    assert predicted==author['predictions'][phase][qi] and target==author['targets'][phase][qi]
                    verified_scores[name]+=1;maxima[name]=max(maxima[name],abs(value));out.append(value)
                    correct_phases[name][phase]+=predicted==target;right+=predicted==target
                    if phase==2:
                        final_task[name][s]+=predicted==target
                        strata[name][stratum]+=predicted==target
                        attributes[name][f'{s}.{r["a"]}{r["b"]}']+=predicted==target
                        skill_correct[name][types[s]]+=predicted==target
                checked_scores[name].append(out)
                if phase==2:final_by_history[name].append(right)
        for name in methods:
            assert checked_states[name][0][0]==checked_states[name][1][0]
            assert checked_states[name][1][1]==checked_states[name][2][1]
            assert checked_scores[name][0][:64]==checked_scores[name][1][:64]
            assert checked_scores[name][1][64:]==checked_scores[name][2][64:]
            retention+=2

    assert verified_scores=={n:24576 for n in methods}
    assert (primary_updates,primary_expiries,primary_vectors,retention)==(12288,8192,384,384)
    for n in methods:
        a=report['results'][n]
        assert sum(final_by_history[n])==a['correct_final']
        assert {k:v for k,v in strata[n].items()}=={k:v['correct_final'] for k,v in a['joint_rule_strata'].items()}
        assert {k:v for k,v in skill_correct[n].items()}=={k:v['correct_final'] for k,v in a['by_rule_type'].items()}
        for key,right in attributes[n].items():
            skill,pair=key.split('.');label=('plant','letter')[int(skill)]+'.'+pair
            assert right==a['joint_attribute_strata'][label]['correct_final']
    gains=[(a-b)/128 for a,b in zip(final_by_history['semantic577'],final_by_history['original577'],strict=True)]
    mean=statistics.mean(gains);half=1.96*statistics.stdev(gains)/math.sqrt(64)
    saved=report['paired_primary_minus']['original577']
    assert mean==saved['mean'] and abs(half-saved['normal95_half_width'])<1e-14
    assert min(gains)==saved['min'] and max(gains)==saved['max']
    factual_overall=sum(factual_correct.values())/256
    nonlinear_gain=(skill_correct['semantic577']['nonlinear']-skill_correct['original577']['nonlinear'])/(64*skill_types['nonlinear'])
    simple_gain=(skill_correct['semantic577']['linear']-skill_correct['original577']['linear'])/(64*skill_types['linear'])
    gates=[factual_overall>=.9,all(sum(v for (t,a),v in factual_correct.items() if t==task)/128>=.85 for task in ('plant','letter')),
           sum(final_by_history['semantic577'])/8192>=.75,all(v/4096>=.75 for v in final_task['semantic577']),
           mean>=.1,mean-half>0,nonlinear_gain>=.1,simple_gain>=-.05,retention==384,
           all(strata['semantic577'][k]/(128*v)>=.65 for k,v in rule_types.items()),
           all(v/1024>=.65 for v in attributes['semantic577'].values())]
    assert all(gates) and list(report['acceptance'].values()).count(True)==11
    image={}
    for s in range(2):
        for pool,ids in [('teacher',range(128)),('test',range(256,384))]:
            coords={nonzero['semantic577'][i][0][0] for i in ids if records[i]['skill']==s}
            assert coords==set(range(4*s,4*s+4));image[f'{s}.{pool}']=sorted(coords)

    output={'schema':'independent-semantic-successor-recorded-replay-v1','passed':True,'script_sha256':sha(Path(__file__)),
            'author_report_sha256':sha(ROOT/'REPORT.md'),'author_manifest_sha256':sha(ROOT/'manifest.json'),
            'frozen_sources_rehashed':len(checked_sources),'exact_selected_scorer_metadata_only_delta':True,
            'new_full_text_overlaps':overlaps,'prompt_message_constructions_checked':len(inputs),'new_token_counts':[45312,46304],
            'teacher_predictions_reused_exactly':128,'factual_correct_by_axis':{'.'.join(k):v for k,v in factual_correct.items()},
            'factual_correct_bits':sum(factual_correct.values()),'complete_factual_pairs':complete_pairs,'all_fifteen_error_ids':errors,
            'all_method_integer_scores_checked':dict(verified_scores),'all_three_method_checkpoint_vectors_checked':384*3,
            'primary_direct_queue_updates':primary_updates,'primary_original_signed_expiries':primary_expiries,
            'untouched_route_exact_state_and_raw_score_equalities':retention,
            'correct_by_phase':correct_phases,'final_task_correct':final_task,'final_correct':{n:sum(v) for n,v in final_by_history.items()},
            'joint_rule_history_counts':dict(rule_types),'rule_skill_instance_counts':dict(skill_types),
            'joint_rule_correct':{n:dict(v) for n,v in strata.items()},'attribute_strata_correct':{n:dict(v) for n,v in attributes.items()},
            'paired_gain':mean,'descriptive_history_paired_1_96_se_half_width':half,'history_gain_range':[min(gains),max(gains)],
            'all_eleven_frozen_gates_pass':True,'observed_max_abs_scores':dict(maxima),
            'effective_basis_image':image,'exact_score_basis_determinant':16129**4,
            'numpy_version':np.__version__,'elapsed_seconds':time.monotonic()-start,'model_calls':0,'crypto_calls':0,
            'scope':'Only retained public synthetic data/source; no model/crypto rerun or privacy/routing/extraction experiment.'}
    (HERE/'recorded_results.json').write_text(json.dumps(output,indent=2)+'\n')
    print(json.dumps(output,indent=2))


if __name__=='__main__':
    main()
