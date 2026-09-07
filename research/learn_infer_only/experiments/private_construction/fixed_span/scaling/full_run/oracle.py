#!/usr/bin/env python3
"""Independent integer oracle for the original public fixture, no crypto imports."""
from pathlib import Path
from collections import deque
import argparse
import hashlib
import json

HERE=Path(__file__).resolve().parent
UTILITY=HERE.parents[3]/"end_to_end/utility"


def load(path):return json.loads(Path(path).read_text())
def sha(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def save(path,value):Path(path).write_text(json.dumps(value,indent=2)+"\n")


def prepare(out):
    index_path=UTILITY/"issuer_oracle/input_index.json"
    old_path=UTILITY/"issuer_oracle/expected_scalars.json"
    events=load(index_path)["events"];old=load(old_path)["queries"]
    history=None;queues={};sums={};answers=[];learns=expirations=0
    for event in events:
        h=int(event["event_id"].split("-")[0][1:])
        if h!=history:
            history=h;queues={0:deque(),1:deque()};sums={0:[0]*577,1:[0]*577}
        route=event["route"]
        if event["kind"]=="Learn":
            x=load(event["issuer_vector_path"])
            assert len(x)==577 and all(type(v)is int and abs(v)<=127 for v in x)
            # Expire first, then add, independently of the ciphertext implementation.
            if len(queues[route])==32:
                expired=queues[route].popleft()
                sums[route]=[sums[route][i]-expired[i] for i in range(577)]
                expirations+=1
            queues[route].append(x)
            sums[route]=[sums[route][i]+x[i] for i in range(577)]
            learns+=1
        else:
            y=load(event["public_query_vector_path"])
            score=sum(sums[route][i]*y[i] for i in range(577))
            expected=old[event["event_id"]]
            sign=1 if score>=0 else -1
            assert score==expected["expected_scalar"] and sign==expected["sign"]
            correct=sign==expected["target_label"]
            assert correct==expected["correct"]
            ordinal=int(event["event_id"].split("-e")[1])
            answers.append({"event_id":event["event_id"],"history":h,"route":route,
                "phase":(ordinal-1)//80+1,"expected_score":score,"sign":sign,
                "target_label":expected["target_label"],"correct":correct,
                "structural_zero":expected["public_structural_zero"],"active_count":len(queues[route])})
    assert (learns,len(answers),expirations)==(384,96,256)
    nonempty=[a for a in answers if not a["structural_zero"]]
    final=[a for a in answers if a["phase"]==3]
    report={"passed":True,"classification":"independent integer replay of public fixture, no crypto code imports",
        "script_sha256":sha(__file__),"input_index_sha256":sha(index_path),"prior_oracle_sha256":sha(old_path),
        "learns":learns,"scores":len(answers),"expirations":expirations,"answers":answers,
        "utility":{"all":{"correct":sum(a["correct"] for a in answers),"total":len(answers)},
            "nonempty":{"correct":sum(a["correct"] for a in nonempty),"total":len(nonempty)},
            "final":{"correct":sum(a["correct"] for a in final),"total":len(final)}}}
    save(out/"independent_integer_oracle.json",report)
    return report


def compare(out):
    expected=load(out/"independent_integer_oracle.json")
    host=load(out/"host_results.json")
    assert len(host["answers"])==len(expected["answers"])==96
    comparisons=[]
    for actual,wanted in zip(host["answers"],expected["answers"],strict=True):
        assert actual["event_id"]==wanted["event_id"]
        assert actual["score"]==wanted["expected_score"]
        assert actual["sign"]==wanted["sign"]
        assert actual["active_count"]==wanted["active_count"]
        comparisons.append({"event_id":actual["event_id"],"actual_score":actual["score"],
            "expected_score":wanted["expected_score"],"matched":True,
            "utility_correct":wanted["correct"],"structural_zero":wanted["structural_zero"]})
    assert (host["stats"]["learns"],host["stats"]["queries"],host["stats"]["expirations"],
            host["stats"]["queue_identity_checks"])==(384,96,256,384)
    report={"passed":True,"all_96_scores_match":True,"all_384_exact_queue_identities":True,
        "script_sha256":sha(__file__),"host_result_sha256":sha(out/"host_results.json"),
        "independent_oracle_sha256":sha(out/"independent_integer_oracle.json"),
        "utility_unchanged":expected["utility"],"comparisons":comparisons}
    save(out/"comparison.json",report)
    return {k:v for k,v in report.items() if k!="comparisons"}


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("mode",choices=["prepare","compare"])
    parser.add_argument("--out",type=Path,default=HERE/"outputs")
    args=parser.parse_args()
    if args.mode=="prepare":
        r=prepare(args.out);print(json.dumps({k:r[k] for k in ["passed","learns","scores","expirations","utility"]},indent=2))
    else:print(json.dumps(compare(args.out),indent=2))
