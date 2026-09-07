#!/usr/bin/env python3
"""Authorized 384-input fixed-span public-fixture run, with resumable checkpoints.

No unissued query, extraction test, or private user data. The host intentionally
holds every fixed-span key; honest private initialization/issuance are assumed.
"""
from pathlib import Path
from collections import deque
import argparse
import hashlib
import json
import math
import os
import secrets
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
SCALING = HERE.parent
sys.path.insert(0,str(SCALING))
import micro
from native_pow import NativePow, LIBRARY

P,Q,G,D,K,WIDTH = micro.P,micro.Q,micro.G,micro.D,micro.K,micro.WIDTH
CT_BYTES = (D+1)*WIDTH
UTILITY = micro.UTILITY
IDENTITY = (1,)*(D+1)


def save(path, value, private=False):
    path=Path(path);temporary=path.with_suffix(path.suffix+".tmp")
    fd=os.open(temporary,os.O_WRONLY|os.O_CREAT|os.O_TRUNC,0o600 if private else 0o644)
    with os.fdopen(fd,"w") as stream:
        json.dump(value,stream,indent=2);stream.write("\n");stream.flush();os.fsync(stream.fileno())
    os.replace(temporary,path)


def read(path):return json.loads(Path(path).read_text())


def emit(value):print(json.dumps(value),flush=True)


def matrix():return micro.queries()


def private_setup(out):
    native=NativePow(P)
    try:
        started=time.perf_counter_ns()
        master=tuple(secrets.randbelow(Q) for _ in range(D))
        public=tuple(native(G,s,P) for s in master)
        keys=tuple(sum(a*b for a,b in zip(master,y,strict=True))%Q for y in matrix())
        micro.dump(out/"public.bin",public);micro.dump(out/"fixed_keys.bin",keys)
        elapsed=time.perf_counter_ns()-started
        save(out/"setup_cost_private.json",{"elapsed_ns":elapsed,"native_powers":D,
            "master_exported":False,"scope":"private timing diagnostic on public synthetic fixture"},True)
        emit({"setup_complete":True,"public_key_bytes":D*WIDTH,"fixed_key_bytes":K*WIDTH,
              "master_exported":False})
    finally:native.close()


def issuer(out, commands_path, deadline):
    commands=read(commands_path)
    public=micro.load(out/"public.bin",D)
    native=NativePow(P)
    ciphertext_dir=out/"ciphertexts";ciphertext_dir.mkdir(exist_ok=True)
    progress_path=out/"issuer_progress_private.json"
    progress=read(progress_path) if progress_path.exists() else {
        "completed":0,"encryption_ns":0,"serialization_ns":0,"input_read_ns":0,
        "native_powers":0,"records":[],"public_key_sha256":micro.sha(out/"public.bin"),
        "commands_sha256":micro.sha(commands_path)}
    assert progress["public_key_sha256"]==micro.sha(out/"public.bin")
    assert progress["commands_sha256"]==micro.sha(commands_path)
    for record in progress["records"]:
        assert micro.sha(out/record["ciphertext"])==record["ciphertext_sha256"]
    try:
        value=native(G,-127,P);encodings={}
        for x in range(-127,128):encodings[x]=value;value=value*G%P
        for ordinal,command in enumerate(commands):
            if ordinal<progress["completed"]:continue
            if time.time()>=deadline:
                save(progress_path,progress,True);emit({"saved_for_deadline":True});return 2
            started=time.perf_counter_ns()
            path=Path(command["issuer_vector_path"])
            assert micro.sha(path)==command["vector_sha256"]
            vector=read(path)
            assert len(vector)==D and all(type(v)is int and abs(v)<=127 for v in vector)
            progress["input_read_ns"]+=time.perf_counter_ns()-started
            started=time.perf_counter_ns()
            randomness=secrets.randbelow(Q)
            ciphertext=(native(G,randomness,P),)+tuple(native(h,randomness,P)*encodings[v]%P
                for h,v in zip(public,vector,strict=True))
            progress["encryption_ns"]+=time.perf_counter_ns()-started
            progress["native_powers"]+=D+1
            started=time.perf_counter_ns()
            dest=out/command["ciphertext"]
            temporary=dest.with_suffix(".tmp");micro.dump(temporary,ciphertext);os.replace(temporary,dest)
            progress["serialization_ns"]+=time.perf_counter_ns()-started
            progress["records"].append({"event_id":command["event_id"],"ciphertext":command["ciphertext"],
                "ciphertext_sha256":micro.sha(dest),"bytes":CT_BYTES})
            progress["completed"]=ordinal+1
            # Commit every input so resumption never needs prior private coins.
            save(progress_path,progress,True)
            if (ordinal+1)%16==0:
                emit({"issued":ordinal+1,"total":len(commands),"ciphertext_bytes":(ordinal+1)*CT_BYTES})
        save(out/"ciphertext_manifest.json",{"records":progress["records"],
            "public_key_sha256":progress["public_key_sha256"],"count":len(commands)})
        emit({"issuance_complete":True,"issued":len(commands),"bytes":len(commands)*CT_BYTES})
        return 0
    finally:native.close()


def group_product(ciphers):
    value=IDENTITY
    for ciphertext in ciphers:value=tuple(a*b%P for a,b in zip(value,ciphertext,strict=True))
    return value


def make_decoder(rows, native):
    bound=32*127*max(sum(map(abs,y)) for y in rows)
    size=math.isqrt(2*bound+1)
    if size*size<2*bound+1:size+=1
    table={};value=1
    for j in range(size):table[value]=j;value=value*G%P
    factor,shift=native(G,-size,P),native(G,bound,P)
    def decode_score(value):
        target=value*shift%P
        for i in range((2*bound)//size+1):
            j=table.get(target)
            if j is not None and i*size+j<=2*bound:return i*size+j-bound,i+1
            target=target*factor%P
        raise ValueError("outside fixed honest-input projection interval")
    return decode_score,bound,size


def evaluator(out, commands_path, deadline):
    commands=read(commands_path);rows=matrix();keys=micro.load(out/"fixed_keys.bin",K)
    manifest=read(out/"ciphertext_manifest.json")
    expected_hash={r["ciphertext"]:r["ciphertext_sha256"] for r in manifest["records"]}
    checkpoint_dir=out/"checkpoints";checkpoint_dir.mkdir(exist_ok=True)
    current=out/"checkpoint.json"
    stats={"learns":0,"queries":0,"expirations":0,"queue_identity_checks":0,
        "validation_ns":0,"update_ns":0,"audit_queue_product_ns":0,"projection_ns":0,
        "decode_ns":0,"serialization_ns":0,"validation_native_powers":0,
        "projection_native_powers":0,"decode_giant_iterations":0}
    completed=0;history=None;queues={};aggregates={};answers=[]
    if current.exists():
        old=read(current)
        assert old["commands_sha256"]==micro.sha(commands_path)
        assert old["fixed_keys_sha256"]==micro.sha(out/"fixed_keys.bin")
        assert old["code_sha256"]==micro.sha(__file__)
        stats,completed,history,answers=old["stats"],old["completed_events"],old["history"],old["answers"]
        for route,items in old["queues"].items():
            queues[int(route)]=deque((item,micro.load(out/item,D+1)) for item in items)
        raw=micro.load(out/old["aggregate_file"],2*(D+1))
        assert micro.sha(out/old["aggregate_file"])==old["aggregate_sha256"]
        for i,route in enumerate(sorted(queues)):
            aggregates[route]=raw[i*(D+1):(i+1)*(D+1)]
            assert group_product(ct for _,ct in queues[route])==aggregates[route]
    native=NativePow(P)
    started=time.perf_counter_ns();decode_score,bound,baby_size=make_decoder(rows,native)
    decoder_ns=time.perf_counter_ns()-started

    def checkpoint():
        started=time.perf_counter_ns()
        relative=f"checkpoints/aggregate_{completed:04d}.bin"
        micro.dump(out/relative,tuple(v for route in sorted(aggregates) for v in aggregates[route]))
        stats["serialization_ns"]+=time.perf_counter_ns()-started
        value={"completed_events":completed,"history":history,
            "queues":{r:[item for item,_ in q] for r,q in queues.items()},
            "aggregate_file":relative,"aggregate_sha256":micro.sha(out/relative),
            "stats":stats,"answers":answers,"code_sha256":micro.sha(__file__),
            "commands_sha256":micro.sha(commands_path),"fixed_keys_sha256":micro.sha(out/"fixed_keys.bin")}
        save(current,value)
        emit({"evaluated_events":completed,"total_events":len(commands),
              "learns":stats["learns"],"queries":stats["queries"],"expirations":stats["expirations"]})

    try:
        for index,command in enumerate(commands):
            if index<completed:continue
            if time.time()>=deadline:checkpoint();return 2
            if command["history"]!=history:
                history=command["history"]
                routes=sorted({c["route"] for c in commands if c["history"]==history})
                assert len(routes)==2
                queues={r:deque() for r in routes};aggregates={r:IDENTITY for r in routes}
            route=command["route"]
            if command["kind"]=="Learn":
                path=out/command["ciphertext"]
                assert micro.sha(path)==expected_hash[command["ciphertext"]]
                ciphertext=micro.load(path,D+1)
                started=time.perf_counter_ns()
                assert all(1<=c<P and native(c,Q,P)==1 for c in ciphertext)
                stats["validation_ns"]+=time.perf_counter_ns()-started
                stats["validation_native_powers"]+=D+1
                started=time.perf_counter_ns()
                aggregate=tuple(a*b%P for a,b in zip(aggregates[route],ciphertext,strict=True))
                queues[route].append((command["ciphertext"],ciphertext))
                if len(queues[route])>32:
                    _,old=queues[route].popleft()
                    aggregate=tuple(a*pow(b,-1,P)%P for a,b in zip(aggregate,old,strict=True))
                    stats["expirations"]+=1
                aggregates[route]=aggregate
                stats["update_ns"]+=time.perf_counter_ns()-started
                started=time.perf_counter_ns()
                assert group_product(ct for _,ct in queues[route])==aggregate
                stats["audit_queue_product_ns"]+=time.perf_counter_ns()-started
                stats["queue_identity_checks"]+=1;stats["learns"]+=1
            else:
                q=command["query_index"];y=rows[q];aggregate=aggregates[route]
                started=time.perf_counter_ns()
                value=pow(native(aggregate[0],keys[q],P),-1,P)
                for c,v in zip(aggregate[1:],y,strict=True):value=value*native(c,v,P)%P
                stats["projection_ns"]+=time.perf_counter_ns()-started
                stats["projection_native_powers"]+=D+1
                started=time.perf_counter_ns();score,iterations=decode_score(value)
                stats["decode_ns"]+=time.perf_counter_ns()-started
                stats["decode_giant_iterations"]+=iterations
                answers.append({"event_id":command["event_id"],"query_index":q,"route":route,
                    "history":history,"score":score,"sign":1 if score>=0 else -1,
                    "active_count":len(queues[route])})
                stats["queries"]+=1
            completed=index+1
            if completed%16==0:checkpoint()
        checkpoint()
        assert (stats["learns"],stats["queries"],stats["expirations"])==(384,96,256)
        save(out/"host_results.json",{"passed":True,"stats":stats,"answers":answers,
            "decoder_setup_ns_this_process":decoder_ns,"decode_bound":bound,"baby_entries":baby_size,
            "master_or_input_plaintext_received":False,"fixed_key_count":K,
            "code_sha256":micro.sha(__file__)})
        return 0
    finally:native.close()


def prepare(out):
    original=UTILITY/"issuer_oracle/input_index.json"
    index=read(original)["events"];assert len(index)==480
    source_manifest=read(UTILITY/"materialized_inputs_manifest.json")["files_sha256"]
    issuer_commands=[];host_commands=[]
    for command in index:
        public={"event_id":command["event_id"],"kind":command["kind"],"route":command["route"],
            "history":int(command["event_id"].split("-")[0][1:])}
        if command["kind"]=="Learn":
            relative=f"ciphertexts/c{len(issuer_commands):04d}.bin"
            vector=command["issuer_vector_path"]
            assert micro.sha(vector)==source_manifest[vector]
            issuer_commands.append({"event_id":command["event_id"],"ciphertext":relative,
                "issuer_vector_path":vector,"vector_sha256":source_manifest[vector]})
            public["ciphertext"]=relative
        else:
            path=Path(command["public_query_vector_path"])
            assert micro.sha(path)==source_manifest[str(path)]
            public["query_index"]=int(path.stem[1:])
        host_commands.append(public)
    assert len(issuer_commands)==384
    save(out/"issuer_commands_private.json",issuer_commands,True)
    save(out/"host_commands.json",host_commands)
    return original


def orchestrate(out, hours):
    out.mkdir(exist_ok=True,parents=True)
    start=time.time();deadline=start+hours*3600
    original=prepare(out)
    save(out/"run_manifest.json",{"started_unix":start,"deadline_unix":deadline,
        "script_sha256":micro.sha(__file__),"native_backend_sha256":micro.sha(SCALING/"native_pow.py"),
        "library_path":str(LIBRARY),"library_sha256":micro.sha(LIBRARY),
        "source_index_sha256":micro.sha(original),"query_hashes":read(SCALING/"linear_results.json")["query_files_sha256"],
        "same_group_control_sha256":micro.sha(SCALING.parents[1]/"additive_ipfe.py"),
        "micro_equality_evidence_sha256":micro.sha(SCALING/"native_micro_results.json"),
        "general_lemma_sha256":micro.sha(SCALING/"GENERAL_FIXED_SPAN.md"),
        "full_fixture_only":True,"no_recovery_or_extraction_tests":True,"fixed_keys":16,
        "group": "RFC3526 group14, P2048, q=(P-1)/2, g2; no PQ or numerical-strength claim"})
    phases=[]
    ready=all((out/name).exists() for name in ("public.bin","fixed_keys.bin","setup_cost_private.json"))
    if (out/"public.bin").exists() and not ready:
        raise ValueError("incomplete setup; use an isolated fresh output directory")
    roles=["issue","evaluate"] if ready else ["setup","issue","evaluate"]
    for name in roles:
        args=[sys.executable,"-I","-B",str(Path(__file__).resolve()),name,"--out",str(out),"--deadline",str(deadline)]
        emit({"phase_start":name})
        t=time.perf_counter_ns()
        with (out/f"{name}_stdout.jsonl").open("a") as log:
            try:result=subprocess.run(args,stdout=log,stderr=subprocess.STDOUT,timeout=max(1,deadline-time.time()))
            except subprocess.TimeoutExpired:
                save(out/"STOPPED.json",{"reason":"wall deadline","phase":name});return 2
        phases.append({"role":name,"wall_ns":time.perf_counter_ns()-t,"exit_code":result.returncode})
        if result.returncode:
            save(out/"STOPPED.json",{"reason":"role saved or failed","phase":name,"exit_code":result.returncode});return result.returncode
        emit({"phase_complete":name,"wall_seconds":phases[-1]["wall_ns"]/1e9})
    save(out/"crypto_execution.json",{"passed":True,"phases":phases,"wall_seconds":time.time()-start,
        "learns":384,"selected_scores":96,"expirations":256,
        "oracle_comparison":"separate oracle.py required","no_master_export":True})
    emit({"crypto_complete":True,"wall_seconds":time.time()-start})
    return 0


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("role",nargs="?",default="run",choices=["run","setup","issue","evaluate"])
    parser.add_argument("--out",type=Path,default=HERE/"outputs")
    parser.add_argument("--deadline",type=float,default=float("inf"))
    parser.add_argument("--hours",type=float,default=2)
    args=parser.parse_args()
    if args.role=="run":code=orchestrate(args.out,args.hours)
    elif args.role=="setup":private_setup(args.out);code=0
    elif args.role=="issue":code=issuer(args.out,args.out/"issuer_commands_private.json",args.deadline)
    else:code=evaluator(args.out,args.out/"host_commands.json",args.deadline)
    raise SystemExit(code)
