#!/usr/bin/env python3
"""Continuing local text learner with proof-gated durable updates and queries.
Reuse the previous journal's canonical JSON, CAS writes and SQLite primitives.
The encoder/full reader and protocol metadata remain explicit local TCB.
"""
from pathlib import Path
import argparse
import contextlib
import fcntl
import importlib.util
import json
import os
import re
import sys
import time
from common import ROOT, command, now, sha, check_pins
import pipeline
from fixture_builder import helper

spec=importlib.util.spec_from_file_location('frozen_multiclass_journal',ROOT.parent/'multiclass_successor/service.py')
j=importlib.util.module_from_spec(spec); spec.loader.exec_module(j)
ENV=dict(os.environ,RAYON_NUM_THREADS='4',PYTHONDONTWRITEBYTECODE='1')
POLICY={'schema':'live-nonlinear-continuing-policy-v1','capacity':8,'update':'out=acc+fresh-old; issue fresh example into next cyclic SIMD lane; old is oldest committed issued example once full, otherwise literal coefficient-zero ciphertext.','query':'Every active class in the current accepted model must have its complete fresh kernel proof accepted before any private read.','initial':'Fresh native keygen and literal zero ciphertext are trusted setup.','reader':'Surviving full BFV reader; protocol sequencing is not cryptographic decryption restriction.','scope':'Public encoder, encryption/key validity, lane/FIFO/request/recipient policy, parser/NTT maps and controller/backend TCB. Arithmetic is checked by existing Lean-derived relations.'}


def state_root(classes): return j.digest({'schema':'live-nonlinear-class-map-v1','classes':classes})

def initialize(root, classes):
    root=Path(root).resolve()
    j.need(not root.exists() and 1<=len(classes)<=1024 and len(classes)==len(set(classes)), 'fresh_instance_classes')
    j.need(all(isinstance(x,str) and 0<len(x)<=256 for x in classes),'class_labels')
    c=pipeline.config(); root.mkdir(parents=True,mode=0o700)
    (root/'issuer').mkdir(mode=0o700)
    command(root,'keygen',helper.native_argv('keygen',dir=root/'issuer'),300,ENV)
    zero=(root/'issuer/zero.ct').read_bytes(); zh=j.sha(zero)
    initial={label:{'acc_sha256':zh,'teaches':0,'queue':[]} for label in sorted(classes)}
    journal=root/'journal';journal.mkdir();j.write(journal/'cas'/zh,zero)
    genesis={'schema':'live-nonlinear-genesis-v1','classes':sorted(classes),'profile_sha256':sha(ROOT/'PIPELINE.json'),'source_pins':c['pins'],'policy':POLICY,'recipient_id':sha(root/'issuer/public.key'),'evaluation_key_sha256':sha(root/'issuer/evaluation.key'),'initial_classes':initial,'zero_sha256':zh,'created_utc':now()}
    j.write_json(journal/'genesis.json',genesis);gid=j.digest(genesis)
    state={'genesis':gid,'revision':0,'classes':initial,'model_root':state_root(initial),'last_receipt_sha256':None}
    db=j.connection(journal)
    try:
        db.execute('BEGIN IMMEDIATE')
        db.execute('CREATE TABLE head(singleton INTEGER PRIMARY KEY CHECK(singleton=1),state TEXT NOT NULL,state_sha256 TEXT NOT NULL)')
        db.execute('CREATE TABLE journal(revision INTEGER PRIMARY KEY,request_id TEXT UNIQUE NOT NULL,request_sha256 TEXT NOT NULL,receipt TEXT NOT NULL,receipt_sha256 TEXT NOT NULL)')
        db.execute('INSERT INTO head VALUES(1,?,?)',(j.canonical(state).decode(),j.digest(state)))
        db.execute('COMMIT')
    finally: db.close()
    return {'initialized':True,'genesis':gid,'head':state,'recipient_id':genesis['recipient_id'],'full_reader_key':True}


class Live:
    def __init__(self,root):
        self.root=Path(root).resolve();self.journal=self.root/'journal'
        self.genesis=j.read(self.journal/'genesis.json');self.gid=j.digest(self.genesis);self.encoder=None
        self.check();self.reopen()

    def check(self):
        j.need(j.read(self.journal/'genesis.json')==self.genesis and self.genesis['policy']==POLICY,'genesis_policy_changed')
        j.need(sha(ROOT/'PIPELINE.json')==self.genesis['profile_sha256'],'approved_profile_changed')
        check_pins(self.genesis['source_pins'])
        j.need(sha(self.root/'issuer/public.key')==self.genesis['recipient_id'] and sha(self.root/'issuer/evaluation.key')==self.genesis['evaluation_key_sha256'],'public_key_identity')

    @contextlib.contextmanager
    def locked(self):
        with (self.root/'adapter.lock').open('a') as lock:
            fcntl.flock(lock,fcntl.LOCK_EX)
            try:self.check();yield
            finally:fcntl.flock(lock,fcntl.LOCK_UN)

    def head(self,db=None):
        own=db is None;db=db or j.connection(self.journal)
        try:
            row=db.execute('SELECT state,state_sha256 FROM head WHERE singleton=1').fetchone();state=j.parse(row['state'])
            j.need(j.digest(state)==row['state_sha256'] and state['genesis']==self.gid and state['model_root']==state_root(state['classes']),'head_identity')
            return state
        finally:
            if own:db.close()

    def cas(self,digest):
        path=self.journal/'cas'/digest
        j.need(re.fullmatch('[a-f0-9]{64}',digest) is not None,'cas_identifier')
        raw=j.regular_bytes(path);j.need(j.sha(raw)==digest,'cas_identity');return raw

    def reopen(self):
        state={'genesis':self.gid,'revision':0,'classes':self.genesis['initial_classes'],'model_root':state_root(self.genesis['initial_classes']),'last_receipt_sha256':None}
        db=j.connection(self.journal)
        try:
            for row in db.execute('SELECT * FROM journal ORDER BY revision'):
                receipt=j.parse(row['receipt']);req=receipt['request']
                j.need(j.digest(receipt)==row['receipt_sha256'] and j.digest(req)==row['request_sha256'],'receipt_identity')
                self.parent(state,req)
                j.need(receipt['proof_acceptance']['verified'] and receipt['proof_acceptance']['proofs_verified']==8 and receipt['proof_acceptance']['binding']==req['payloads'],'retained_update_acceptance')
                for digest in req['payloads'].values():self.cas(digest)
                state=self.advance(state,req,row['receipt_sha256'])
            j.need(state==self.head(db),'reopened_committed_chain')
        finally:db.close()

    def directory(self,kind,request_id):
        j.need(isinstance(request_id,str) and re.fullmatch('[A-Za-z0-9_-]{1,80}',request_id),'request_id')
        return self.root/kind/request_id

    def vector(self,text):
        j.need(isinstance(text,str) and text.strip(),'supplied_text')
        if self.encoder is None:self.encoder=helper.TextEncoder(self.root/'encoder_cache')
        return self.encoder.encode([text])[0]

    def parent(self,state,req):
        label=req['label'];entry=state['classes'][label]
        j.need(req['genesis']==self.gid and req['recipient_id']==self.genesis['recipient_id'],'request_genesis_recipient')
        j.need(req['parent_sha256']==j.digest(state) and req['revision']==state['revision']+1 and req['parent_model_root']==state['model_root'],'current_model_parent')
        q=entry['queue'];old=q[0]['sha256'] if len(q)==8 else self.genesis['zero_sha256']
        j.need(req['payloads']['acc_sha256']==entry['acc_sha256'] and req['payloads']['old_sha256']==old and req['lane']==entry['teaches']%8,'current_class_lane_fifo')
        j.need(req['profile_sha256']==self.genesis['profile_sha256'],'request_profile')

    def advance(self,state,req,receipt_sha):
        classes=dict(state['classes']);entry=classes[req['label']];queue=list(entry['queue'])
        if len(queue)==8:queue.pop(0)
        queue.append({'sha256':req['payloads']['fresh_sha256'],'lane':req['lane']})
        classes[req['label']]={'acc_sha256':req['payloads']['out_sha256'],'teaches':entry['teaches']+1,'queue':queue}
        return {'genesis':self.gid,'revision':state['revision']+1,'classes':classes,'model_root':state_root(classes),'last_receipt_sha256':receipt_sha}

    def teach_vector(self,label,vector,text,request_id):
        with self.locked():
            head=self.head();j.need(label in head['classes'],'declared_class')
            out=self.directory('teaching',request_id);j.need(not out.exists(),'fresh_teach_request')
            out.mkdir(parents=True);case=out/'candidate';case.mkdir()
            entry=head['classes'][label];queue=entry['queue'];lane=entry['teaches']%8
            old=queue[0]['sha256'] if len(queue)==8 else self.genesis['zero_sha256']
            j.write_json(out/'vector.json',vector)
            j.write(case/'acc.ct',self.cas(entry['acc_sha256']));j.write(case/'old.ct',self.cas(old))
            command(out,'issue',helper.native_argv('issue',dir=self.root/'issuer',vector=out/'vector.json',lane=lane,out=case/'fresh.ct'),120,ENV)
            command(out,'learn',helper.native_argv('learn',acc=case/'acc.ct',fresh=case/'fresh.ct',old=case/'old.ct',out=case/'out.ct'),120,ENV)
            produced=pipeline.produce_update(case,out/'produced')
            req={'schema':'live-nonlinear-update-v1','request_id':request_id,'genesis':self.gid,'recipient_id':self.genesis['recipient_id'],'revision':head['revision']+1,'parent_sha256':j.digest(head),'parent_model_root':head['model_root'],'label':label,'lane':lane,'text_sha256':j.sha(text.encode()),'feature_sha256':sha(out/'vector.json'),'payloads':produced['binding'],'profile_sha256':self.genesis['profile_sha256']}
            self.parent(head,req);j.write_json(out/'request.json',req)
            accepted=pipeline.verify_update(req['payloads'],out/'produced',out/'verification')
            self.check();db=j.connection(self.journal)
            try:
                db.execute('BEGIN IMMEDIATE');self.parent(self.head(db),req)
                for role,digest in req['payloads'].items():
                    raw=(case/(role.removesuffix('_sha256')+'.ct')).read_bytes();j.need(j.sha(raw)==digest,'verified_update_bytes')
                    path=self.journal/'cas'/digest
                    if path.exists():j.need(self.cas(digest)==raw,'immutable_cas_conflict')
                    else:j.write(path,raw)
                receipt={'schema':'live-nonlinear-teach-receipt-v1','request':req,'proof_acceptance':accepted,'parent_checked_inside_commit':True,'accepted_utc':now()}
                digest=j.digest(receipt);new=self.advance(head,req,digest)
                db.execute('INSERT INTO journal VALUES(?,?,?,?,?)',(new['revision'],request_id,j.digest(req),j.canonical(receipt).decode(),digest))
                db.execute('UPDATE head SET state=?,state_sha256=? WHERE singleton=1',(j.canonical(new).decode(),j.digest(new)))
                db.execute('COMMIT')
            except BaseException:
                if db.in_transaction:db.execute('ROLLBACK')
                raise
            finally:db.close()
            result={'committed':True,'head':new,'receipt_sha256':digest,'request':req,'private_reads':0}
            j.write_json(out/'committed.json',result);return result

    def teach(self,label,text,request_id):return self.teach_vector(label,self.vector(text),text,request_id)

    def prepare_query(self,vector,text,request_id):
        with self.locked():
            head=self.head();active=sorted(c for c,e in head['classes'].items() if e['queue']);j.need(active,'active_classes')
            out=self.directory('queries',request_id);j.need(not out.exists(),'fresh_query_request');out.mkdir(parents=True)
            j.write_json(out/'query.json',vector)
            req={'schema':'live-nonlinear-query-v1','request_id':request_id,'genesis':self.gid,'recipient_id':self.genesis['recipient_id'],'revision':head['revision'],'head_sha256':j.digest(head),'model_root':head['model_root'],'profile_sha256':self.genesis['profile_sha256'],'evaluation_key_sha256':self.genesis['evaluation_key_sha256'],'query_sha256':sha(out/'query.json'),'text_sha256':j.sha(text.encode()),'active_classes':active,'classes':{}}
            for i,label in enumerate(active):
                acc=head['classes'][label]['acc_sha256'];self.cas(acc);job=out/f'class{i:03}'
                job.mkdir();helper.capture(self.root/'issuer',self.journal/'cas'/acc,out/'query.json',job/'capture',head['revision'],label)
                result=pipeline.produce_infer(self.journal/'cas'/acc,out/'query.json',self.root/'issuer/evaluation.key',job/'capture',job/'produced')
                req['classes'][label]={'model_ciphertext_sha256':acc,'kernel_ciphertext_sha256':result['binding']['kernel_ciphertext_sha256'],'count':len(head['classes'][label]['queue']),'job':str(job)}
            j.need(self.head()==head,'model_changed_during_query')
            j.write_json(out/'request.json',req)
            j.write_json(out/'prepared.json',{'prepared':True,'private_reads':0,'request_sha256':j.digest(req),'finished_utc':now()})
            return req

    def query_binding(self,head,req):
        active=sorted(c for c,e in head['classes'].items() if e['queue'])
        j.need(req['genesis']==self.gid and req['recipient_id']==self.genesis['recipient_id'] and req['profile_sha256']==self.genesis['profile_sha256'],'query_genesis_profile')
        j.need(req['revision']==head['revision'] and req['head_sha256']==j.digest(head) and req['model_root']==head['model_root'],'query_current_revision')
        j.need(req['active_classes']==active and set(req['classes'])==set(active),'all_active_classes_required')
        j.need(req['evaluation_key_sha256']==self.genesis['evaluation_key_sha256'],'query_evaluation_key')
        for label,e in req['classes'].items():
            j.need(e['model_ciphertext_sha256']==head['classes'][label]['acc_sha256'] and e['count']==len(head['classes'][label]['queue']),'query_class_current_model')

    def accept_query(self,request_id):
        with self.locked():
            out=self.directory('queries',request_id);req=j.read(out/'request.json');head=self.head();self.query_binding(head,req)
            acceptance_path=out/'public_acceptance.json';j.need(not acceptance_path.exists(),'fresh_query_acceptance')
            checks={};outputs={}
            for label,e in req['classes'].items():
                expected={k:e[k] for k in ('model_ciphertext_sha256','kernel_ciphertext_sha256')}
                expected.update(query_sha256=req['query_sha256'],evaluation_key_sha256=req['evaluation_key_sha256'])
                job=Path(e['job']);checks[label]=pipeline.verify_infer(expected,job/'produced',job/'verification')
                outputs[label]=str(job/'produced/infer_case/expected_kernel.ct')
            self.check();db=j.connection(self.journal)
            try:
                db.execute('BEGIN IMMEDIATE');self.query_binding(self.head(db),req)
                acceptance={'all_active_classes_verified':True,'head':head,'request':req,'request_sha256':j.digest(req),'profile_sha256':self.genesis['profile_sha256'],'checks':checks,'outputs':outputs,'private_reads':0,'public_phase_complete_utc':now(),'head_checked_under_write_lock':True}
                j.write_json(acceptance_path,acceptance);db.execute('COMMIT')
            finally:db.close()
            return acceptance

    def receive(self,request_id):
        with self.locked():
            out=self.directory('queries',request_id);req=j.read(out/'request.json');self.query_binding(self.head(),req)
            acceptance=j.read(out/'public_acceptance.json')
            j.need(acceptance['all_active_classes_verified'] and acceptance['head_checked_under_write_lock'] and acceptance['request_sha256']==j.digest(req) and acceptance['request']==req and set(acceptance['checks'])==set(req['active_classes']),'all_proofs_before_private_receive')
            j.need(not (out/'receive_started.json').exists(),'single_receive_attempt')
            for label,path in acceptance['outputs'].items():
                j.need(sha(Path(path))==req['classes'][label]['kernel_ciphertext_sha256'] and acceptance['checks'][label]['complete_infer_verified'] and acceptance['checks'][label]['proofs_verified']==116,'accepted_reader_output')
            j.write_json(out/'receive_started.json',{'utc':now(),'public_acceptance_sha256':sha(out/'public_acceptance.json')})
            answers={}
            for i,label in enumerate(req['active_classes']):
                command(out,f'read{i:03}',helper.native_argv('read',dir=self.root/'issuer',ct=acceptance['outputs'][label]),120,ENV)
                answers[label]=j.read(out/f'read{i:03}.stdout')
            # Compare exact rational class means without floating-point ranking.
            from fractions import Fraction
            order=sorted(answers,key=lambda c:(-Fraction(answers[c]['sum_kernel'],req['classes'][c]['count']),c))
            result={'answered':True,'prediction':order[0],'ranking':order,'classes':answers,'counts':{c:req['classes'][c]['count'] for c in answers},'revision':req['revision'],'model_root':req['model_root'],'public_acceptance_sha256':sha(out/'public_acceptance.json'),'private_reads':len(answers),'finished_utc':now(),'full_reader':True}
            j.write_json(out/'answer.json',result);return result

    def query_vector(self,vector,text,request_id):
        self.prepare_query(vector,text,request_id);self.accept_query(request_id);return self.receive(request_id)
    def query(self,text,request_id):return self.query_vector(self.vector(text),text,request_id)


def main():
    p=argparse.ArgumentParser(description=__doc__);s=p.add_subparsers(dest='action',required=True)
    a=s.add_parser('init');a.add_argument('root');a.add_argument('--class',dest='classes',action='append',required=True)
    for name in ('teach','query','status'):
        a=s.add_parser(name);a.add_argument('root')
        if name!='status':a.add_argument('--text',required=True);a.add_argument('--request-id',required=True)
        if name=='teach':a.add_argument('--label',required=True)
    a=p.parse_args()
    if a.action=='init':r=initialize(a.root,a.classes)
    else:
        live=Live(a.root)
        if a.action=='teach':r=live.teach(a.label,a.text,a.request_id)
        elif a.action=='query':r=live.query(a.text,a.request_id)
        else:r=live.head()
    print(json.dumps(r,indent=2))

if __name__=='__main__':main()
