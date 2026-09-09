#!/usr/bin/env python3
"""Whitelist public proof bundles; replay via the existing pinned workspace only."""
import argparse
import copy
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import sqlite3
import stat

HERE = Path(__file__).resolve().parent
ID = re.compile(r'[A-Za-z0-9_-]{1,80}')
HEX = re.compile(r'[a-f0-9]{64}')
COUNTS = {'update':8, 'infer':88, 'extension':4, 'tensor':18, 'rescale':6}


def need(ok, message):
    if not ok:
        raise ValueError(message)


def canonical(value):
    return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False).encode()


def digest(value):
    return hashlib.sha256(canonical(value)).hexdigest()


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''):
            h.update(b)
    return h.hexdigest()


def regular(path):
    path = Path(path)
    need(path.is_absolute() and path.resolve()==path and stat.S_ISREG(path.lstat().st_mode),
         'regular nonsymlink public file required: '+str(path))
    return path


def read(path):
    return json.loads(regular(path).read_text())


def save(path, value):
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('xb') as f:
        f.write(canonical(value)+b'\n')


def model_root(classes):
    return digest({'schema':'live-nonlinear-class-map-v1','classes':classes})


def public_history(genesis, head, journal):
    """Check public hash/parent/FIFO metadata; this is controller code, not AIR."""
    gid = digest(genesis)
    need(genesis['schema']=='live-nonlinear-genesis-v1','genesis schema')
    classes = copy.deepcopy(genesis['initial_classes'])
    need(sorted(classes)==genesis['classes'] and 1<=len(classes)<=1024,'declared class set')
    need(HEX.fullmatch(genesis['recipient_id']) and HEX.fullmatch(genesis['zero_sha256']), 'setup identity')
    for entry in classes.values():
        need(entry=={'acc_sha256':genesis['zero_sha256'],'teaches':0,'queue':[]},'initial class state')
    state = {'genesis':gid,'revision':0,'classes':classes,'model_root':model_root(classes),'last_receipt_sha256':None}
    heads = {0:copy.deepcopy(state)}
    for i,row in enumerate(journal,1):
        receipt = row['receipt'];req = receipt['request'];rid = req['request_id']
        need(ID.fullmatch(rid) and row['revision']==i and row['request_id']==rid, 'journal sequence')
        need(row['receipt_sha256']==digest(receipt) and row['request_sha256']==digest(req),'receipt hash')
        need(req['genesis']==gid and req['recipient_id']==genesis['recipient_id'] and req['profile_sha256']==genesis['profile_sha256'],'teaching context')
        need(req['revision']==i and req['parent_sha256']==digest(state) and req['parent_model_root']==state['model_root'],'teaching parent')
        entry = state['classes'][req['label']];queue = list(entry['queue']);payload = req['payloads']
        need(set(payload)=={'acc_sha256','fresh_sha256','old_sha256','out_sha256'} and all(HEX.fullmatch(x) for x in payload.values()),'teaching payload roles')
        old = queue[0]['sha256'] if len(queue)==8 else genesis['zero_sha256']
        need(payload['acc_sha256']==entry['acc_sha256'] and payload['old_sha256']==old and req['lane']==entry['teaches']%8,'teaching FIFO/lane')
        acceptance = receipt['proof_acceptance']
        need(acceptance['verified'] and acceptance['proofs_verified']==8 and acceptance['binding']==payload and receipt['parent_checked_inside_commit'],'retained update acceptance')
        if len(queue)==8:queue.pop(0)
        queue.append({'sha256':payload['fresh_sha256'],'lane':req['lane']})
        classes = copy.deepcopy(state['classes'])
        classes[req['label']] = {'acc_sha256':payload['out_sha256'],'teaches':entry['teaches']+1,'queue':queue}
        state = {'genesis':gid,'revision':i,'classes':classes,'model_root':model_root(classes),'last_receipt_sha256':row['receipt_sha256']}
        heads[i] = copy.deepcopy(state)
    need(state==head,'exported committed head')
    return heads


def query_jobs(request, acceptance, genesis, heads):
    need(ID.fullmatch(request['request_id']) and request['schema']=='live-nonlinear-query-v1','query identifier/schema')
    head = heads[request['revision']]
    active = sorted(c for c,e in head['classes'].items() if e['queue'])
    need(request['genesis']==digest(genesis) and request['recipient_id']==genesis['recipient_id'],'query genesis/recipient')
    need(request['profile_sha256']==genesis['profile_sha256'] and request['evaluation_key_sha256']==genesis['evaluation_key_sha256'],'query profile/key')
    need(request['head_sha256']==digest(head) and request['model_root']==head['model_root'],'query committed revision')
    need(request['active_classes']==active and set(request['classes'])==set(active) and active,'all active classes required')
    need(acceptance['request']==request and acceptance['request_sha256']==digest(request) and acceptance['head']==head,'accepted query identity')
    need(acceptance['all_active_classes_verified'] and acceptance['head_checked_under_write_lock'] and set(acceptance['checks'])==set(active) and set(acceptance['outputs'])==set(active),'accepted all-class gate')
    result = []
    for index,label in enumerate(active):
        entry = request['classes'][label]
        need(entry['model_ciphertext_sha256']==head['classes'][label]['acc_sha256'] and entry['count']==len(head['classes'][label]['queue']),'query model/count')
        expected = {k:entry[k] for k in ('model_ciphertext_sha256','kernel_ciphertext_sha256')}
        expected.update(query_sha256=request['query_sha256'],evaluation_key_sha256=request['evaluation_key_sha256'])
        check = acceptance['checks'][label]
        need(check['complete_infer_verified'] and check['proofs_verified']==116 and all(check['binding'][k]==v for k,v in expected.items()),'retained complete Infer acceptance')
        result.append({'index':index,'label':label,'count':entry['count'],'expected':expected})
    return result


def case_names(kind):
    if kind=='update':
        return ['operation.json']+[x+'.ct' for x in ('acc','fresh','old','out')]+[f'rows/{i:03}.json' for i in range(8)]
    if kind=='infer':
        return ['operation.json','model.ct','query.json','evaluation.key','expected_dot.ct','expected_kernel.ct']+[f'steps/{i:02}.ct' for i in range(11)]+[f'rows/{i:03}.json' for i in range(88)]
    shared = ['operation.json','source_descriptor.json','basic.json','basic.dot.ct','basic-000.ct']
    if kind=='square':
        return shared+['extension_power.json','native_extension_constants.json']+[f'extension/{i:03}.json' for i in range(4)]+[f'tensor/{i:03}.json' for i in range(18)]
    need(kind=='rescale','known public case schema')
    return shared+[f'chunks/{i:03}.json' for i in range(6)]


class Bundle:
    def __init__(self, root, output):
        self.root=root;self.output=output;self.files={}

    def copy(self, source, relative):
        source=regular(source);relative=Path(relative)
        need(not relative.is_absolute() and '..' not in relative.parts,'bundle-relative path')
        need(not any(x in relative.parts for x in ('.private','encoder_cache')),'private/cache export forbidden')
        need(not any(x.startswith('read') or x in ('answer.json','receive_started.json','reader.key') for x in relative.parts),'answer/reader export forbidden')
        target=self.output/relative;target.parent.mkdir(parents=True,exist_ok=True)
        with source.open('rb') as src,target.open('xb') as dst:
            shutil.copyfileobj(src,dst,1024*1024)
        hs=sha(source);need(sha(target)==hs,'copied public file changed')
        self.files[str(relative)]={'sha256':hs,'bytes':target.stat().st_size}

    def json(self, relative, value):
        target=self.output/relative;save(target,value)
        self.files[str(relative)]={'sha256':sha(target),'bytes':target.stat().st_size}

    def produced(self, source, relative, operation):
        self.copy(source/'result.json',relative/'result.json')
        cases=[('case','update')] if operation=='update' else [('infer_case','infer'),('square_case','square'),('rescale_case','rescale')]
        for folder,kind in cases:
            for name in case_names(kind):self.copy(source/folder/name,relative/folder/name)
        phases=[('proofs','update')] if operation=='update' else [(k,k) for k in ('infer','extension','tensor','rescale')]
        for folder,kind in phases:
            for i in range(COUNTS[kind]):
                for name in ('proof.bin','proof.json'):
                    self.copy(source/folder/f'chunk{i:03}'/name,relative/folder/f'chunk{i:03}'/name)


def export(instance, output, selected):
    instance=Path(instance).resolve();output=Path(output).absolute()
    need(instance.exists() and not output.exists() and output.resolve()==output,'fresh canonical export directory')
    need(instance!=output and instance not in output.parents,'export must be outside the instance')
    # Shared lock is read-only and nonblocking. No background run is paused.
    with regular(instance/'adapter.lock').open('rb') as lock:
        fcntl.flock(lock,fcntl.LOCK_SH|fcntl.LOCK_NB)
        import pipeline
        config=pipeline.config()
        genesis=read(instance/'journal/genesis.json')
        need(sha(HERE/'PIPELINE.json')==genesis['profile_sha256'] and config['pins']==genesis['source_pins'],'current approved workspace/profile')
        database=regular(instance/'journal/journal.sqlite3')
        db=sqlite3.connect(database.as_uri()+'?mode=ro',uri=True,isolation_level=None)
        db.row_factory=sqlite3.Row
        try:
            db.execute('BEGIN')
            row=db.execute('SELECT state,state_sha256 FROM head WHERE singleton=1').fetchone()
            head=json.loads(row['state']);need(digest(head)==row['state_sha256'],'stored head hash')
            journal=[]
            for row in db.execute('SELECT * FROM journal ORDER BY revision'):
                item=dict(row);item['receipt']=json.loads(item['receipt']);journal.append(item)
        finally:db.close()
        heads=public_history(genesis,head,journal)
        if selected is None:
            selected=sorted(p.name for p in (instance/'queries').iterdir() if p.is_dir() and (p/'public_acceptance.json').is_file()) if (instance/'queries').exists() else []
        need(len(selected)==len(set(selected)) and all(ID.fullmatch(x) for x in selected),'unique selected query identifiers')
        selected_data=[]
        for rid in selected:
            folder=instance/'queries'/rid;req=read(folder/'request.json');acceptance=read(folder/'public_acceptance.json')
            need(req['request_id']==rid,'selected request id')
            selected_data.append((rid,req,acceptance,query_jobs(req,acceptance,genesis,heads)))
        output.mkdir(parents=True)
        bundle=Bundle(instance,output)
        bundle.copy(HERE/'PIPELINE.json',Path('profile/PIPELINE.json'))
        bundle.json(Path('DEPENDENCIES.json'),{'mode':'Current pinned workspace required; native binaries/source/templates/linear plan are not bundled.','profile_sha256':genesis['profile_sha256'],'pins':config['pins'],'pipeline_path':str(HERE/'pipeline.py'),'pipeline_sha256':sha(HERE/'pipeline.py'),'exporter_sha256':sha(Path(__file__).resolve())})
        bundle.copy(instance/'journal/genesis.json',Path('journal/genesis.json'))
        bundle.json(Path('journal/head.json'),head);bundle.json(Path('journal/receipts.json'),journal)
        for name in ('public.key','evaluation.key','parameters.json','zero.ct'):
            bundle.copy(instance/'issuer'/name,Path('public_setup')/name)
        need(sha(output/'public_setup/public.key')==genesis['recipient_id'] and sha(output/'public_setup/evaluation.key')==genesis['evaluation_key_sha256'] and sha(output/'public_setup/zero.ct')==genesis['zero_sha256'],'public setup identity')
        jobs=[]
        for row in journal:
            req=row['receipt']['request'];rid=req['request_id'];folder=instance/'teaching'/rid;target=Path('teaching')/rid
            need(read(folder/'request.json')==req,'teaching request/receipt join')
            committed=read(folder/'committed.json');need(committed['receipt_sha256']==row['receipt_sha256'] and committed['head']==heads[req['revision']],'teaching commit snapshot')
            for name in ('request.json','committed.json'):bundle.copy(folder/name,target/name)
            bundle.produced(folder/'produced',target/'produced','update')
            bundle.json(target/'expected.json',req['payloads'])
            jobs.append({'kind':'update','request_id':rid,'revision':req['revision'],'produced':str(target/'produced'),'expected':str(target/'expected.json')})
        for rid,req,acceptance,classes in selected_data:
            folder=instance/'queries'/rid;target=Path('queries')/rid
            for name in ('request.json','prepared.json','public_acceptance.json','query.json'):bundle.copy(folder/name,target/name)
            need(sha(output/target/'query.json')==req['query_sha256'],'public query hash')
            for entry in classes:
                index=entry['index'];label=entry['label'];source=folder/f'class{index:03}';dest=target/f'class{index:03}'
                need(Path(req['classes'][label]['job']).resolve()==source.resolve(),'canonical query job path')
                bundle.produced(source/'produced',dest/'produced','infer')
                bundle.json(dest/'expected.json',entry['expected'])
                jobs.append({'kind':'infer','request_id':rid,'revision':req['revision'],'label':label,'count':entry['count'],'produced':str(dest/'produced'),'expected':str(dest/'expected.json')})
        manifest={'schema':'live-nonlinear-public-bundle-v1','genesis_sha256':digest(genesis),'head_sha256':digest(head),'recipient_id':genesis['recipient_id'],'profile_sha256':genesis['profile_sha256'],'revision':head['revision'],'model_root':head['model_root'],'selected_accepted_queries':selected,'jobs':jobs,'files':bundle.files,'boundaries':'Unsigned export of a continuing accepted model snapshot. Caller supplies manifest/genesis/head/recipient digests. Historical selected queries bind their accepted revisions and every then-active class. Full reader remains outside bundle. Verification requires current pinned workspace; not standalone or a new privacy claim.','private_files_exported':0,'answers_exported':0,'proofs_reexecuted':0}
        need(set(manifest['files'])==expected_public_paths(manifest),'exact public export whitelist')
        save(output/'BUNDLE.json',manifest)
        return {'bundle':str(output),'manifest_sha256':sha(output/'BUNDLE.json'),'genesis_sha256':manifest['genesis_sha256'],'head_sha256':manifest['head_sha256'],'recipient_id':manifest['recipient_id'],'files':len(bundle.files),'bytes':sum(x['bytes'] for x in bundle.files.values()),'private_files_exported':0,'proofs_reexecuted':0}


def expected_public_paths(manifest):
    """Exact replay file whitelist, checked before opening bundled file payloads."""
    paths = {'profile/PIPELINE.json','DEPENDENCIES.json','journal/genesis.json',
             'journal/head.json','journal/receipts.json','public_setup/public.key',
             'public_setup/evaluation.key','public_setup/parameters.json','public_setup/zero.ct'}
    selected = manifest['selected_accepted_queries']
    need(len(selected)==len(set(selected)) and all(ID.fullmatch(x) for x in selected),'selected query identifiers')
    for rid in selected:
        for name in ('request.json','prepared.json','public_acceptance.json','query.json'):
            paths.add(str(Path('queries')/rid/name))
    for job in manifest['jobs']:
        rid=job['request_id'];kind=job['kind'];need(ID.fullmatch(rid),'job request identifier')
        produced=Path(job['produced']);base=produced.parent
        if kind=='update':
            need(produced==Path('teaching')/rid/'produced','update bundle path')
            for name in ('request.json','committed.json','expected.json'):paths.add(str(base/name))
            cases=[('case','update')];phases=[('proofs','update')]
        else:
            need(kind=='infer' and rid in selected and re.fullmatch(r'queries/'+re.escape(rid)+r'/class[0-9]{3,4}/produced',str(produced)), 'Infer bundle path')
            paths.add(str(base/'expected.json'))
            cases=[('infer_case','infer'),('square_case','square'),('rescale_case','rescale')]
            phases=[(k,k) for k in ('infer','extension','tensor','rescale')]
        need(job['expected']==str(base/'expected.json'),'expected binding path')
        paths.add(str(produced/'result.json'))
        for folder,case in cases:
            paths.update(str(produced/folder/name) for name in case_names(case))
        for folder,phase in phases:
            paths.update(str(produced/folder/f'chunk{i:03}'/name)
                         for i in range(COUNTS[phase]) for name in ('proof.bin','proof.json'))
    return paths


def replay(bundle, output, manifest_sha256, genesis_sha256, head_sha256, recipient_id):
    bundle=Path(bundle).resolve();output=Path(output).absolute()
    need(not output.exists() and output.resolve()==output and bundle not in output.parents,'new replay directory outside bundle')
    need(sha(regular(bundle/'BUNDLE.json'))==manifest_sha256,'caller-selected manifest')
    m=read(bundle/'BUNDLE.json');need(m['schema']=='live-nonlinear-public-bundle-v1','bundle schema')
    need((m['genesis_sha256'],m['head_sha256'],m['recipient_id'])==(genesis_sha256,head_sha256,recipient_id),'caller-selected continuing model/recipient')
    need(set(m['files'])==expected_public_paths(m),'exact public replay whitelist')
    for relative,row in m['files'].items():
        rel=Path(relative);need(not rel.is_absolute() and '..' not in rel.parts,'bundle relative artifact')
        path=regular(bundle/rel);need(path.stat().st_size==row['bytes'] and sha(path)==row['sha256'],'bundle artifact hash')
    genesis=read(bundle/'journal/genesis.json');head=read(bundle/'journal/head.json');journal=read(bundle/'journal/receipts.json')
    need(digest(genesis)==genesis_sha256 and digest(head)==head_sha256 and genesis['recipient_id']==recipient_id,'bundle root identity')
    heads=public_history(genesis,head,journal)
    need(sha(bundle/'public_setup/public.key')==recipient_id and sha(bundle/'public_setup/evaluation.key')==genesis['evaluation_key_sha256'] and sha(bundle/'public_setup/zero.ct')==genesis['zero_sha256'],'bundled public setup identity')
    expected_jobs=[]
    for row in journal:
        req=row['receipt']['request'];target=Path('teaching')/req['request_id']
        need(read(bundle/target/'request.json')==req and read(bundle/target/'expected.json')==req['payloads'],'public update expected binding')
        expected_jobs.append({'kind':'update','request_id':req['request_id'],'revision':req['revision'],'produced':str(target/'produced'),'expected':str(target/'expected.json')})
    for rid in m['selected_accepted_queries']:
        need(ID.fullmatch(rid),'selected query identifier');target=Path('queries')/rid
        req=read(bundle/target/'request.json');acceptance=read(bundle/target/'public_acceptance.json')
        for entry in query_jobs(req,acceptance,genesis,heads):
            dest=target/f"class{entry['index']:03}"
            need(read(bundle/dest/'expected.json')==entry['expected'],'public Infer expected binding')
            expected_jobs.append({'kind':'infer','request_id':rid,'revision':req['revision'],'label':entry['label'],'count':entry['count'],'produced':str(dest/'produced'),'expected':str(dest/'expected.json')})
    need(m['jobs']==expected_jobs,'exact all-history/all-active-class replay jobs')
    import pipeline
    c=pipeline.config();need(sha(HERE/'PIPELINE.json')==m['profile_sha256']==genesis['profile_sha256'] and c['pins']==genesis['source_pins'],'current pinned workspace required')
    output.mkdir(parents=True);checks=[]
    for i,job in enumerate(expected_jobs):
        expected=read(bundle/job['expected']);produced=bundle/job['produced'];dest=output/f'job{i:04}'
        check=pipeline.verify_update(expected,produced,dest) if job['kind']=='update' else pipeline.verify_infer(expected,produced,dest)
        checks.append({'job':job,'proofs_verified':check['proofs_verified'],'result_sha256':sha(dest/'result.json')})
    result={'public_replay_complete':True,'manifest_sha256':manifest_sha256,'genesis_sha256':genesis_sha256,'head_sha256':head_sha256,'recipient_id':recipient_id,'checks':checks,'proofs_verified':sum(x['proofs_verified'] for x in checks),'private_files_read':0,'scope':'Existing approved public pipeline verification in pinned workspace, with exact exported history/query bindings; no issuer secret, encoder or recipient decryption.'}
    save(output/'RESULT.json',result);return result


def main():
    p=argparse.ArgumentParser(description=__doc__);sub=p.add_subparsers(dest='action',required=True)
    x=sub.add_parser('export');x.add_argument('instance');x.add_argument('output');x.add_argument('--query',action='append',dest='queries')
    x=sub.add_parser('replay');x.add_argument('bundle');x.add_argument('output')
    for name in ('manifest-sha256','genesis-sha256','head-sha256','recipient-id'):x.add_argument('--'+name,required=True)
    a=p.parse_args()
    result=export(a.instance,a.output,a.queries) if a.action=='export' else replay(a.bundle,a.output,a.manifest_sha256,a.genesis_sha256,a.head_sha256,a.recipient_id)
    print(json.dumps(result,indent=2))

if __name__=='__main__':main()
