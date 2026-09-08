#!/usr/bin/env python3
"""Package public recorded query receipts with the unchanged frozen WASM core."""
from pathlib import Path
import hashlib,json,shutil,gzip
ROOT=Path(__file__).resolve().parent;LANES=ROOT.parent
SOURCE=LANES/'proved_journal/query_gate_successor/results/gated001'
PREDECESSOR=LANES/'browser_verifier'
sha=lambda b:hashlib.sha256(b).hexdigest()
ROOT.mkdir(exist_ok=True)
prior=json.loads((PREDECESSOR/'BROWSER_PACKAGE.json').read_text())
backend=prior['backend'];copied={}
def copy(source,relative,expected=None):
 data=source.read_bytes();digest=sha(data)
 if expected:assert digest==expected,(source,'pin mismatch')
 target=ROOT/relative;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
 copied[relative]={'bytes':len(data),'sha256':digest,'gzip9_bytes':len(gzip.compress(data,compresslevel=9,mtime=0)),'source':str(source.resolve())}
for item in prior['files']:
 rel=item['path']
 if rel in ['web/verifier.js','web/package.json'] or rel.startswith('web/pkg/'):
  copy(PREDECESSOR/rel,rel,item['sha256'])
accepted=json.loads((SOURCE/'public_acceptance.json').read_text())
envelope=json.loads((SOURCE/'request.json').read_text());request=envelope['request']
assert request==accepted['request']
assert request['active_classes']==['card_arrival','cash_withdrawal_charge']
template=LANES/'query_arithmetic/artifacts/template_ir2.json'
copy(template,'fixtures/template.json',request['template_sha256'])
copy(SOURCE/'request.json','fixtures/request.json')
cases=[]
for index,label in enumerate(request['active_classes']):
 folder=SOURCE/f'class{index}';info=json.loads((folder/'proof/proof.json').read_text())
 assert info['backend']==backend and info['template_sha256']==request['template_sha256']
 assert info['public_rows_sha256']==request['classes'][label]['rows_sha256']
 assert info['proof_sha256']==request['classes'][label]['proof_sha256']
 rows=f'fixtures/class{index}/public_rows.json';proof=f'fixtures/class{index}/proof.bin'
 copy(folder/'case/public_rows.json',rows,info['public_rows_sha256']);copy(folder/'proof/proof.bin',proof,info['proof_sha256'])
 values=json.loads((ROOT/rows).read_text());assert len(values)==8192 and all(len(row)==57 for row in values)
 assert all(row[0]==i for i,row in enumerate(values))
 cases.append({'label':label,'publicRowsPath':rows,'proofPath':proof,'rows':8192,'publicWidth':57,
   'accumulatorSha256':request['classes'][label]['acc_sha256'],'outputCiphertextSha256':request['classes'][label]['out_sha256']})
case={'schema':'recorded-two-class-query-wasm-v1','id':'gated001-new-two-class-query','requestId':request['request_id'],
 'expectedBackend':backend,'expectedTemplateSha256':request['template_sha256'],
 'templatePath':'fixtures/template.json','requestPath':'fixtures/request.json','wasmPath':'web/pkg/vfhe_browser_verifier_bg.wasm',
 'publicQuerySha256':request['query_sha256'],'recordedModelRoot':request['model_root'],'recordedRevision':request['revision'],
 'scope':'Both recorded class ciphertext query computations: two signed products and subtraction. No encoder, decryption or authorization proof.',
 'cases':cases,'files':{rel:{k:v for k,v in info.items() if k in ['bytes','sha256']} for rel,info in copied.items()}}
(ROOT/'query-case.json').write_text(json.dumps(case,indent=2)+'\n')
(ROOT/'web/query-case.js').write_text('// Application-selected transport pins for this exact retained public case.\nconst freeze = value => { if (value && typeof value === "object") { for (const item of Object.values(value)) freeze(item); Object.freeze(value); } return value; };\nexport const QUERY_CASE = freeze('+json.dumps(case,indent=2)+');\n')
record={'predecessor_package_sha256':sha((PREDECESSOR/'BROWSER_PACKAGE.json').read_bytes()),'source_public_request_sha256':sha((SOURCE/'request.json').read_bytes()),
 'source_public_acceptance_sha256':sha((SOURCE/'public_acceptance.json').read_bytes()),'copied_files':copied,
 'wasm_rebuilt':False,'new_proof_generated':False,'private_files_read':0}
(ROOT/'source_provenance.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':'PASS','copied_files':len(copied),'core_wasm_sha256':case['files'][case['wasmPath']]['sha256'],
 'copied_uncompressed_bytes':sum(v['bytes'] for v in copied.values()),'copied_gzip9_bytes':sum(v['gzip9_bytes'] for v in copied.values()),'classes':[c['label'] for c in cases]},indent=2))
