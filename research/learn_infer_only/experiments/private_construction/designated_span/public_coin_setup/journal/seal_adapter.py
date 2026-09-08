#!/usr/bin/env python3
"""Rehash only saved public adapter evidence; never execute crypto/read private files."""
from pathlib import Path
import collections, hashlib, json
HERE=Path(__file__).resolve().parent
BASE=HERE.parent
ADAPTER=BASE/'adapter'
REPORTS=ADAPTER/'reports/positive_001'
RUNTIME=ADAPTER/'runtime/positive-001'
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p): return json.loads(p.read_bytes())
def write(p,x): p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def main():
 pins=read(REPORTS/'execution_pins.json')
 for name,h in pins['source_sha256'].items(): assert sha(ADAPTER/name)==h
 for name,x in read(BASE/'implementation_review/source_read.json')['files'].items(): assert sha(BASE/name)==x['sha256']
 native=pins['native_dependency']; assert sha(Path(native['path']))==native['sha256']
 calls=[json.loads(x) for x in (REPORTS/'commands.jsonl').read_bytes().splitlines()]
 names=[x['command'] for x in calls]; counts=dict(collections.Counter(names))
 assert counts=={'auth-init':1,'recipient-init':16,'public-build':1,'verify-public':1,'validate-context':1,'recipient-finalize':16,'issuer-encrypt':33,'host-learn':33,'encode-query':4,'host-infer':4}
 assert names[:20]==['auth-init']+['recipient-init']*16+['public-build','verify-public','validate-context']
 assert names[20:36]==['recipient-finalize']*16
 assert all(x['exit_code']==0 and 'signed_score' not in x['result'] for x in calls)
 report=read(REPORTS/'report.json'); context=read(REPORTS/'context.json'); transcript=read(REPORTS/'public_transcript.json')
 canonical=lambda x:json.dumps(x,sort_keys=True,separators=(',',':'),ensure_ascii=True).encode()
 assert hashlib.sha256(canonical(context)).hexdigest()==report['context_id']==transcript['context_id']
 assert transcript['setup_source_sha256']==pins['source_sha256']['setup.py']
 assert report['ok'] and report['learns']==33 and report['infers']==4 and report['exact_original_expiries']==1 and report['all_match']
 assert not report['scalar_master_computed_in_executed_setup_path'] and not report['projection_key_delivery_computed_in_executed_setup_path']
 same=[]
 for p in sorted(REPORTS.rglob('*')):
  if p.is_file() and (RUNTIME/p.relative_to(REPORTS)).is_file():
   assert sha(p)==sha(RUNTIME/p.relative_to(REPORTS)); same.append(str(p.relative_to(REPORTS)))
 inv=read(REPORTS/'public_ciphertext_inventory.json')['files']
 for x in inv:
  p=RUNTIME/x['path']; assert '.private' not in p.parts and sha(p)==x['sha256'] and p.stat().st_size==x['bytes']
 result={'ok':True,'schema':'public-coin-adapter-evidence-seal-v1','public_command_counts':counts,'public_call_count':len(calls),'saved_exports_matching_runtime':len(same),'public_ciphertext_hashes_checked':len(inv),'context_id':report['context_id'],'source_and_review_read_pins_match':True,'native_pin_matches':True,'registration_before_public_build':True,'full_verification_before_operational_continuation':True,'legacy_dealer_commands_absent':True,'private_files_read_or_hashed':0,'group_arithmetic_or_private_decode_reruns':0,'private_integer_match_status':'attributed to frozen executed report; private answers not opened','report_sha256':sha(REPORTS/'report.json'),'source_sha256':sha(Path(__file__))}
 write(HERE/'reports/adapter_seal.json',result)
 closeout='''# Public-coin adapter evidence closeout\n\n[EXECUTED seal, 2026-09-08] `python3 ../journal/seal_adapter.py` rehashes the\nsaved public exports, source/review pins and ciphertext inventory, and checks\nactual public command counts/order. Retained output is\n`../journal/reports/adapter_seal.json`; `FINAL_MANIFEST.json` pins this closeout\nand every exported public report. No workload, group arithmetic or private\ndecode is rerun; no private file is opened or hashed. Frozen sources and prior\nreview notes remain unchanged.\n\n[EXECUTED saved result; attribution] `reports/positive_001/report.json` records\n33 Learn, four Infer, one expiry, 33 exact queue-byte checks and four matching\nprivate integer comparisons. It records 174.625837167 seconds overall and\n42.710028458 seconds setup. These are the original executed harness timings,\nwhich included private-role processing outside the accepted-public-value\nsecurity transcript. The seal checks report provenance, not the private answers.\n\n[DERIVED source/evidence agreement] The saved commands begin with independent\nregistration (16 recipient announcements), then public-build, verify-public,\nfull validate-context, and 16 recipient-finalize calls. No keygen, initializer\nor recipient-register command appears. Reviewed setup/source bytes match the\nexecution pins; the source computes no scalar master or projection deliveries\non that path. Successful public algebra recomputation is attributed to its saved\ncommand output. Source-level review remains in the unchanged\n`../implementation_review/REVIEW.md`; this closeout supplies its missing seal\nwithout impersonating an independent reviewer's final disposition.\n\n[DERIVED limits] Honest direct tau/U sampling and honest independent recipient\nregistration remain premises. The recipient coalition retains its full fixed\nper-input span, and the known fixture is reconstructible. Shared-account roles\nprovide no OS isolation or operator confidentiality. Classical DDH and Ed25519\nremain separate assumptions; no PQ, malicious setup, selected-only release or\nnew utility claim follows. No metered or network query was used.\n'''
 (ADAPTER/'CLOSEOUT.md').write_text(closeout)
 paths=[ADAPTER/'CLOSEOUT.md',ADAPTER/'SOURCE_PINS.json',ADAPTER/'ENVIRONMENT.json',ADAPTER/'README.md',ADAPTER/'.gitignore']
 paths += [ADAPTER/name for name in pins['source_sha256']]
 paths += [p for p in REPORTS.rglob('*') if p.is_file()]
 paths += [BASE/'implementation_review/REVIEW.md',BASE/'implementation_review/source_read.json',HERE/'reports/adapter_seal.json',Path(__file__)]
 write(ADAPTER/'FINAL_MANIFEST.json',{'schema':'public-coin-adapter-final-evidence-v1','scope':'named public artifacts only; no private material; immutable original execution','files':{str(p.relative_to(BASE)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(set(paths))}})
 print(json.dumps(result,sort_keys=True))
if __name__=='__main__':main()
