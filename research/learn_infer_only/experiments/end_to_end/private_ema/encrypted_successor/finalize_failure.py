"""Seal stopped-run evidence without any crypto or private-file access."""
import csv
from common import ROOT,REPORTS,load,save,meta,sha,lines,verify_freeze

verify_freeze();audit=load(REPORTS/'public_failure_audit.json')
assert audit['passed_public_evidence_audit'] and not audit['crypto_workload_completed']
operations=lines(REPORTS/'public_operations.jsonl')
with (ROOT/'costs.csv').open('w',newline='') as f:
    writer=csv.writer(f)
    writer.writerow(['operation','binary','subprocess_wall_seconds','evaluation_seconds','and_calls','xor_calls','not_calls','mux_calls','trivial_encrypt_calls'])
    for row in operations:
        reported=row['reported'];g=reported.get('gate_api_calls',{})
        writer.writerow([row['name'],row['binary'],row['subprocess_wall_seconds'],reported.get('evaluate_ns',0)/1e9,
                         *[g.get(k,0) for k in ['and','xor','not','mux','trivial_encrypt']]])
source_files=[p for p in ROOT.iterdir() if p.is_file() and p.suffix in ['.py','.md']]
source_files+=[ROOT/'freeze.json']+[p for d in ['sources','analysis'] for p in (ROOT/d).iterdir() if p.is_file()]
save(ROOT/'source_checkpoint.json',{'scope':'final source checkpoint after first replay failure; supersedes early running source/status snapshot',
    'files':{str(p.relative_to(ROOT)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(source_files)}})
files=[p for p in ROOT.rglob('*') if p.is_file() and not p.is_relative_to(ROOT/'runtime') and '__pycache__' not in p.parts
       and p.name not in ['manifest.json','finalize_failure.stdout']]
save(ROOT/'manifest.json',{'scope':'stopped first TFHE workload; public-only failure audit; no private drain',
    'files':{str(p.relative_to(ROOT)):{'sha256':sha(p),'bytes':p.stat().st_size} for p in sorted(files)},
    'retained_files':len(files),'public_failure_audit_sha256':sha(REPORTS/'public_failure_audit.json'),
    'freeze_sha256':sha(ROOT/'freeze.json'),'cryptographic_workload_completed':False})
print({'files':len(files),'manifest_sha256':sha(ROOT/'manifest.json'),'source_checkpoint_sha256':sha(ROOT/'source_checkpoint.json'),
       'public_failure_audit_sha256':sha(REPORTS/'public_failure_audit.json')})
