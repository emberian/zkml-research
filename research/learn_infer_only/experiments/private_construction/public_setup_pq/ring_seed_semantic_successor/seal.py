#!/usr/bin/env python3
"""Seal this public package; hash-only, with no runtime/private-artifact access."""
import hashlib
import json
import os
from pathlib import Path

HERE=Path(__file__).resolve().parent
REPO=HERE.parents[5]
EXPECTED={
    HERE/'SOURCE_PINS.json':'6dc57e64871dce8972c81c0a9288aaabd57f2dc0483748f1b592282a7f40ab45',
    HERE/'THEOREM_APPLICATION.md':'d2761b8d1f075eeb8fc35aabc594a6e1e4918b84fcba6e6932fa0daa8032099f',
    HERE/'expansion/MANIFEST.json':'968a140d3e908d1d0ea2a8a42b13efc93e006c55308f9058ee22f66517561f79',
    HERE.parent/'ring_seed_qrom_successor/MANIFEST.json':'1e4415069a3afbc45fd27345e3487e36b4c8a8f3378f4b9c7ebbf1054265147a',
    HERE.parent/'ring_seed_qrom_successor/THEOREM.md':'9c038779e494bcbada7875940fba276c3256af60d7dda4b5f94bf565c5d7a73d',
    REPO/'research/learn_infer_only/experiments/end_to_end/restricted_query_learner_2026_09_08/SOURCE_PINS.json':'2fb22bf8b14807a1f66549a27b9be97a99b18c4e742c70ffa7d4abb82adf8426',
    REPO/'research/vfhe_2026_09_08/proved_journal/seeded_ring_successor/REPORT.md':'a2f9ce71d1cf11e2d756a8d98e57902726e9d1560671b057ea5fd451a9744118',
}

def sha(path):
    h=hashlib.sha256()
    with path.open('rb') as f:
        for data in iter(lambda:f.read(1<<20),b''):h.update(data)
    return h.hexdigest()

def main():
    for path,expected in EXPECTED.items():assert sha(path)==expected,str(path)
    executable=json.loads((HERE/'SOURCE_PINS.json').read_text())['owned']
    assert len(executable)==15
    for name,expected in executable.items():assert sha(HERE/name)==expected,name
    run=json.loads((HERE/'RUN.json').read_text())
    external=dict(EXPECTED)
    public_inputs={**run['shared_public_outputs'],**run['actor_metrics']['actor_receipt_pins']}
    for name,entry in public_inputs.items():
        path=Path(name)
        assert 'results/seeded001/' in name and '/runtime/' not in name,name
        assert sha(path)==entry['sha256'],name
        external[path]=entry['sha256']
    artifacts={}
    for directory,dirs,files in os.walk(HERE):
        dirs[:]=sorted(d for d in dirs if d not in {'.runtime','runtime','private','__pycache__','.venv','.git'})
        for name in sorted(files):
            path=Path(directory)/name
            if path==HERE/'MANIFEST.json' or name.endswith('.pyc'):continue
            artifacts[str(path.relative_to(HERE))]={'sha256':sha(path),'bytes':path.stat().st_size}
    manifest={
        'schema':'ring-seed-semantic-successor-public-seal-v1',
        'status':'COMPLETE',
        'scope':'384-bit semantic transport plus one shared service run; public hashes only; no additional cryptographic execution',
        'artifacts':artifacts,
        'public_inputs':{str(p):v for p,v in sorted(external.items()) if not p.is_relative_to(HERE)},
        'frozen_executable_manifest_sha256':EXPECTED[HERE/'SOURCE_PINS.json'],
        'frozen_theorem_application_sha256':EXPECTED[HERE/'THEOREM_APPLICATION.md'],
        'checked_executable_files':15,
        'checked_shared_public_files':len(public_inputs),
        'shared_setup_runs':1,'additional_setups':0,'private_payload_reads':0,
        'search_counts':{'web':0,'Scry_SQL':0,'PDF_downloads':0},
    }
    (HERE/'MANIFEST.json').write_text(json.dumps(manifest,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'COMPLETE','artifacts':len(artifacts),'public_inputs':len(manifest['public_inputs']),
                      'manifest_sha256':sha(HERE/'MANIFEST.json'),'report_sha256':sha(HERE/'REPORT.md'),
                      'run_sha256':sha(HERE/'RUN.json'),'theorem_application_sha256':sha(HERE/'THEOREM_APPLICATION.md')}))

if __name__=='__main__':main()
