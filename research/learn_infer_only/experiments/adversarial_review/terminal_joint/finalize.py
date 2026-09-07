#!/usr/bin/env python3
"""Freeze the independent terminal-joint review's hashes and scope."""
import hashlib
import json
from pathlib import Path
import re

HERE=Path(__file__).resolve().parent


def main():
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    results=json.loads((HERE/'results.json').read_text())
    assert results['all_inputs_unchanged']
    for path,digest in results['input_hashes_after'].items():
        assert sha(Path(path))==digest,path
    assert (HERE/'stderr.txt').read_text()==''
    report=HERE/'REPORT.md'
    prose=re.sub(r'```.*?```','',report.read_text(),flags=re.S)
    prose=re.sub(r'`[^`]*`','',prose)
    links=[x for x in re.findall(r'\]\(([^)]+)\)',prose) if not x.startswith('https://')]
    assert all((HERE/x).is_file() for x in links),links
    files=['REPORT.md','review.py','results.json','stdout.txt','stderr.txt','.gitignore','finalize.py']
    result={'label':'EXECUTED independent review freeze',
            'author':'/root/private_ingress','reviewer':'/root/pq_composition',
            'verdict':'Accepted source-conditioned classical honest-setup-averaged terminal output lemma; no blocking error found.',
            'preserved_boundaries':['Current compatibility bridge and numerical threshold remain open.',
                'Same-parent descent is enforced inside F and the experiment; public R2 alone does not identify current C.',
                'No arbitrary post-setup terminal-secret advice is inferred from source definitions.',
                'Source Theorem6.1/internal Lemma6.8 remains a source-conditioned ingredient.'],
            'reviewed_note_sha256':'1c698c8361cd4d6e5bfefc96ee34d1bcc4d090ec59f09f6efaad378d5195717c',
            'files':[{ 'path':str(HERE/name),'sha256':sha(HERE/name)} for name in files],
            'input_hashes_rechecked':len(results['input_hashes_after']),
            'local_report_links_checked':len(links),
            'command':['python3',str(Path(__file__))],
            'queries':results['queries'],'new_PDF_extracts':0,'PDF_downloads':0,
            'cryptographic_extraction_recovery_routing_or_service_runtimes':0,
            'author_or_companion_or_shared_writes':0,'commits':0}
    (HERE/'review_manifest.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
