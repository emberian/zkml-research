#!/usr/bin/env python3
"""Pin the finite local source/proof audit without any network operation."""
import hashlib
import json
from pathlib import Path
import re
import subprocess

HERE = Path(__file__).resolve().parent
MIRROR = Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')
SOURCES = {
    '2016/006': ['Theorem 6.', 'Theorem 7.', 'Definition 4', 'Definition 5'],
    '2015/720': ['Definition 20', 'Definition 21', 'Theorem 11.', 'Theorem 12.',
                 'Theorem 13.', 'Theorem 15.'],
    '2015/173': ['From Compact (1)-Secure FE to Compact'],
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def command(args):
    p = subprocess.run(args, text=True, capture_output=True)
    assert p.returncode == 0, (args,p.stderr)
    return {'command': args, 'returncode': p.returncode, 'stdout': p.stdout, 'stderr': p.stderr}


def main():
    (HERE/'extracts').mkdir(exist_ok=True)
    sources=[]
    for paper, tokens in SOURCES.items():
        pdf=MIRROR/f'{paper}.pdf'
        extract=HERE/'extracts'/f'{paper.replace("/","-")}.txt'
        commands=[command(['pdftotext','-layout',str(pdf),str(extract)]),
                  command(['pdfinfo',str(pdf)])]
        pages=extract.read_text().split('\f')
        locations={token:[i+1 for i,page in enumerate(pages) if token in page] for token in tokens}
        assert all(locations.values()),(paper,locations)
        sources.append({'paper':paper,'pdf_path':str(pdf),'pdf_sha256':sha(pdf),
                        'extract_sha256':sha(extract),'locator_pdf_pages':locations,'commands':commands})
    note=HERE/'BOOTSTRAP_LIFT.md'
    prose=re.sub(r'```.*?```','',note.read_text(),flags=re.S)
    prose=re.sub(r'`[^`]*`','',prose)
    links=[x for x in re.findall(r'\]\(([^)]+)\)',prose) if not x.startswith('https://')]
    assert all((HERE/x).is_file() for x in links),links
    controls=json.loads((HERE/'controls.json').read_text())
    result={'label':'EXECUTED','scope':__doc__,'note_sha256':sha(note),
            'script_sha256':sha(Path(__file__)),'controls_sha256':sha(HERE/'controls.json'),
            'sources':sources,'local_note_links_checked':len(links),
            'frozen_predecessor_sha256':sha(HERE.parent/'INSTANTIATION.md'),
            'accepted_interface_sha256':sha(HERE.parent.parent/'qio_interface'/'QIO_INTERFACE.md'),
            'control_counts':controls['counts'],
            'queries_this_tranche':{'SQL':0,'schema':0,'web_search':0,'web_open':0,'Kagi':0},
            'network_PDF_downloads':0}
    (HERE/'audit.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
