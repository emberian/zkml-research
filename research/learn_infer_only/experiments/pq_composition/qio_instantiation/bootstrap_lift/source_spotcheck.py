#!/usr/bin/env python3
"""Pin read-only primary spot checks of the complementary base audit."""
import hashlib
import json
from pathlib import Path

HERE=Path(__file__).resolve().parent
BASE=HERE.parent.parent/'base_fe_audit'
MIRROR=Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror')


def main():
    sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
    rows=[]
    for paper,pdf_pages,printed_pages,tokens in [
        ('2012/733',[23,24],[23,24],['MPK = (fmpk1', 'nλ']),
        ('2013/337',[16,17],[15,16],['Setup(1λ', 'mpk :=']),
    ]:
        pdf=MIRROR/f'{paper}.pdf'
        extract=BASE/'texts'/f'{paper.replace("/","_")}.txt'
        pages=extract.read_text().split('\f')
        selected='\n'.join(pages[p-1] for p in pdf_pages)
        assert all(t in selected for t in tokens),(paper,tokens)
        rows.append({'paper':paper,'pdf_path':str(pdf),'pdf_sha256':sha(pdf),
                     'read_only_extract_path':str(extract),'extract_sha256':sha(extract),
                     'PDF_pages_read':pdf_pages,'printed_pages_read':printed_pages,
                     'locator_tokens_checked':tokens})
    result={'label':'EXECUTED','scope':__doc__,'sources':rows,
            'extraction_provenance':str(BASE/'access.json'),
            'extraction_provenance_sha256':sha(BASE/'access.json'),
            'additional_SQL_schema_web_queries':0,'PDF_downloads':0,
            'script_sha256':sha(Path(__file__))}
    (HERE/'source_spotcheck.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result,indent=2))


if __name__=='__main__':
    main()
