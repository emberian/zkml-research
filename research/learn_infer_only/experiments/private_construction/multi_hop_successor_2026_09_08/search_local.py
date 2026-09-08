"""Bounded title/front-page search; local mirror PDFs are read only."""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import subprocess,re,json,time
root=Path('/Users/ember/dev/gh/forks/IACR-eprint-mirror/2026')
files=sorted(root.glob('*.pdf'), key=lambda p:int(p.stem))
start=time.monotonic()
def inspect(p):
 r=subprocess.run(['pdftotext','-f','1','-l','2',str(p),'-'],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=20)
 s=' '.join(r.stdout.lower().replace('\u00ad','').split())
 hit=bool(re.search(r'multi[ \-\u2010-\u2015]?hop functional encryption',s))
 return {'path':str(p),'returncode':r.returncode,'match':hit,'snippet':s[:1800] if hit else None,'error':r.stderr[:400] if r.returncode else None}
with ThreadPoolExecutor(max_workers=6)as pool: records=list(pool.map(inspect,files))
result={'instrument':'pdftotext -f 1 -l 2 on every 2026 mirror PDF, whitespace collapse, soft-hyphen removal, then multi + optional space/ASCII-or-Unicode-hyphen + hop functional encryption regex','corpus':str(root),'pdf_count':len(files),'numeric_first':str(files[0]),'numeric_last':str(files[-1]),'matches':[r for r in records if r['match']],'errors':[r for r in records if r['returncode']],'elapsed_seconds':time.monotonic()-start,'scope':'Front two pages of existing 2026 files only; neither other-year files nor papers missing from this local mirror are ruled out.'}
Path(__file__).with_name('sources').joinpath('local_search.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
