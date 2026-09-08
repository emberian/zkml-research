import csv,hashlib,io,json,urllib.request
from pathlib import Path
HERE=Path(__file__).resolve().parent
cfg=json.loads((HERE/'config.json').read_text())
base='https://raw.githubusercontent.com/PolyAI-LDN/task-specific-datasets/master/'
provenance={}
for name in ['banking_data/train.csv','banking_data/test.csv','LICENSE']:
 path=HERE/'data'/Path(name).name
 if not path.exists():path.write_bytes(urllib.request.urlopen(base+name,timeout=60).read())
 provenance[name]={'url':base+name,'sha256':hashlib.sha256(path.read_bytes()).hexdigest(),'bytes':path.stat().st_size}
train=list(csv.DictReader((HERE/'data/train.csv').open()));test=list(csv.DictReader((HERE/'data/test.csv').open()))
assert set(train[0])=={'text','category'}
held=[dict(r,source_split='test',source_row=i) for i,r in enumerate(test) if r['category'] in cfg['classes']]
testtexts={r['text'].strip().casefold() for r in test}
chosen={};excluded=[]
for label in cfg['classes']:
 rows=[dict(r,source_split='train',source_row=i) for i,r in enumerate(train) if r['category']==label]
 excluded.extend(r for r in rows if r['text'].strip().casefold() in testtexts)
 rows=[r for r in rows if r['text'].strip().casefold() not in testtexts]
 rows.sort(key=lambda r:hashlib.sha256(('useful-learner-2026-09-08:'+r['text']).encode()).digest())
 chosen[label]=rows[:16];assert len(chosen[label])==16
schedule=[]
for labels,indices in [(cfg['classes'][:4],range(8)),(cfg['classes'][4:],range(8)),(cfg['classes'],range(8,16))]:
 for j in indices:
  for label in labels:schedule.append(chosen[label][j])
assert len(schedule)==128 and len(held)==320
out={'config_sha256':hashlib.sha256((HERE/'config.json').read_bytes()).hexdigest(),'train':schedule,'test':held,'provenance':provenance,'excluded_train_test_exact_overlaps':excluded,'selected_train_rows':128,'held_out_rows':320}
(HERE/'data/selected.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({'train':128,'test':320,'excluded_overlap':len(excluded),'provenance':provenance}))
