"""Read-only preparation recheck; imports no experiment module and starts no process."""
from pathlib import Path
import ast,hashlib,json,stat
HERE=Path(__file__).resolve().parent
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(HERE/'PREPARATION_MANIFEST.json')=='110901f488ca678d4c6cf6c0db6dbdc4344d736ce8c539f0d15210cea9834e7d'
manifest=json.loads((HERE/'PREPARATION_MANIFEST.json').read_text())
for name,item in manifest['files'].items():
 assert sha(HERE/name)==item['sha256'] and (HERE/name).stat().st_size==item['bytes']
pins=json.loads((HERE/'SOURCE_PINS.json').read_text())
for name,item in pins['files'].items():
 assert sha(HERE/name)==sha(Path(item['origin']))==item['sha256']
 assert oct(stat.S_IMODE((HERE/name).stat().st_mode))==item['mode']
execution=json.loads((HERE/'reports/normal_001/execution_pins.json').read_text())
for name,expected in execution['source_files_sha256'].items():assert sha(HERE/name)==expected
for category in ['native_dependency','interpreter']:
 record=execution[category];assert sha(Path(record['path']))==record['sha256']
for name,expected in execution['signature_dependency']['files_sha256'].items():assert sha(Path(name))==expected
python=[]
for name in manifest['files']:
 if name.endswith('.py'):ast.parse((HERE/name).read_text(),filename=name);python.append(name)
assert not (HERE/'runtime').exists()
assert not (HERE/'reports/normal_001/LAUNCH.json').exists()
assert not (HERE/'PRELAUNCH_REVIEW.json').exists()
assert not (HERE/'RUN_AUTHORIZATION.json').exists()
# Preserve both completed primitive and its two independent frozen review inventories.
primitive=HERE.parent/'adapter';completed=json.loads((primitive/'FINAL_MANIFEST.json').read_text())
assert sha(primitive/'FINAL_MANIFEST.json')=='e59b5c1734dd229fd9eaf38084f0efce977f9f49319c7057c067855deeaefff8'
for item in completed['files']:
 path=primitive/item['path'];assert '.private' not in path.parts and sha(path)==item['sha256']
review=HERE.parents[4]/'adversarial_review/public_seed_adapter'
assert sha(review/'manifest.json')=='e3cdb34f400ea9d67574d91e32f5249cdfc4f40039f6ec2a8d5f1e0016283709'
assert sha(review/'execution/manifest.json')=='c5e05ce99c7e88ad048f552d3130bb3403213ce0f1c9849ecb0c45ea8fa44976'
for base in [review,review/'execution']:
 for name,item in json.loads((base/'manifest.json').read_text())['files'].items():assert sha(base/name)==item['sha256']
print(json.dumps({'ok':True,'source_freeze_files':len(manifest['files']),'unchanged_dependency_copies':len(pins['files']),'runtime_source_pins':len(execution['source_files_sha256']),'signature_files':len(execution['signature_dependency']['files_sha256']),'Python_ASTs':len(python),'primitive_files_preserved':len(completed['files']),'completed_prelaunch_and_execution_reviews_preserved':True,'runtime_exists':False,'accepted_gate_exists':False,'future_launch_authorization_exists':False,'processes_started':0,'cryptographic_operations':0,'private_file_reads':0,'scope':'Preparation integrity only; final launcher/checker source review and future execution authorization remain pending'},indent=2))
