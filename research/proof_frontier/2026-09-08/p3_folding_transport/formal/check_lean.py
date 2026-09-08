from pathlib import Path
import hashlib, json, os, subprocess, sys, time
HERE = Path(__file__).resolve().parent
WORK = Path('/tmp/minidregg-p3-folding-transport-20260908')
relative = sys.argv[1] if len(sys.argv) > 1 else 'Theory/BitReverseFriTransport.lean'
SOURCE = WORK / relative
logs = HERE / 'logs'
prefix = 'lean' if relative.startswith('Theory/') else 'selvage'
number = 1 + len(list(logs.glob(f'{prefix}_*.json')))
stem = f'{prefix}_{number:03d}'
data = SOURCE.read_bytes()
(logs / f'{stem}.lean').write_bytes(data)
output = WORK / '.lake/build/lib/lean' / str(Path(relative).with_suffix('.olean'))
output.parent.mkdir(parents=True,exist_ok=True)
cmd = ['lake', 'env', 'lean', '-o', str(output), relative]
env = os.environ.copy()
env['LEAN_PATH'] = '/Users/ember/dev/minidregg/.lake/build/lib/lean'
start = time.monotonic()
p = subprocess.run(cmd, cwd=WORK, env=env, text=True, capture_output=True, timeout=120)
r = dict(command=cmd, cwd=str(WORK), exit_code=p.returncode, seconds=time.monotonic()-start,
         source_sha256=hashlib.sha256(data).hexdigest(),
         source_sha256_after=hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
         stdout=p.stdout, stderr=p.stderr)
(logs / f'{stem}.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r,indent=2))
raise SystemExit(p.returncode)
