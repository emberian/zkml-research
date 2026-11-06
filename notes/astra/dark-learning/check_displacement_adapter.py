"""Check the candidate with exact current source fragments, never stale Selvage oleans.
Not a full-module integration build. No stubs, axioms, or sorry are introduced.
"""
from pathlib import Path
import subprocess, os, hashlib, json
root = Path('/Users/ember/dev/minidregg')
base = Path(__file__).resolve().parent
snippets = []
def cut(path, start, end, include_end=False):
    text = (root / path).read_text()
    a = text.index(start); b = text.index(end, a)
    if include_end:
        b += len(end)
    snippet = text[a:b]
    snippets.append({'path': path, 'first_line': text[:a].count('\n') + 1,
                     'sha256': hashlib.sha256(snippet.encode()).hexdigest()})
    return snippet
h = 'import Mathlib\nnamespace Minidregg.Selvage\n'
h += cut('Selvage/Rbr.lean', 'noncomputable def uniformProb', '/-! ## Transcripts')
h += cut('Selvage/Depth.lean', 'section UniformProb', '/-- The finite union bound over `Fin m`')
h += '\nend UniformProb\nend Minidregg.Selvage\n'
h += cut('Selvage/AuditSampling.lean', 'namespace Minidregg.Selvage', '/-! ## 5. Cost:')
h += cut('Selvage/AuditSampling.lean', 'namespace AuditWitness', 'end AuditWitness', True)
h += '\nend Minidregg.Selvage\n'
a = (base / 'source/Selvage/AuditDisplacement.lean').read_text()
h += a[a.index('namespace Minidregg.Selvage.AuditDisplacement'):]
p = base / 'DisplacementSourceCheck.lean'; p.write_text(h)
for generated in [base / 'source/Selvage/AuditDisplacement.lean', p]:
    snippets.append({'generated_path': str(generated),
                     'sha256': hashlib.sha256(generated.read_bytes()).hexdigest()})
(base / 'adapter-source-slices.json').write_text(json.dumps(snippets, indent=2) + '\n')
env = dict(os.environ, LEAN_PATH=':'.join(str(p) for p in (root / '.lake/packages').glob('*/.lake/build/lib/lean')))
cmd = ['/Users/ember/.elan/toolchains/leanprover--lean4---v4.35.0/bin/lean', str(p)]
proc = subprocess.Popen(cmd, env=env, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
(base / 'displacement-adapter.pid').write_text(str(proc.pid) + '\n')
output, _ = proc.communicate()
(base / 'displacement-adapter-check.log').write_text('COMMAND ' + repr(cmd) + '\n' + output + '\nEXIT ' + str(proc.returncode) + '\n')
print(output); print('exit', proc.returncode)
raise SystemExit(proc.returncode)
