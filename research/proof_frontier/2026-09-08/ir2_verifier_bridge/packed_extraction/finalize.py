from pathlib import Path
import hashlib, importlib.util, json, re, subprocess, tempfile

out = Path(__file__).resolve().parent
repo = Path('/tmp/minidregg-ir2-packed-extraction-20260908')
mods = ['Selvage/'+m+'.lean' for m in [
    'ShapeRootExtraction', 'PackedLeafEncoding', 'Ir2FriPackedIndices',
    'Ir2FriNativeMerklePath', 'Ir2PackedCommitments', 'Ir2PackedExtraction',
    'Ir2PackedSoundness', 'ShapeRootExtractionFresh',
    'ShapeRootExtractionWitnesses', 'Ir2PackedFresh', 'Ir2PackedWitnesses',
    'Ir2PackedFreshWitness']]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
spec = importlib.util.spec_from_file_location('c', '/Users/ember/dev/zkml-research/research/learn_infer_only/experiments/integration/check_all_formal.py')
c = importlib.util.module_from_spec(spec)
spec.loader.exec_module(c)
files, deps, patch, total = {}, {}, '', 0
for m in mods:
    p = repo/m
    s = p.read_text()
    declarations = c.qualified_declarations(c.stripped_lean(s))
    pins = re.findall(r'^#print axioms (\S+)', s, re.M)
    assert sorted(pins) == sorted(n['qualified_name'] for n in declarations), m
    assert not re.search(r'\b(?:sorry|native_decide)\b|^\s*axiom\s', c.stripped_lean(s), re.M), m
    total += len(pins)
    dest = out/'src'/m
    dest.parent.mkdir(parents=True, exist_ok=True)
    dest.write_bytes(p.read_bytes())
    files[m] = {'sha256': sha(dest), 'pins': len(pins), 'lines': len(s.splitlines())}
    patch += f'diff --git a/{m} b/{m}\nnew file mode 100644\n--- /dev/null\n+++ b/{m}\n@@ -0,0 +1,{len(s.splitlines())} @@\n' + ''.join('+'+l+'\n' for l in s.splitlines())
    for imp in re.findall(r'^import (\S+)', s, re.M):
        ip = imp.replace('.', '/')+'.lean'
        if not imp.startswith('Mathlib') and ip not in mods:
            deps[ip] = {'sha256': sha(repo/ip)}
patchpath = out/'ir2-packed-extraction.patch'
patchpath.write_text(patch)

checks = [json.loads(p.read_text()) for p in sorted((out/'checks').glob('final-*.json'))]
assert len(checks) == 9, len(checks)
for rec in checks:
    assert rec['exit_code'] == 0 and rec['source_unchanged']
    assert Path(rec['log']).read_text() == ''
    assert rec['source_sha256'] == sha(repo/rec['command'][-1])
indices = json.loads((out/'indices/CHECKS.json').read_text())
for rec in indices['checks']:
    assert rec['exit_code'] == 0 and rec['output'] == ''
    assert rec['source_sha256'] == sha(repo/rec['source'])
encoding = json.loads((out/'encoding/checks/005-guarded.json').read_text())
assert encoding['exit'] == 0
assert encoding['source_sha256'] == sha(repo/'Selvage/PackedLeafEncoding.lean')
assert (out/'encoding/checks/005-guarded.log').read_text() == ''

r = subprocess.run(['bash', 'scripts/check-import-boundary.sh'], cwd=repo, text=True, capture_output=True)
assert r.returncode == 0, (r.stdout, r.stderr)
(out/'checks/import-boundary.log').write_text(r.stdout+r.stderr)
with tempfile.TemporaryDirectory(prefix='ir2-packed-patch-check-') as temp:
    rr = subprocess.run(['git', 'apply', str(patchpath)], cwd=temp, text=True, capture_output=True)
    assert rr.returncode == 0, (rr.stdout, rr.stderr)
    assert all(sha(Path(temp)/m) == v['sha256'] for m, v in files.items())

result = {
    'claim_status': '[EXECUTED]', 'isolate': str(repo),
    'base_git_commit': '6937394e1dc2c2aaff986c7d4b3a258aca5d16fd',
    'lean_version': '4.30.0', 'patch_sha256': sha(patchpath),
    'module_count': len(mods), 'pin_count': total, 'source_files': files,
    'own_final_checks': checks,
    'retained_child_checks': {
        str(p.relative_to(out)): {'sha256': sha(p)} for p in [
            out/'indices/CHECKS.json', out/'encoding/checks/005-guarded.json']},
    'helper_dependency_note': 'Final06 through final09 recheck the four extraction/fresh witnesses against the final guarded parent dependency bytes; earlier helper metadata is retained as historical execution evidence.',
    'direct_predecessor_imports': deps,
    'import_gate': {'command': ['bash', 'scripts/check-import-boundary.sh'], 'exit_code': r.returncode, 'log': 'checks/import-boundary.log'},
    'patch_replay': 'PASS: additive exact-source reconstruction in empty temporary directory',
    'forbidden_tokens': 'PASS: no sorry, axiom declaration, native_decide in stripped source',
    'scope': 'Arbitrary typed canonical packed openings; same-shape collision/late-target residual; optional ideal typed macro-query bound. No actual Poseidon pricing, PCS false-claim farness, Fiat-Shamir law, or arbitrary Rust-to-Lean refinement is asserted. No broad rebuild.',
    'excluded_active_extension': 'pcs_batching/',
    'native_cross_shape_experiment': {'path': 'hash_shape/MANIFEST.json', 'note': 'Separate already-executed constructor, not part of the Lean patch.'}}
(out/'CHECKS.json').write_text(json.dumps(result, indent=2)+'\n')
prefix = '../proof_frontier/2026-09-08/ir2_verifier_bridge/packed_extraction'
(out/'integration_entry.json').write_text(json.dumps({
    'name': 'ir2_packed_extraction', 'root': prefix,
    'patch': prefix+'/ir2-packed-extraction.patch', 'expected_pins': total,
    'source_files': {m: prefix+'/src/'+m for m in mods}}, indent=2)+'\n')
(out/'STATUS.md').write_text(
    f'[EXECUTED] FROZEN: {len(mods)} additive Lean modules, {total} exact axiom pins; changed-module checks and import gate pass. `Packed.supplied_cover` constructs commitment-time words and derives the actual native event or shaped collision/late-target failure. `Packed.supplied_fresh_38` joins the q38 proximity theorem; `Packed.sound` is the separately conditional ideal macro-query composition. Actual-profile and complete execution premises are inhabited. See README.md for the retained actual hash, PCS and FS limits.\n')
(out/'NEXT.md').write_text(
    '[OPEN] Complete the separate active pcs_batching/ construction, instantiate Packed.Reduction with the actual 5271 source-ordered quotients, and join false claims/common nearby input polynomials to extracted-input farness. The actual Poseidon sponge collision/late-target probability, Fiat-Shamir/PoW challenge game and arbitrary native-code refinement remain distinct obligations. Do not repeat the completed proof replay or native collision constructor. Frozen modules and patch need no further examples or broad build.\n')
print(json.dumps({'patch_sha256': sha(patchpath), 'CHECKS_sha256': sha(out/'CHECKS.json'), 'modules': len(mods), 'pins': total, 'soundness_sha256': files['Selvage/Ir2PackedSoundness.lean']['sha256']}, indent=2))
