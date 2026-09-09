from pathlib import Path
import hashlib, importlib.util, json, re, subprocess, tempfile

out = Path(__file__).resolve().parent
repo = Path('/tmp/minidregg-ir2-pcs-join-20260908')
mods = ['Selvage/Ir2PcsPackedSoundness.lean', 'Selvage/Ir2PcsPackedWitnesses.lean']
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
patchpath = out/'ir2-pcs-join.patch'
patchpath.write_text(patch)

check = json.loads((out/'checks/final-01.json').read_text())
assert check['exit_code'] == 0 and check['source_unchanged']
assert Path(check['log']).read_text() == ''
assert check['source_sha256'] == sha(repo/check['command'][-1])
witness = json.loads((out/'witness/CHECKS.json').read_text())
assert witness['exit_code'] == 0 and witness['output'] == '' and witness['source_stable']
assert witness['source_sha256'] == sha(repo/witness['source'])
for m, rec in witness['preserved_dependencies'].items():
    assert rec['source_sha256'] == sha(repo/('Selvage/'+m+'.lean'))
pcs = json.loads((out.parent/'pcs_batching/CHECKS.json').read_text())
for m, h in pcs['sources'].items():
    assert sha(repo/m) == h == sha(out.parent/'pcs_batching'/m)
assert sha(out.parent/'pcs_batching/pcs-batching.patch') == pcs['patch_sha256']
packed = json.loads((out.parent/'CHECKS.json').read_text())
for m, rec in packed['source_files'].items():
    assert sha(repo/m) == rec['sha256'] == sha(out.parent/'src'/m)

r = subprocess.run(['bash', 'scripts/check-import-boundary.sh'], cwd=repo, text=True, capture_output=True)
assert r.returncode == 0, (r.stdout, r.stderr)
(out/'checks/import-boundary.log').write_text(r.stdout+r.stderr)
with tempfile.TemporaryDirectory(prefix='ir2-pcs-join-check-') as temp:
    rr = subprocess.run(['git', 'apply', str(patchpath)], cwd=temp, text=True, capture_output=True)
    assert rr.returncode == 0, (rr.stdout, rr.stderr)
    assert all(sha(Path(temp)/m) == rec['sha256'] for m, rec in files.items())

result = {
    'claim_status': '[EXECUTED]', 'isolate': str(repo),
    'base_git_commit': '6937394e1dc2c2aaff986c7d4b3a258aca5d16fd',
    'lean_version': '4.30.0', 'patch_sha256': sha(patchpath),
    'module_count': len(mods), 'pin_count': total, 'source_files': files,
    'own_final_check': check,
    'retained_witness_check': {'path': 'witness/CHECKS.json', 'sha256': sha(out/'witness/CHECKS.json'), 'evidence': witness},
    'preserved_packed_sources': {m: rec['sha256'] for m, rec in packed['source_files'].items()},
    'preserved_pcs_sources': pcs['sources'],
    'required_pcs_patch_sha256': pcs['patch_sha256'],
    'direct_predecessor_imports': deps,
    'import_gate': {'command': ['bash', 'scripts/check-import-boundary.sh'], 'exit_code': r.returncode, 'log': 'checks/import-boundary.log'},
    'patch_replay': 'PASS: two additive modules reconstructed at exact source bytes',
    'forbidden_tokens': 'PASS: no sorry, axiom declaration, native_decide in stripped source',
    'challenge_numerator': {'alpha': 690749440, 'fri': 131064, 'sum': 690880504},
    'scope': 'Actual fixed alpha batching plus arbitrary typed canonical packed acceptance, under fresh challenge laws, off-domain points and an explicit shaped extraction-failure residual. No deployed hash/FS price or Rust compiler refinement; no broad rebuild.'}
(out/'CHECKS.json').write_text(json.dumps(result, indent=2)+'\n')
prefix = '../proof_frontier/2026-09-08/ir2_verifier_bridge/packed_extraction/pcs_join'
(out/'integration_entry.json').write_text(json.dumps({
    'name': 'ir2_pcs_packed_join', 'root': prefix,
    'patch': prefix+'/ir2-pcs-join.patch', 'expected_pins': total,
    'source_files': {m: prefix+'/src/'+m for m in mods}}, indent=2)+'\n')
pcs_prefix = '../proof_frontier/2026-09-08/ir2_verifier_bridge/packed_extraction/pcs_batching'
(out/'pcs_dependency_entry.json').write_text(json.dumps({
    'name': 'ir2_pcs_batching', 'root': pcs_prefix,
    'patch': pcs_prefix+'/pcs-batching.patch', 'expected_pins': pcs['guards'],
    'source_files': {m: pcs_prefix+'/'+m for m in pcs['sources']}}, indent=2)+'\n')
(out/'STATUS.md').write_text(
    f'[EXECUTED] FROZEN: two additive modules and {total} exact guards; changed-module checks, preserved dependency bytes and import gate pass. Actual PCS batching and arbitrary typed packed acceptance are joined in `packed_pcs_soundness`; `packed_pcs_false_claim_sound` handles false claims for exact extracted source polynomials. Actual shapes, off-domain points, no common nearby explanation and checkpoint inclusion are jointly inhabited; truthful zero claims provide the opposing witness. No source or FRI words are assumed already extracted. See README.md for retained hash, FS, off-domain and implementation limits.\n')
(out/'NEXT.md').write_text(
    '[OPEN] The mathematical acceptance event now uses the actual PCS reduction and log-constructed packed words. The remaining deployed-security critical path is a justified hash extraction-failure model and Fiat-Shamir/PoW challenge reduction, together with arbitrary native-code correspondence and the application AIR/claim reduction. On-domain opening-point failure is unpriced. No extra radius tuning, round count, witness expansion or proof replay is needed to use this handoff.\n')
print(json.dumps({'patch_sha256': sha(patchpath), 'CHECKS_sha256': sha(out/'CHECKS.json'), 'modules': len(mods), 'pins': total, 'head_sha256': files[mods[0]]['sha256']}, indent=2))
