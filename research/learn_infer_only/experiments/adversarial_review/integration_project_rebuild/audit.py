#!/usr/bin/env python3
"""Public source/helper audit only. Never invoke Lean or the integration runner."""
import ast
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
RESIDENT = HERE.parents[2]
INTEGRATION = RESIDENT / 'experiments/integration'
CHECKER = INTEGRATION / 'check_all_formal.py'
COMPANION = Path('/Users/ember/dev/minidregg')
MANIFEST = INTEGRATION / 'modules_overnight_sampled.json'
ENVIRONMENT = RESIDENT / 'experiments/results/environment.json'
PINS = {}
COMMANDS = []


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def read(path):
    raw = path.read_bytes()
    PINS[str(path)] = digest(raw)
    return raw


def cmd(argv, cwd):
    p = subprocess.run(argv, cwd=cwd, capture_output=True, text=True)
    COMMANDS.append(dict(argv=argv, cwd=str(cwd), exit=p.returncode,
                         stdout=p.stdout, stderr=p.stderr))
    if p.returncode:
        raise RuntimeError(COMMANDS[-1])
    return p.stdout


def mask(source):
    """Independent small scanner for comments/strings, retaining newlines."""
    i, depth, string, comment = 0, 0, False, False
    out = []
    while i < len(source):
        pair = source[i:i+2]
        ch = source[i]
        if comment:
            if ch == '\n':
                comment = False
            out.append('\n' if ch == '\n' else ' ')
            i += 1
        elif depth:
            if pair == '/-':
                depth += 1
                out.extend('  ')
                i += 2
            elif pair == '-/':
                depth -= 1
                out.extend('  ')
                i += 2
            else:
                out.append('\n' if ch == '\n' else ' ')
                i += 1
        elif string:
            if ch == '\\':
                out.extend('\n' if c == '\n' else ' ' for c in source[i:i+2])
                i += 2
            else:
                string = ch != '"'
                out.append('\n' if ch == '\n' else ' ')
                i += 1
        elif pair == '/-':
            depth = 1
            out.extend('  ')
            i += 2
        elif pair == '--':
            comment = True
            out.extend('  ')
            i += 2
        elif ch == '"':
            string = True
            out.append(' ')
            i += 1
        else:
            out.append(ch)
            i += 1
    assert not depth and not string
    return ''.join(out)


def header_imports(source):
    """Audit actual current simple headers; stop at the first body token."""
    clean = mask(source)
    tokens = re.findall(r'\S+', clean)
    found = []
    i = 0
    if tokens and tokens[0] == 'module':
        i += 1
    if i < len(tokens) and tokens[i] == 'prelude':
        i += 1
    while i < len(tokens):
        start = i
        for prefix in ('public', 'meta'):
            if i < len(tokens) and tokens[i] == prefix:
                i += 1
        if i >= len(tokens) or tokens[i] != 'import':
            i = start
            break
        i += 1
        if tokens[i] == 'all':
            i += 1
        name = tokens[i]
        assert re.fullmatch(r'[A-Za-z_][\w.]*', name), name
        found.append(name)
        i += 1
    return found


def negative(label, f):
    try:
        f()
    except ValueError as exc:
        return dict(label=label, refused=True, reason=str(exc))
    return dict(label=label, refused=False)


def main():
    current = read(CHECKER).decode()
    lean_parser_root=Path('/Users/ember/.elan/toolchains/leanprover--lean4---v4.30.0/src/lean/Lean/Parser')
    read(lean_parser_root/'Module.lean')
    read(lean_parser_root/'Module/Syntax.lean')
    spec = importlib.util.spec_from_file_location('reviewed_checker', CHECKER)
    checker = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(checker)
    tree = ast.parse(current)
    result = dict(scope='Source and bounded helper controls only; no Lean invocation or shared-output writes.',
                  checker_sha256=digest(current.encode()))
    manifest = json.loads(read(MANIFEST))
    before_head = cmd(['git', 'rev-parse', 'HEAD'], COMPANION)
    before_status = cmd(['git', 'status', '--short'], COMPANION)
    relative = sorted(set(cmd(['git', 'ls-files', '--cached', '--others', '--exclude-standard', '*.lean'], COMPANION).splitlines()))
    baseline = {p[:-5].replace('/', '.'): read(COMPANION/p).decode() for p in relative}
    baseline_hashes = {p: PINS[str(COMPANION/p)] for p in relative}
    modules, additions, lane_counts = {}, {u: [] for u in checker.UMBRELLAS}, {}
    source_bytes_roundtrip = []
    for lane in manifest['lanes']:
        patch = read(RESIDENT/lane['patch']).decode()
        for u, lines in checker.umbrella_imports(patch).items():
            additions[u].extend(lines)
        count = 0
        for dest in re.findall(r'^\+\+\+ b/(.+\.lean)$', patch, re.M):
            if dest in [u+'.lean' for u in checker.UMBRELLAS]:
                continue
            name = dest[:-5].replace('/', '.')
            source = RESIDENT/lane.get('source_files', {}).get(dest, lane['root']+'/'+dest)
            raw = read(source)
            text = raw.decode()
            assert source.read_text().encode() == raw, f'Universal-newline conversion: {source}'
            source_bytes_roundtrip.append(name)
            section = re.split(r'^\+\+\+ b/'+re.escape(dest)+r'\n', patch, maxsplit=1, flags=re.M)[1]
            section = re.split(r'^(?:diff --git |--- )', section, maxsplit=1, flags=re.M)[0]
            added = ''.join(line[1:] for line in section.splitlines(True) if line.startswith('+'))
            assert added.encode() == raw, source
            census = checker.census(text, name)
            count += census['pin_count']
            assert name not in modules and name not in baseline
            modules[name] = dict(text=text, dest=dest, source=str(source), census=census)
        assert count == lane['expected_pins'], lane['name']
        lane_counts[lane['name']] = count
    assert sum(lane_counts.values()) == manifest['expected_theorem_pins'] == 952
    staged = {}
    for u in checker.UMBRELLAS:
        existing = set(checker.imports(baseline[u]))
        appended = []
        for line in additions[u]:
            names = checker.imports(line)
            assert len(names) == 1
            if names[0] not in existing:
                appended.append(line if line.endswith('\n') else line+'\n')
                existing.add(names[0])
        staged[u] = baseline[u].rstrip('\n')+'\n\n'+''.join(appended)
    texts = {**baseline, **{n:m['text'] for n,m in modules.items()}, **staged}
    graphs = {n:checker.imports(t) for n,t in texts.items()}
    discrepancies = {n:dict(checker=graphs[n], independent=header_imports(t)) for n,t in texts.items() if graphs[n] != header_imports(t)}
    assert not discrepancies, discrepancies
    closure, pending = set(), list(checker.UMBRELLAS)
    while pending:
        name = pending.pop()
        if name in closure or name not in graphs:
            continue
        closure.add(name)
        pending.extend(graphs[name])
    unrooted_selected = sorted(set(modules)-closure)
    order = checker.topo({n:graphs[n] for n in sorted(closure)})
    index = {n:i for i,n in enumerate(order)}
    assert all(index[d]<index[n] for n in closure for d in graphs[n] if d in closure)
    external = sorted({d for n in closure for d in graphs[n] if d not in closure})
    env = json.loads(read(ENVIRONMENT))
    original_paths = next(c['stdout'].strip().split(':') for c in env['checks'] if c['command']==['lake','env','printenv','LEAN_PATH'])
    artifacts = COMPANION/'.lake/build/lib/lean'
    kept = [p for p in original_paths if Path(p).resolve()!=artifacts.resolve()]
    assert all(Path(p).is_absolute() for p in kept)
    assert all(Path(p).resolve()!=artifacts.resolve() for p in kept)
    assert all('/.lake/packages/' in p or '/.elan/toolchains/' in p for p in kept)
    resolution = {}
    for name in external:
        candidates = [Path(p)/(name.replace('.','/')+'.olean') for p in kept]
        found = next((p for p in candidates if p.is_file()), None)
        assert found is not None, name
        assert not found.resolve().is_relative_to(artifacts.resolve()), found
        resolution[name] = str(found.resolve())
    project_artifact_collisions = {n:[str(Path(p)/(n.replace('.','/')+'.olean')) for p in kept if (Path(p)/(n.replace('.','/')+'.olean')).is_file()] for n in graphs}
    project_artifact_collisions = {n:paths for n,paths in project_artifact_collisions.items() if paths}
    assert not project_artifact_collisions, project_artifact_collisions
    result['closure'] = dict(current_project_files=len(baseline), selected_new_modules=len(modules), selected_pins=sum(lane_counts.values()),
        total_available_project_modules=len(graphs), rooted_compile_count=len(closure), existing_rooted_count=len(closure-set(modules)),
        excluded_existing=sorted(set(baseline)-closure), complete_selected_rooting=not unrooted_selected,
        unrooted_selected=unrooted_selected, independent_header_agreement=len(graphs),
        topological_order=order, external_direct_import_count=len(external), external_resolution=resolution)
    result['cache_paths'] = dict(original=original_paths, retained=kept, removed=[p for p in original_paths if p not in kept], external_project_name_collisions=project_artifact_collisions)
    result['source_symlinks'] = [p for p in relative if (COMPANION/p).is_symlink()]
    assert not result['source_symlinks']
    result['isolation_path_types'] = {str(p):dict(is_symlink=p.is_symlink(),resolved=str(p.resolve()))
        for p in (INTEGRATION,INTEGRATION/'build',COMPANION,artifacts)}
    result['lean_environment'] = {name:__import__('os').environ.get(name) for name in ('LEAN_PATH','LEAN_SYSROOT','LEAN_SRC_PATH','ELAN_TOOLCHAIN')}
    result['side_effect_token_scan'] = {n:[dict(line=i+1,text=line.strip()) for i,line in enumerate(mask(texts[n]).splitlines())
        if re.search(r'#eval\b|#run\b|\brun_elab\b|\brun_cmd\b|\binitialize\b|IO\.FS\.|writeFile|writeBinFile|createDir',line)] for n in sorted(closure)}
    result['side_effect_token_scan'] = {n:rows for n,rows in result['side_effect_token_scan'].items() if rows}
    result['literal_write_targets'] = {n:re.findall(r'"((?:prover/)[^"\n]*)"',texts[n]) for n in result['side_effect_token_scan']}
    private_name='Selvage.FullUDTeeth'
    private_text=modules[private_name]['text']
    private_census=checker.census(private_text,private_name)
    result['private_census'] = dict(theorems=private_census['theorem_count'], private=sum(d['private'] for d in private_census['qualified_declarations']),
        controls=[negative('wrong module',lambda:checker.census(private_text,'Selvage.WrongModule')),
          negative('public declaration/private printed name',lambda:checker.census(private_text.replace('private theorem affine_mem','theorem affine_mem'),private_name)),
          negative('private declaration/public printed name',lambda:checker.census(private_text.replace('_private.Selvage.FullUDTeeth.0.Minidregg.Selvage.FullUDTeeth.affine_mem','Minidregg.Selvage.FullUDTeeth.affine_mem'),private_name)),
          negative('missing private guard',lambda:checker.census(private_text.replace('#print axioms affine_mem','#check affine_mem'),private_name)),
          negative('forbidden sorry',lambda:checker.census(private_text+'\nexample : True := by sorry\n',private_name)),
          negative('unauthorized axiom',lambda:checker.census(private_text.replace('Classical.choice','Custom.axiom'),private_name))])
    assert all(c['refused'] for c in result['private_census']['controls'])
    result['import_helper_controls'] = dict(multi_same_line=checker.imports('import Theory.A Theory.B -- trailing\n'),
        nested_comments=checker.imports('/- import X /- import Y -/ -/\nimport Theory.A /- middle -/ Theory.B\n'),
        unsupported_symbol=negative('quoted module name',lambda:checker.imports('import «A-B»\n')),
        public_import=negative('public import',lambda:checker.imports('module\npublic import Theory.A\n')),
        import_newline=negative('newline after import',lambda:checker.imports('import\n  Theory.A\n')))
    assert result['import_helper_controls']['public_import']['refused']
    assert result['import_helper_controls']['import_newline']['refused']
    run_dir=HERE/'scratch'
    run_dir.mkdir(exist_ok=True)
    patch_root=run_dir/'exact_patch'
    if patch_root.exists():
        shutil.rmtree(patch_root)
    patch_root.mkdir()
    cmd(['git','init','-q'],patch_root)
    combined=''
    expected={}
    for u in checker.UMBRELLAS:
        (patch_root/(u+'.lean')).write_bytes(baseline[u].encode())
        combined+=checker.unified_patch(baseline[u],staged[u],'a/'+u+'.lean','b/'+u+'.lean')
        expected[u+'.lean']=staged[u].encode()
    for n,m in modules.items():
        combined+=checker.unified_patch('',m['text'],'/dev/null','b/'+m['dest'])
        expected[m['dest']]=m['text'].encode()
    supports=[]
    for item in manifest['support_files']:
        raw=read(RESIDENT/item['source'])
        assert digest(raw)==item['sha256']
        assert (RESIDENT/item['source']).read_text().encode()==raw
        combined+=checker.unified_patch('',raw.decode(),'/dev/null','b/'+item['destination'])
        expected[item['destination']]=raw
        supports.append(dict(destination=item['destination'],sha256=digest(raw),bytes=len(raw),final_newline=raw.endswith(b'\n')))
    patch=run_dir/'combined-helper.patch'
    patch.write_text(combined)
    cmd(['git','apply','--check',str(patch)],patch_root)
    cmd(['git','apply',str(patch)],patch_root)
    assert all((patch_root/p).read_bytes()==raw for p,raw in expected.items())
    result['exact_patch'] = dict(files=len(expected), selected_source_roundtrips=len(source_bytes_roundtrip),
        patch_sha256=digest(combined.encode()), supports=supports, every_applied_byte_equal=True)
    eof_cases=[]
    for i,(before,after) in enumerate([('before','after'),('before\n','after'),('before','after\n'),('','text\n'),('','text'),('λ\nold','λ\nnew')]):
        p=run_dir/f'eof_{i}'
        p.mkdir(exist_ok=True)
        cmd(['git','init','-q'],p)
        (p/'sample').write_text(before)
        raw_patch=checker.unified_patch(before,after,'a/sample','b/sample')
        pp=run_dir/f'eof_{i}.patch'
        pp.write_text(raw_patch)
        cmd(['git','apply','--check',str(pp)],p)
        cmd(['git','apply',str(pp)],p)
        assert (p/'sample').read_bytes()==after.encode()
        eof_cases.append(dict(case=i,before_final_newline=before.endswith('\n'),after_final_newline=after.endswith('\n'),exact_bytes=True))
    result['eof_controls']=eof_cases
    report17=json.loads(read(INTEGRATION/'results/run_017/report.json'))
    applied17=json.loads(read(INTEGRATION/'results/run_017/applied_source_hashes.json'))
    baseline17=json.loads(read(INTEGRATION/'results/run_017/companion_source_hashes_before.json'))
    common_selected={n:applied17[m['dest']]==digest(m['text'].encode()) for n,m in modules.items() if m['dest'] in applied17}
    assert len(common_selected)==70 and all(common_selected.values())
    result['run017'] = dict(checker_hash=next(v for k,v in report17['input_hashes_before'].items() if k.endswith('/check_all_formal.py')),
         module_count=report17['module_count'],pins=report17['theorem_pins'],project_sources=len(baseline17)-1,
         common_selected_source_count=len(common_selected),common_selected_sources_byte_equal=all(common_selected.values()),
         changed_baseline_since_run017=[p for p in relative if baseline17.get(str(COMPANION/p))!=baseline_hashes[p]])
    old_ast_path=INTEGRATION/'results/run_017/check_all_formal.py'
    if old_ast_path.exists():
        old=read(old_ast_path).decode()
        assert digest(old.encode())==result['run017']['checker_hash']
        recovery=INTEGRATION/'results/run_017/harness_archive_recovery.json'
        result['run017']['archive_recovery']=json.loads(read(recovery))
        result['run017']['archived_checker']=str(old_ast_path)
        before_functions={n.name:ast.dump(n,include_attributes=False) for n in ast.parse(old).body if isinstance(n,(ast.FunctionDef,ast.ClassDef))}
        after_functions={n.name:ast.dump(n,include_attributes=False) for n in tree.body if isinstance(n,(ast.FunctionDef,ast.ClassDef))}
        result['run017']['changed_ast_members']=[n for n in after_functions if before_functions.get(n)!=after_functions[n]]
        (HERE/'checker_vs_run017.diff').write_text(''.join(difflib.unified_diff(old.splitlines(True),current.splitlines(True),fromfile='run017/check_all_formal.py',tofile='current/check_all_formal.py')))
        census_same=all(before_functions[name]==after_functions[name] for name in ('census','qualified_declarations','stripped_lean','unified_patch'))
        assert census_same
        result['run017']['census_and_eof_helper_ast_unchanged']=census_same
    else:
        result['run017']['archived_checker']=None
    result['companion_unchanged']=dict(head=before_head==cmd(['git','rev-parse','HEAD'],COMPANION),status=before_status==cmd(['git','status','--short'],COMPANION),source_hashes=all(digest((COMPANION/p).read_bytes())==h for p,h in baseline_hashes.items()))
    assert all(result['companion_unchanged'].values())
    result['checker_unchanged_during_review']=digest(CHECKER.read_bytes())==result['checker_sha256']
    assert result['checker_unchanged_during_review']
    PINS[str(Path(__file__).resolve())]=digest(Path(__file__).read_bytes())
    (HERE/'source_manifest.json').write_text(json.dumps(PINS,indent=2,sort_keys=True)+'\n')
    (HERE/'commands.json').write_text(json.dumps(COMMANDS,indent=2)+'\n')
    (HERE/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({k:v for k,v in result.items() if k not in ('closure','cache_paths','side_effect_token_scan')},indent=2))
    print(json.dumps({'closure':{k:v for k,v in result['closure'].items() if k not in ('topological_order','external_resolution','excluded_existing')},'excluded_existing':result['closure']['excluded_existing'],'side_effect_tokens':result['side_effect_token_scan']},indent=2))


if __name__=='__main__':
    main()
