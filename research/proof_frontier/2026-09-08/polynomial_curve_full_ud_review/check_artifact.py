#!/usr/bin/env python3
"""Read-only audit of frozen curve package, with patch replay in fresh temp dir."""
from pathlib import Path
import collections, hashlib, json, re, subprocess, tempfile

HERE=Path(__file__).resolve().parent
PACKAGE=HERE.parent/'formal/polynomial_curve_full_ud'
AFFINE=HERE.parent/'formal/full_ud'
KERNEL=HERE.parent/'formal/polynomial_curve_kernel'
BASE='6937394e1dc2c2aaff986c7d4b3a258aca5d16fd'
COMPANION=Path('/Users/ember/dev/minidregg')

def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def strip_comments(s):
    out=[]; depth=0; i=0
    while i<len(s):
        if s[i:i+2]=='/-': depth+=1;out.extend('  ');i+=2
        elif depth and s[i:i+2]=='-/': depth-=1;out.extend('  ');i+=2
        elif depth: out.append('\n' if s[i]=='\n' else ' ');i+=1
        elif s[i:i+2]=='--':
            k=s.find('\n',i)
            if k<0:k=len(s)
            out.extend(' '*(k-i));i=k
        else:out.append(s[i]);i+=1
    assert depth==0
    return ''.join(out)

def census(p):
    s=p.read_text();clean=strip_comments(s)
    decl=re.findall(r'^\s*(?:private\s+|protected\s+)?(?:theorem|lemma)\s+([\w\'.]+)',clean,re.M)
    pattern=r'/--\s*info:\s*\x27([^\x27]+)\x27\s+(depends on axioms: \[([^]]*)\]|does not depend on any axioms)\s*-/' + r'\s*#guard_msgs(?:\s*\(whitespace := lax\))?\s+in\s*#print axioms\s+([\w\'.]+)'
    guards=list(re.finditer(pattern,s,re.S))
    assert len(decl)==len(guards),(p,len(decl),len(guards))
    assert collections.Counter(x.split('.')[-1] for x in decl)==collections.Counter(m.group(4).split('.')[-1] for m in guards),p
    assert len(re.findall(r'#print\s+axioms',clean))==len(guards),p
    assert len(re.findall(r'#guard_msgs\b',clean))==len(guards),p
    for m in guards:
        assert m.group(1)==m.group(4) or re.fullmatch(r'_private\..+\.\d+\.'+re.escape(m.group(4)),m.group(1)),(p,m.group(1),m.group(4))
        assert set(x.strip() for x in (m.group(3) or '').split(',') if x.strip()) <= {'propext','Classical.choice','Quot.sound'},p
    assert not re.search(r'\b(sorry|axiom|admit|native_decide|implemented_by|unsafe)\b',clean),p
    return {'declarations':decl,'pins':[m.group(4) for m in guards],
            'imports':re.findall(r'^import\s+(\S+)',clean,re.M),'sha256':sha(p)}

def main():
    manifest_path=PACKAGE/'manifest.json'
    assert sha(manifest_path)=='fed8141f3d1606cd7ffa25bdd85918acbbdcb1ac8037307359adf1ff05994729'
    manifest=json.loads(manifest_path.read_text())
    modules=sorted((PACKAGE/'src').rglob('*.lean'))
    assert len(modules)==10,len(modules)
    records={str(p.relative_to(PACKAGE/'src')):census(p) for p in modules}
    assert sum(len(v['declarations']) for v in records.values())==42
    filepins=[{'path':str(p.relative_to(PACKAGE)),'sha256':sha(p)} for p in sorted(PACKAGE.rglob('*')) if p.is_file() and '__pycache__' not in p.parts]
    for item in manifest.get('files',[]):
        p=PACKAGE/item['path']
        assert sha(p)==item['sha256'],p
        filepins.append({'path':item['path'],'sha256':sha(p)})
    for item in manifest.get('modules',[]):
        if item.get('owned',True) and item['path'] in records:
            assert records[item['path']]['sha256']==item['sha256'],item
    checks=[]
    for rel,record in records.items():
        found=[]
        for p in (PACKAGE/'checks').glob('*.json'):
            j=json.loads(p.read_text())
            if j.get('source_sha256')==record['sha256'] and j.get('exit_code')==0 and j.get('source_unchanged'):
                log=Path(j['log'])
                if log.exists() and not log.read_text().strip():
                    found.append({'record':str(p.relative_to(PACKAGE)),'log':str(log.relative_to(PACKAGE)),
                                  'record_sha256':sha(p),'log_sha256':sha(log),'command':j['command']})
        assert found,('No exact green guarded log',rel)
        checks.append({'source':rel,'matching_clean_checks':found})
    # Verify selected immutable affine source bytes in both original and author's isolate.
    isolate=Path(manifest.get('checkout','/tmp/minidregg-polynomial-curve-full-ud-20260908'))
    declared_deps=[]
    for item in manifest['dependencies']:
        assert sha(isolate/item['path'])==item['sha256'],item
        declared_deps.append(item)
    evidence=PACKAGE/'source-evidence.json'
    assert sha(evidence)==manifest['source_evidence_sha256']
    for item in json.loads(evidence.read_text()).values():
        if isinstance(item,dict) and 'path' in item and 'sha256' in item:
            assert sha(Path(item['path']))==item['sha256'],item
    predecessor=[]
    for item in json.loads((AFFINE/'manifest.json').read_text())['modules']:
        if not item.get('owned',False):continue
        p=AFFINE/'src'/item['path'];q=isolate/item['path']
        assert sha(p)==item['sha256'] and sha(q)==item['sha256'],item['path']
        predecessor.append({'path':item['path'],'sha256':sha(p)})
    ps_package=HERE.parent/'formal/polynomial_gluing/universe_successor'
    ps=[]
    for item in json.loads((ps_package/'SHA256.json').read_text()):
        p=ps_package/Path(item['file']).name
        assert sha(p)==item['sha256'] and sha(isolate/item['file'])==item['sha256'],item
        ps.append({'path':item['file'],'sha256':sha(p)})
    kernel=KERNEL/'PolynomialMatrixKernel.lean'
    assert sha(kernel)=='f510b6cc0c648a3583e3eefa49e283b2186add24d2e4df71f3afeb9b06a3fa91'
    assert sha(isolate/'Theory/PolynomialMatrixKernel.lean')==sha(kernel)
    kernel_census=census(kernel)
    assert len(kernel_census['declarations'])==26
    # Pin direct dependency source bytes. Owned imports resolve to the audited modules;
    # all external Theory imports remain within Mathlib/Theory boundaries.
    deps={}
    for rel,record in records.items():
        for mod in record['imports']:
            if rel.startswith('Theory/'):
                assert mod.startswith(('Theory.','Mathlib.')), (rel,mod)
            if mod.startswith('Mathlib.'): continue
            dep=mod.replace('.','/')+'.lean'
            q=isolate/dep
            assert q.exists(),q
            if dep not in records:deps[dep]=sha(q)
            else:assert sha(q)==records[dep]['sha256']
    theory_boundary={}
    pending=[rel for rel in records if rel.startswith('Theory/')]
    while pending:
        rel=pending.pop()
        if rel in theory_boundary:continue
        q=isolate/rel
        imports=re.findall(r'^import\s+(\S+)',strip_comments(q.read_text()),re.M)
        assert all(m.startswith(('Theory.','Mathlib.')) for m in imports),(rel,imports)
        theory_boundary[rel]={'sha256':sha(q),'imports':imports}
        pending.extend(m.replace('.','/')+'.lean' for m in imports if m.startswith('Theory.'))
    patches=list(PACKAGE.glob('*.patch'))
    assert len(patches)==1,patches
    patch=patches[0]
    assert sha(patch)==manifest['patch_sha256']=='3fa34548e2f1ec0f286ba04594374f3fc5aa636fda5dd5f7583bdeeca6dd7d0f'
    targets=re.findall(r'^\+\+\+ b/(.+)$',patch.read_text(),re.M)
    assert set(records)==set(targets),(set(records)-set(targets))
    replay=[]
    with tempfile.TemporaryDirectory(prefix='curve-full-ud-review-') as name:
        target=Path(name)
        subprocess.run(['git','init','-q',str(target)],check=True)
        for rel in targets:
            old=subprocess.run(['git','show',f'{BASE}:{rel}'],cwd=COMPANION,capture_output=True)
            if old.returncode==0:
                p=target/rel;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(old.stdout)
        for args in (['git','apply','--check',str(patch)],['git','apply',str(patch)]):
            r=subprocess.run(args,cwd=target,capture_output=True,text=True)
            assert r.returncode==0,(args,r.stdout,r.stderr)
        for rel in targets:
            q=target/rel
            expected=PACKAGE/'src'/rel
            if not expected.exists():expected=isolate/rel
            assert q.read_bytes()==expected.read_bytes(),rel
            replay.append({'path':rel,'sha256':sha(q)})
    result={'status':'PASS','scope':'Source/guard/manifest/dependency census and exact patch replay; no Lean build performed by reviewer.',
       'author_manifest_sha256':sha(manifest_path),'patch':patch.name,'patch_sha256':sha(patch),
       'owned_modules':records,'owned_declarations':42,'exact_guarded_pins':42,
       'reviewer_package_file_pins':filepins,'matching_author_checks':checks,
       'declared_dependency_pins_checked':declared_deps,'theory_import_closure':theory_boundary,'frozen_affine_modules_preserved':predecessor,'kernel_source_sha256':sha(kernel),
       'kernel_declarations_and_pins':26,'unchanged_PS_successor_sources':ps,'direct_nonowned_dependencies':deps,
       'patch_targets_replayed':replay,'script_sha256':sha(Path(__file__))}
    (HERE/'ARTIFACT_CHECKS.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','modules':10,'pins':42,'package_files_pinned':len(filepins),
                      'patch_targets':len(targets),'dependencies':len(deps)}))
if __name__=='__main__':main()
