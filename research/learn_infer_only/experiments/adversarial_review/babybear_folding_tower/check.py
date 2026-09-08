"""Independent source/pin/patch and pure field-arithmetic checks.

Does not import author code, launch Lean, or execute a cryptographic protocol.
"""
from collections import Counter
from fractions import Fraction as Q
from hashlib import sha256
from math import isqrt
from pathlib import Path
import json
import re

HERE=Path(__file__).resolve().parent
ROOT=HERE.parents[4]
FORMAL=ROOT/'research/proof_frontier/2026-09-08/formal'
AUTHOR=FORMAL/'babybear_folding_tower'
CHECKOUT=Path('/tmp/minidregg-babybear-folding-tower-20260908')
COMPANION=Path('/Users/ember/dev/minidregg')
EXPECTED_MANIFEST='ae965e4e43fdded42b7992ee8ee9a1a265085c9ab861e2c481fef75ca1e14dc2'
EXPECTED_PATCH='900f184c759ff80a1debe2e585ca9f493b4bd13d65a77feb8762f9d07651779a'


def read_public(path):
    path=Path(path).absolute()
    assert not {'.private','private','runtime','signer_route','verified_route'}.intersection(path.parts)
    assert any(path.is_relative_to(base) for base in [ROOT,COMPANION,CHECKOUT,
        Path('/Users/ember/dev/breadstuffs'),Path('/Users/ember/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7')])
    return path.read_bytes()


def pin(path):
    b=read_public(path)
    return {'path':str(Path(path).absolute()),'bytes':len(b),'sha256':sha256(b).hexdigest()}


assert pin(AUTHOR/'manifest.json')['sha256']==EXPECTED_MANIFEST
assert pin(AUTHOR/'babybear-folding-tower.patch')['sha256']==EXPECTED_PATCH
manifest=json.loads(read_public(AUTHOR/'manifest.json'))
evidence=json.loads(read_public(AUTHOR/'source-evidence.json'))
assert pin(AUTHOR/'source-evidence.json')['sha256']==manifest['source_evidence_sha256']
frozen=[]
# Restrict discovery to the already inventoried public author package.
for path in sorted(AUTHOR.rglob('*')):
    if path.is_file():
        frozen.append(pin(path))
for path,entry in evidence['sources'].items():
    assert pin(path)['sha256']==entry['sha256'],path
    frozen.append(pin(path))

# Match the sixteen predecessor declarations to their frozen originals and
# the exact isolated checkout used by the saved final module checks.
core=json.loads(read_public(FORMAL/'full_ud/manifest.json'))
core_map={x['path']:x for x in core['modules']}
dep_origins={}
for d in manifest['dependencies']:
    rel=d['path']
    if d['frozen_source']=='full_ud/manifest.json':
        assert core_map[rel]['sha256']==d['sha256']
        if core_map[rel]['owned']:
            origin=FORMAL/'full_ud/src'/rel
        elif Path(rel).name=='PolynomialMatrixKernel.lean':
            origin=FORMAL/'polynomial_kernel/all_pins_successor'/Path(rel).name
        else:
            origin=FORMAL/'polynomial_gluing/universe_successor'/Path(rel).name
    else:
        origin=FORMAL/d['frozen_source']
    assert pin(origin)['sha256']==d['sha256'],str(origin)
    assert pin(CHECKOUT/rel)['sha256']==d['sha256'],rel
    dep_origins[rel]=str(origin)
    frozen.extend([pin(origin),pin(CHECKOUT/rel)])
assert len(dep_origins)==16
base_modules=['Selvage/BabyBearExt4.lean','Selvage/Proximity.lean',
    'Selvage/HalfThresholdFriCoherent.lean','Selvage/HalfThresholdFriQuery.lean',
    'Selvage/ReedSolomon.lean','Selvage/Commitment.lean','Selvage/Rbr.lean']
for path in base_modules:
    assert read_public(CHECKOUT/path)==read_public(COMPANION/path),path
    frozen.extend([pin(CHECKOUT/path),pin(COMPANION/path)])
for path in ['lean-toolchain','lake-manifest.json','scripts/check-import-boundary.sh']:
    frozen.append(pin(CHECKOUT/path))
assert read_public(CHECKOUT/'lean-toolchain').strip()==b'leanprover/lean4:v4.30.0'
census_script=ROOT/'research/learn_infer_only/experiments/integration/check_all_formal.py'
assert pin(census_script)['sha256']==manifest['root_census_script_sha256']
frozen.append(pin(census_script))


def mask_comments_strings(text):
    """Small independent lexer for the concrete files, preserving line positions."""
    out=list(text);i=0;depth=0;string=False
    while i<len(text):
        if depth:
            if text.startswith('/-',i):
                out[i:i+2]=[' ',' '];depth+=1;i+=2;continue
            if text.startswith('-/',i):
                out[i:i+2]=[' ',' '];depth-=1;i+=2;continue
            if text[i]!='\n':out[i]=' '
            i+=1;continue
        if string:
            if text[i]=='\\' and i+1<len(text):
                out[i:i+2]=[' ',' '];i+=2;continue
            if text[i]=='"':string=False
            if text[i]!='\n':out[i]=' '
            i+=1;continue
        if text.startswith('/-',i):
            out[i:i+2]=[' ',' '];depth=1;i+=2;continue
        if text.startswith('--',i):
            while i<len(text) and text[i]!='\n':out[i]=' ';i+=1
            continue
        if text[i]=='"':string=True;out[i]=' '
        i+=1
    assert depth==0 and not string
    return ''.join(out)


saved_census=json.loads(read_public(AUTHOR/'integration_census.json'))
declared_names=json.loads(read_public(AUTHOR/'declaration-names.json'))
pin_pattern=re.compile(r"/-- info: '([^']+)' depends on axioms: \[([^\]]*)\] -/\s*#guard_msgs \(whitespace := lax\) in #print axioms ([A-Za-z0-9_.]+)")
checked_declarations=[];axiom_counts=Counter();module_reports=[];all_source={}
for number,module in enumerate(manifest['modules'],1):
    path=module['path'];src=read_public(AUTHOR/'src'/path).decode()
    assert sha256(src.encode()).hexdigest()==module['sha256']
    assert read_public(CHECKOUT/path)==src.encode()
    all_source[path]=src
    masked=mask_comments_strings(src)
    forbidden=re.findall(r'\b(?:sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|elab|macro)\b|#(?:eval|reduce)',masked)
    assert forbidden==[],(path,forbidden)
    scope=[];declarations=[]
    for line_no,line in enumerate(masked.splitlines(),1):
        line=line.strip()
        if line.startswith('namespace '):scope.append(('namespace',line[10:].strip()))
        elif re.match(r'(?:noncomputable )?section(?:\s|$)',line):scope.append(('section',''))
        elif re.match(r'end(?:\s|$)',line):assert scope;scope.pop()
        m=re.match(r'theorem ([A-Za-z0-9_]+)',line)
        if m:
            fqn='.'.join([value for kind,value in scope if kind=='namespace']+[m[1]])
            declarations.append({'name':m[1],'qualified_name':fqn,'private':False,'line':line_no})
    assert not scope
    guards=[]
    for match in pin_pattern.finditer(src):
        named,axioms,requested=match.groups();assert named==requested
        ax=axioms.split(', ')
        assert set(ax)<= {'propext','Classical.choice','Quot.sound'}
        axiom_counts[tuple(ax)]+=1
        guards.append((named,ax))
    names=[x['qualified_name'] for x in declarations]
    assert names==declared_names[Path(path).stem]
    assert len(names)==len(set(names))==len(guards)==module['pin_count']==module['theorem_count']
    assert [name for name,_ in guards]==names
    assert len(re.findall('#guard_msgs',masked))==len(guards)
    saved=saved_census[path]
    assert saved['qualified_declarations']==declarations
    assert saved['forbidden_constructs']==[] and saved['admit_identifier_tokens']==[]
    assert [(x['theorem'],x['axioms']) for x in saved['pins']]==guards
    check=json.loads(read_public(AUTHOR/'logs'/f'freeze-{number:02d}.json'))
    assert check==module['check'] and check['source_sha256']==module['sha256']
    assert check['source_unchanged'] and check['exit_code']==0
    assert check['cwd']==str(CHECKOUT) and check['command'][-1]==path
    assert check['command'][:3]==['lake','env','lean']
    assert read_public(AUTHOR/'logs'/f'freeze-{number:02d}.log')==b''
    checked_declarations.extend(declarations)
    module_reports.append({'path':path,'theorems':len(names),'guards':len(guards),'saved_exit_code':0})
assert len(checked_declarations)==manifest['owned_theorems']==manifest['owned_pins']==48
assert sum(len(x.splitlines()) for x in all_source.values())==manifest['owned_lines']==683
assert axiom_counts=={('propext','Classical.choice','Quot.sound'):46,('propext','Quot.sound'):2}

# The additive patch reconstructs exactly these four sources, with no deleted
# or modified predecessor file. Saved author git-apply logs are also retained.
patch=read_public(AUTHOR/'babybear-folding-tower.patch').decode()
patch_sources={}
for chunk in patch.split('diff --git ')[1:]:
    lines=chunk.splitlines(keepends=True)
    header=lines[0].strip().split()
    assert len(header)==2 and header[0][2:]==header[1][2:]
    path=header[1][2:]
    assert 'new file mode 100644\n' in lines and '--- /dev/null\n' in lines
    assert f'+++ b/{path}\n' in lines
    hunk_index=next(i for i,line in enumerate(lines) if line.startswith('@@ '))
    body=lines[hunk_index+1:]
    assert all(line.startswith('+') for line in body)
    reconstructed=''.join(line[1:] for line in body)
    assert reconstructed==all_source[path]
    patch_sources[path]=sha256(reconstructed.encode()).hexdigest()
assert set(patch_sources)==set(all_source)
entry=json.loads(read_public(AUTHOR/'integration_entry.json'))
assert entry['expected_pins']==48 and set(entry['source_files'])==set(all_source)
assert manifest['umbrella_imports_proposed']==['Selvage.BabyBearFoldingWitnesses']
assert read_public(AUTHOR/'logs/patch-apply.log').decode().startswith('PASS: clean git apply --check')
assert read_public(AUTHOR/'logs/import-boundary.log').decode().count('OK:')==2

# Pure arithmetic independent of Lean or runtime Rust arithmetic.
p=2013265921;g=440564289
assert p-1==15*2**27 and all(p%d for d in range(2,isqrt(p)+1))
assert pow(31,15,p)==g and pow(g,2**26,p)==p-1 and pow(g,2**27,p)==1
assert pow(g*g%p,2**26,p)==1
p3_path=Path('/Users/ember/.cargo/git/checkouts/plonky3-7d8a3b21a665a86f/82cfad7/baby-bear/src/baby_bear.rs')
p3text=read_public(p3_path).decode().split('const TWO_ADIC_GENERATORS:')[1].split(']);')[0]
p3roots=[int(x,16) for x in re.findall(r'0x[0-9a-fA-F]+',p3text)]
roots=[pow(g,2**(27-bits),p) for bits in range(28)]
assert roots==p3roots and roots[20]==195061667
for bits,root in enumerate(roots):
    assert pow(root,2**bits,p)==1
    if bits:assert pow(root,2**(bits-1),p)==p-1
initial=roots[20];laws=0;coherent=0;folds=0;level_rows=[]
for level in range(20):
    size=2**(20-level);degree=2**(19-level);root=pow(initial,2**level,p)
    assert root==roots[20-level] and Q(degree,size)==Q(1,2)
    level_rows.append({'level':level,'domain_size':size,'degree_bound':degree,'root':root})
    if level==19:continue
    half=size//2;nextroot=pow(initial,2**(level+1),p)
    indices=sorted({i%size for i in [0,1,2,3,5,17,127,half-1,half,size-2,size-1]})
    for i in indices:
        value=pow(root,i,p);neg=(i+half)%size;sq=i%half
        assert value!=0 and (2*value)%p!=0
        assert pow(root,neg,p)==(-value)%p
        assert pow(nextroot,sq,p)==value*value%p
        assert ((neg+half)%size)==i and (neg%half)==sq
        assert sq<half and (sq+half)<size and ((sq+half)%size)==sq+half
        laws+=1
    for seed in [0,1,2,3,7,127,2**18,2**19-1]:
        index=seed%half
        assert pow(nextroot,index,p)==pow(pow(initial,2*seed,p),2**level,p)
        coherent+=1
    if level==0:
        for k in sorted({i%half for i in [0,1,2,3,17,127,half-2,half-1]}):
            x=pow(root,k,p);fx=pow(x,2**19,p);fn=pow((-x)%p,2**19,p)
            assert fx==fn==pow(p-1,k,p)
            for challenge in [0,1,7,p-1]:
                folded=((fx+fn)*pow(2,-1,p)+challenge*(fx-fn)*pow(2*x,-1,p))%p
                assert folded==fx
                assert (folded==1)==(k%2==0)
                folds+=1
assert level_rows[-1]['domain_size']==2 and level_rows[-1]['degree_bound']==1
assert Q(1,2)>Q(2,5)
radius=lambda j:Q(2,5) if j==0 else Q(19-j,95)
for j in range(19):
    foldradius=Q(1,5) if j==0 else radius(j)
    assert radius(j+1)+Q(1,95)==foldradius
    if j:assert 0<radius(j)<Q(1,4)
assert radius(19)==0
challenge_term=Q(19*2**20,p**4)
query_term=Q(94,95)**3603
assert challenge_term+query_term<=Q(1,2**55)
# Counting consequence for this specific ideal witness: parity is the only
# nontrivial equation. This derived identity is not an added Lean theorem.
assert Q(2**18,2**19)==Q(1,2)
assert Q(1,2)**3603>0 and Q(1,2)**3603<=Q(1,2**55)

# Deduplicate explicit public inputs and verify no frozen byte changed.
by_path={x['path']:x for x in frozen}
for expected in by_path.values():assert pin(expected['path'])==expected
inputs={'scope':'Named frozen author/source/dependency records only. No private or runtime artifacts.',
        'frozen_public_files':list(by_path.values()),'dependency_origins':dep_origins}
(HERE/'INPUTS.json').write_text(json.dumps(inputs,indent=2)+'\n')
out={'status':'PASS','scope':'Independent source/axiom/patch census and pure modular/rational arithmetic. No Lean or cryptographic execution.',
 'author_manifest_sha256':EXPECTED_MANIFEST,'author_patch_sha256':EXPECTED_PATCH,
 'author_modules':module_reports,'qualified_declarations':checked_declarations,
 'guard_axiom_sets':[{'axioms':list(k),'count':v} for k,v in axiom_counts.items()],
 'frozen_dependency_count':len(dep_origins),'frozen_source_evidence_files':len(evidence['sources']),
 'seven_base_module_bytes_match_isolated_checkout':True,
 'patch_reconstructs_only_four_additive_files':patch_sources,
 'isolated_toolchain':'leanprover/lean4:v4.30.0',
 'base_prime':p,'generator':g,'all_28_p3_root_entries_match':True,
 'root_table':roots,'levels':level_rows,'sampled_domain_law_cases':laws,
 'coherent_index_cases':coherent,'actual_first_fold_controls':folds,
 'farWord_distance_lower':{'numerator':1,'denominator':2},
 'witness_acceptance_probability_derived_not_new_Lean':'2^-3603',
 'frozen_55_bound_verified':True,'initial_2_5_farness_verified':True,
 'frozen_public_files_unchanged':len(by_path),'new_Lean_runs':0,'new_crypto_runs':0,
 'web_queries':0,'PDF_downloads':0,'Scry_queries':0}
text=json.dumps(out,indent=2)+'\n';(HERE/'results.json').write_text(text);print(text,end='')
