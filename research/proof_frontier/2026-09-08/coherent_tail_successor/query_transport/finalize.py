from pathlib import Path
import hashlib,json,re
root=Path(__file__).resolve().parent
repo=Path('/tmp/minidregg-coherent-query-transport-20260908')
mods={'Selvage/ConsistencyQueryMass.lean':'sealed-mass','Selvage/ConsistencyCoherentTransport.lean':'sealed-transport','Selvage/ConsistencyTransportWitnesses.lean':'sealed-witnesses'}
items=[]
forbidden=[]
for p,tag in mods.items():
    data=(repo/p).read_bytes()
    frozen=root/'src'/p
    frozen.write_bytes(data)
    record=json.loads((root/'checks'/f'{tag}.json').read_text())
    sha=hashlib.sha256(data).hexdigest()
    assert record['source_sha256']==sha and record['source_unchanged'] and record['exit_code']==0
    log=(root/'checks'/f'{tag}.log').read_text()
    assert not log.strip(),log
    source=data.decode()
    hits=[{'file':p,'line':n+1,'text':line} for n,line in enumerate(source.splitlines()) if re.search(r'\b(?:sorry|native_decide)\b|^\s*axiom\s',line)]
    forbidden.extend(hits)
    items.append({'module':p.removesuffix('.lean').replace('/','.'),'source':str(frozen.relative_to(root)),'sha256':sha,'checked_in':str(repo/p),'proof_check':str(Path('checks')/(tag+'.json')),'axiom_guard_count':source.count('#print axioms')})
assert not forbidden
(root/'checks/forbidden.json').write_text(json.dumps({'claim_status':'[EXECUTED]','instrument':'Python re.search over the complete text of exactly the three frozen new Lean modules','pattern':r'\b(?:sorry|native_decide)\b|^\s*axiom\s','matches':forbidden},indent=2)+'\n')
(root/'MANIFEST.json').write_text(json.dumps({'status':'[EXECUTED] All three assigned new Lean modules pass individual source-stable checks with warning-free exact axiom guards.','base_minidregg_commit':'6937394e1dc2c2aaff986c7d4b3a258aca5d16fd','isolate':str(repo),'modules':items,'theorem_count':sum(x['axiom_guard_count']for x in items),'integration':'Only parent coherent_tail_successor combined patch; no standalone patch. Parent owns downstream head assembly and whole-tree integration gate.','dependency_snapshots':'SOURCES.json','frozen_dependency_refresh':'checks/frozen-dependency-refresh.json','import_boundary_check':'checks/import-boundary.json','forbidden_scan':'checks/forbidden.json','web_queries':0},indent=2)+'\n')
print(json.dumps({'manifest':str(root/'MANIFEST.json'),'theorem_count':sum(x['axiom_guard_count']for x in items),'modules':[{k:x[k]for k in ['module','sha256']}for x in items]},indent=2))
