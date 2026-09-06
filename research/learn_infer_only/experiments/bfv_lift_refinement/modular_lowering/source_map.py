#!/usr/bin/env python3
"""Pin local primary source locations and proof endpoints; no source-tree edits."""
import hashlib,json,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parent;crate=Path('/Users/ember/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/fhe-math-0.1.1')
locations=[('src/zq/mod.rs',17,22,'constant-time mask/xor selector','FheBarrettWord.mask_selection'),('src/zq/mod.rs',54,69,'Modulus bounds and Barrett reciprocal constructor','FheRnsSourceWord.target_word_bounds'),('src/zq/mod.rs',169,208,'Shoup reciprocal and lazy multiplication','FheShoupWord.wordLazyShoup_correct'),('src/zq/mod.rs',577,580,'canonical u128 reduction wrapper','FheBarrettWord.wordReduce_correct'),('src/zq/mod.rs',635,645,'one-step lazy residue correction','FheBarrettWord.wordReduceOne_correct'),('src/zq/mod.rs',672,687,'two-word lazy Barrett reduction','FheBarrettWord.wordLazyBarrett_correct'),('src/rns/scaler.rs',76,116,'gamma and omega projection/Shoup setup','FheRnsModularAccumulation.projected_product; constructor remains inspected source'),('src/rns/scaler.rs',250,304,'Garner and correction accumulators/sign/magnitude','existing FheRnsScale word lemmas; FheRnsSourceWord magnitude lemmas'),('src/rns/scaler.rs',307,340,'per-target initialization/correction/product accumulation/reduction','FheRnsSourceWord.sourceWordRefinement'),('src/rns/mod.rs',109,119,'BigUint projection into target residues','inspected constructor source; no Rust BigUint proof')]
records=[]
for rel,start,end,seen,endpoint in locations:
 p=crate/rel;records.append(dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),lines=[start,end],actually_seen='implementation source',operation=seen,proof_endpoint=endpoint))
report=dict(label='SOURCE exact local implementation map; DERIVED theorem correspondence, not Rust semantics refinement',command=[sys.executable,str(Path(__file__).resolve())],records=records,metered_search_queries=0,pdf_downloads=0)
(ROOT/'source-map.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({r['path']:r['sha256'] for r in records},indent=2))
