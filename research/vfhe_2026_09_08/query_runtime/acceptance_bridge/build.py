#!/usr/bin/env python3
"""Build an instrumentation-only copy; never write original sources or companion trees."""
import difflib, hashlib, json, pathlib, shutil, subprocess
HERE=pathlib.Path(__file__).resolve().parent
QUERY=HERE.parent
VFHE=QUERY.parent
FRI=pathlib.Path('/Users/ember/dev/breadstuffs/vendor/plonky3-fri-82cfad73')
OUT=QUERY/'target/acceptance_bridge/overlay'
# The launch records exact source bytes; original verifier source is copied, not reimplemented.
def sha(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def replace(p,a,b):
    s=p.read_text()
    assert s.count(a)==1,(str(p),a[:100],s.count(a))
    p.write_text(s.replace(a,b))
def emit(kind,expr): return f'bridge_events::emit("{kind}", serde_json::json!({expr}));'
def main():
    OUT.mkdir(parents=True,exist_ok=False)
    for name,src in [('fri',FRI),('backend',VFHE/'proved_operation/backend')]:
        (OUT/name).mkdir()
        shutil.copytree(src/'src',OUT/name/'src')
        shutil.copy2(src/'Cargo.toml',OUT/name/'Cargo.toml')
    (OUT/'events').mkdir()
    (OUT/'events/Cargo.toml').write_text('[package]\nname="bridge-events"\nversion="0.1.0"\nedition="2024"\n[lib]\npath='+json.dumps(str(HERE/'events.rs'))+'\n[dependencies]\nserde_json="1"\n')
    dep='bridge-events = { path = "../events" }\nserde_json = "1"\n'
    for name in ['fri','backend']:
        p=OUT/name/'Cargo.toml'
        replace(p,'[dependencies]\n','[dependencies]\n'+dep+('serde = "1"\n' if name=='backend' else ''))
    p=OUT/'backend/src/lib.rs'
    replace(p,'type Challenger=DuplexChallenger<BabyBear,Perm,16,8>;', 'type Challenger=LoggedChallenger;\n'+(HERE/'challenger.rs').read_text())
    p=OUT/'fri/src/lib.rs'
    replace(p,'extern crate alloc;','extern crate alloc;\nextern crate std;')
    p=OUT/'fri/src/verifier.rs'
    replace(p,'    let alpha: Challenge = challenger.sample_algebra_element();','    '+emit('fri_begin','{"log_blowup":params.log_blowup,"log_final_poly_len":params.log_final_poly_len,"max_log_arity":params.max_log_arity,"num_queries":params.num_queries,"commit_pow_bits":params.commit_proof_of_work_bits,"query_pow_bits":params.query_proof_of_work_bits}')+'\n    let alpha: Challenge = challenger.sample_algebra_element();\n    '+emit('fri_alpha','{"alpha":alpha}'))
    anchor='    if proof.commit_pow_witnesses.len() != proof.commit_phase_commits.len() {'
    insert='''    let mut input_heights: alloc::vec::Vec<usize> = commitments_with_opening_points.iter().flat_map(|(_,mats)| mats.iter().map(|(d,_)| log2_strict_usize(d.size())+params.log_blowup)).collect();
    input_heights.sort_unstable(); input_heights.dedup(); input_heights.reverse();
    let mut canonical_arities=alloc::vec::Vec::new();
    if let Some(&max_h)=input_heights.first() {
        let final_h=params.log_blowup+params.log_final_poly_len;
        let mut h=max_h;
        while h>final_h {
            let next=input_heights.iter().copied().find(|&v|v<h);
            let a=crate::compute_log_arity_for_round(h,next,final_h,params.max_log_arity);
            canonical_arities.push(a); h-=a;
        }
    }
    bridge_events::emit("fri_schedule",serde_json::json!({"actual_log_arities":log_arities,"canonical_log_arities":canonical_arities,"canonical_schedule_matches":canonical_arities==log_arities,"input_log_heights":input_heights,"log_global_max_height":log_global_max_height,"extra_query_index_bits":folding.extra_query_index_bits(),"observed_in_transcript_only_after_betas":true}));
'''
    replace(p,anchor,insert+anchor)
    replace(p,'            challenger.observe(comm.clone());','            '+emit('fri_commit_observe','{"commitment":comm,"pow_witness":witness}')+'\n            challenger.observe(comm.clone());')
    replace(p,'            Ok(challenger.sample_algebra_element())','            let beta:Challenge=challenger.sample_algebra_element();\n            '+emit('fri_beta','{"beta":beta}')+'\n            Ok(beta)')
    replace(p,'    challenger.observe_algebra_slice(&proof.final_poly);','    '+emit('fri_final_poly_observe','{"coefficients":proof.final_poly}')+'\n    challenger.observe_algebra_slice(&proof.final_poly);')
    replace(p,'    // Check PoW.','    '+emit('fri_schedule_observed','{"log_arities":log_arities}')+'\n    // Check PoW.')
    replace(p,'    for QueryProof {','    let mut bridge_query=0usize;\n    for QueryProof {')
    replace(p,'        // Next we open all polynomials', '        '+emit('fri_query','{"query":bridge_query,"index":index}')+'\n        // Next we open all polynomials')
    replace(p,'        debug_assert!(\n            ro.iter()', '        '+emit('fri_reduced_openings','{"query":bridge_query,"values":ro}')+'\n        debug_assert!(\n            ro.iter()')
    replace(p,'        if eval != folded_eval {','        '+emit('fri_terminal_check','{"query":bridge_query,"domain_index":domain_index,"x":x,"evaluation":eval,"folded_eval":folded_eval,"equal":eval==folded_eval}')+'\n        bridge_query+=1;\n        if eval != folded_eval {')
    replace(p,'        // Fold the group of sibling nodes', '        '+emit('fri_packed_row_verified','{"round":round,"log_current_height":log_current_height,"log_folded_height":log_folded_height,"extension_width":arity,"base_width":arity*EF::DIMENSION,"index_in_group":index_in_group,"parent_index":*start_index,"commitment":comm,"evals":evals,"opening_proof":opening.opening_proof,"beta":beta}')+'\n        // Fold the group of sibling nodes')
    replace(p,'        // Update current height','        '+emit('fri_fold_result','{"round":round,"before_injection":folded_eval}')+'\n        // Update current height')
    replace(p,'            folded_eval += beta_pow * ro;','            folded_eval += beta_pow * ro;\n            '+emit('fri_injection','{"round":round,"log_height":log_folded_height,"reduced_opening":ro,"beta_power":beta_pow,"after_injection":folded_eval}'))
    replace(p,'        }\n    }\n\n    // Verify we reached', '        }\n        '+emit('fri_round_carried','{"round":round,"value":folded_eval,"index":*start_index}')+'\n    }\n\n    // Verify we reached')
    replace(p,'        // For each matrix in the commitment','        '+emit('input_batch_verified','{"batch":batch,"root":batch_commit,"heights":batch_heights,"reduced_index":reduced_index,"opened_values":batch_opening.opened_values,"opening_proof":batch_opening.opening_proof}')+'\n        // For each matrix in the commitment')
    replace(p,'            // For each polynomial `f` in our matrix,','            '+emit('input_matrix','{"batch":batch,"matrix":matrix,"log_height":log_height,"width":mat_opening.len(),"index":index>>bits_reduced,"reversed_index":rev_reduced_index,"x":x,"alpha_power_start":*alpha_pow,"reduced_opening_start":*ro,"points_and_values":mat_points_and_values}')+'\n            // For each polynomial `f` in our matrix,')
    replace(p,'            }\n        }\n\n        // `reduced_openings`','            }\n            '+emit('input_matrix_reduced','{"batch":batch,"matrix":matrix,"log_height":log_height,"alpha_power_end":*alpha_pow,"reduced_opening_end":*ro}')+'\n        }\n\n        // `reduced_openings`')
    p=OUT/'fri/src/two_adic_pcs.rs'
    replace(p,'        lagrange_interpolate_at(&xs, &evals, beta)','        let result=lagrange_interpolate_at(&xs, &evals, beta);\n        '+emit('native_fold','{"parent_index":index,"log_height":log_height,"log_arity":log_arity,"subgroup_start":subgroup_start,"xs":xs,"evals":evals,"beta":beta,"result":result}')+'\n        result')
    claim_map='commitments_with_opening_points.iter().map(|(c,ms)|serde_json::json!({"root":c,"matrices":ms.iter().map(|(d,pv)|serde_json::json!({"log_domain_size":d.log_size(),"domain_shift":d.shift(),"points_and_values":pv})).collect::<alloc::vec::Vec<_>>()})).collect::<alloc::vec::Vec<_>>()'
    replace(p,'        // Write all evaluations to challenger.','        '+emit('pcs_claims','{"batches":'+claim_map+'}')+'\n        // Write all evaluations to challenger.')
    p=OUT/'fri/src/hiding_pcs.rs'
    replace(p,'        let (opened_values_for_rand_cws, inner_proof) = proof;','        let (opened_values_for_rand_cws, inner_proof) = proof;\n        '+emit('hiding_claims_before_merge','{"batches":'+claim_map.replace('commitments_with_opening_points','rounds')+',"random_codeword_openings":opened_values_for_rand_cws}'))
    (OUT/'src').mkdir()
    shutil.copy2(QUERY/'src/main.rs',OUT/'src/main.rs')
    # Expose only verification; the copied parser/statement construction is unchanged.
    p=OUT/'src/main.rs'
    replace(p,'fn main() -> Result<()> {','fn original_main() -> Result<()> {')
    with p.open('a') as f:
        f.write('\nfn main()->Result<()> {let a:Vec<String>=std::env::args().collect(); if a.len()!=4{return Err("usage: vfhe-acceptance-bridge TEMPLATE CASE PROOF".into())} verify(Path::new(&a[1]),Path::new(&a[2]),Path::new(&a[3]),false)}\n')
    cargo=(QUERY/'Cargo.toml').read_text().replace('name = "vfhe-query-runtime"','name = "vfhe-acceptance-bridge"').replace('../proved_operation/backend','backend').replace(str(FRI),'fri')
    (OUT/'Cargo.toml').write_text(cargo)
    shutil.copy2(QUERY/'Cargo.lock',OUT/'Cargo.lock')
    changes=[];pins={}
    for name,src in [('fri',FRI),('backend',VFHE/'proved_operation/backend')]:
        for p in sorted((OUT/name).rglob('*')):
            if p.is_file():
                rel=p.relative_to(OUT/name); old=src/rel
                pins[str(old)]=sha(old)
                if old.read_bytes()!=p.read_bytes():
                    changes.extend(difflib.unified_diff(old.read_text().splitlines(True),p.read_text().splitlines(True),fromfile=str(old),tofile=str(p)))
    (HERE/'instrumentation.patch').write_text(''.join(changes))
    (HERE/'build_inputs.json').write_text(json.dumps({'scope':'instrumentation-only copies; original files unmodified','source_sha256':pins,'query_source':{'path':str(QUERY/'src/main.rs'),'sha256':sha(QUERY/'src/main.rs')}},indent=2)+'\n')
    cmd=['cargo','build','--release','--offline','--manifest-path',str(OUT/'Cargo.toml'),'--target-dir',str(QUERY/'target')]
    print(json.dumps({'argv':cmd}),flush=True)
    subprocess.run(cmd,check=True)
if __name__=='__main__': main()
