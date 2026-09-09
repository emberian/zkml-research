
use dregg_circuit::descriptor_ir2::{parse_vm_descriptor2,grouped_shape_probe};
fn main(){
 let path=std::env::args().nth(1).expect("template JSON");
 let desc=parse_vm_descriptor2(&std::fs::read_to_string(&path).unwrap()).unwrap();
 let shape=grouped_shape_probe(&desc).unwrap();
 let instances:Vec<_>=shape.into_iter().map(|(name,width,raw,permutation,degree,log_q,buses)|serde_json::json!({"name":name,"main_width":width,"raw_global_interactions":raw,"permutation_ext4_columns":permutation,"max_constraint_degree":degree,"zk_log_quotient_chunks":log_q,"zk_quotient_chunks":1usize<<log_q,"main_plus_perm_base_equivalent":width+4*permutation,"buses":buses})).collect();
 println!("{}",serde_json::to_string_pretty(&serde_json::json!({"input":path,"instances":instances,"is_zk":1,"global_group_limit":4,"flattened_interactions_exact":true,"prover_or_preprocessing_executed":false})).unwrap());
}
