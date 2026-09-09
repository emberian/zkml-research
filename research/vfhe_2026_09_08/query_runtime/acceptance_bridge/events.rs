//! Instrumentation only. One ordered event stream shared by the copied backend and FRI crate.
use std::sync::Mutex;
static SEQUENCE: Mutex<u64> = Mutex::new(0);
pub fn emit(kind: &str, data: serde_json::Value) {
    let mut seq = SEQUENCE.lock().unwrap();
    eprintln!("{}", serde_json::json!({"seq":*seq,"kind":kind,"data":data}));
    *seq += 1;
}
