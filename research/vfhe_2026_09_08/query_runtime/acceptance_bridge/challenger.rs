// Concrete transparent wrapper: all real state transitions delegate to the original challenger.
// The extra clone in sample_bits observes the raw word without advancing the real transcript.
use p3_challenger::{CanObserve, CanSample, CanSampleBits, FieldChallenger, GrindingChallenger};
use p3_field::PrimeField64;
#[derive(Clone)]
pub struct LoggedChallenger(DuplexChallenger<BabyBear,Perm,16,8>);
impl LoggedChallenger {
    fn new(p:Perm)->Self {Self(DuplexChallenger::new(p))}
}
impl<T:serde::Serialize> CanObserve<T> for LoggedChallenger
where DuplexChallenger<BabyBear,Perm,16,8>:CanObserve<T> {
    fn observe(&mut self,v:T) {
        bridge_events::emit("transcript_observe",serde_json::json!({"rust_type":core::any::type_name::<T>(),"value":&v}));
        self.0.observe(v);
    }
}
impl<T:serde::Serialize> CanSample<T> for LoggedChallenger
where DuplexChallenger<BabyBear,Perm,16,8>:CanSample<T> {
    fn sample(&mut self)->T {
        let v:T=self.0.sample();
        bridge_events::emit("transcript_sample",serde_json::json!({"rust_type":core::any::type_name::<T>(),"value":&v}));
        v
    }
}
impl CanSampleBits<usize> for LoggedChallenger {
    fn sample_bits(&mut self,bits:usize)->usize {
        let raw:BabyBear=self.0.clone().sample();
        let result=self.0.sample_bits(bits);
        assert_eq!(result,(raw.as_canonical_u64() as usize)&((1usize<<bits)-1));
        bridge_events::emit("transcript_sample_bits",serde_json::json!({"bits":bits,"raw_base_word":raw.as_canonical_u64(),"index":result}));
        result
    }
}
impl FieldChallenger<BabyBear> for LoggedChallenger {}
impl GrindingChallenger for LoggedChallenger {
    type Witness=BabyBear;
    fn grind(&mut self,_bits:usize)->BabyBear {panic!("acceptance bridge is verification-only")}
}
