//! Public diagnostic for the fixed FFT plan cached by TFHE at this key's size.
use serde::Serialize;
use tfhe::boolean::prelude::ServerKey;
use tfhe::core_crypto::fft_impl::fft64::math::fft::Fft;

#[derive(Serialize)]
pub struct PlanObservation {
    pub source_feature: &'static str,
    pub polynomial_size: usize,
    pub fourier_size: usize,
    pub actual_plan_debug: String,
    pub expected_plan_matched: bool,
    pub observation_method: &'static str,
}

pub fn observe_and_restore(key: ServerKey) -> Result<(ServerKey, PlanObservation), String> {
    // Public key decomposition moves the same owned buffers, without modification.
    let (bootstrapping_key, key_switching_key, order) = key.into_raw_parts();
    let size = bootstrapping_key.polynomial_size();
    let key = ServerKey::from_raw_parts(bootstrapping_key, key_switching_key, order);
    let fft = Fft::new(size);
    // FftView's public Debug includes public twiddles as well as Plan's compact
    // Debug. Retain only that actual cached Plan record, never key contents.
    let debug = format!("{:?}", fft.as_view());
    let begin = debug
        .find("Plan {")
        .ok_or("TFHE Debug did not expose Plan record")?;
    let length = debug[begin..]
        .find('}')
        .ok_or("unterminated Plan Debug record")?
        + 1;
    let observed = debug[begin..begin + length].to_owned();
    let fourier_size = size.to_fourier_polynomial_size().0;
    let expected =
        format!("Plan {{ base_algo: Dif4, base_size: {fourier_size}, fft_size: {fourier_size} }}");
    if observed != expected {
        return Err(format!("fixed FFT plan mismatch: {observed}"));
    }
    Ok((key, PlanObservation {
        source_feature: "experimental-force_fft_algo_dif4",
        polynomial_size: size.0,
        fourier_size,
        actual_plan_debug: observed,
        expected_plan_matched: true,
        observation_method: "public FftView Debug from Fft::new at the actual public server-key polynomial size; same process-global cache used by Boolean bootstrap",
    }))
}
