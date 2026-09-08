use super::*;
use crate::{
    arith::field::{Field64, Field64_2},
    protocol::{utils::sum_over_boolean_hypercube, verifier::Verifier},
};
use ark_ff::AdditiveGroup;
use std::{hint::black_box, time::Instant};

type B = Field64;
type E = Field64_2;

fn extension(a: u64, b: u64) -> E {
    E::new(B::from(a), B::from(b))
}

// All data are deterministic public field elements, with distinct row,
// component and coefficient patterns. No encryption or secret key is needed.
fn fixture<const D: usize>() -> (Matrix<B>, Vec<RLWE<CyclotomicRing<D, B>>>) {
    let matrix = Matrix::from_vec(
        (0..4 * 2 * D)
            .map(|t| B::from((3 + 17 * (t / D) + t * t) as u64))
            .collect(),
        2 * D,
    );
    let x = (0..2)
        .map(|j| {
            RLWE::from_ring_elements(
                (0..2)
                    .map(|k| {
                        CyclotomicRing::from_coeffs(
                            &(0..D)
                                .map(|t| B::from((5 + j * 11 + k * 13 + t * t * t) as u64))
                                .collect::<Vec<_>>(),
                        )
                    })
                    .collect(),
            )
        })
        .collect();
    (matrix, x)
}

fn powers<const D: usize>(alpha: E) -> Vec<E> {
    (0..D)
        .scan(E::ONE, |a, _| {
            let out = *a;
            *a *= alpha;
            Some(out)
        })
        .collect()
}

#[test]
fn contracts_actual_fused_tensors_into_existing_sumchecks() {
    const D: usize = 32;
    let (matrix, x) = fixture::<D>();
    let (m, cache, m_mle, _, nv, _) = Prover::<D, E>::preprocess(&matrix);
    let (y, q) = cache.evaluate(&x);
    let (r0, r1) = compute_r_bpf_mle_evals::<D, E>(&q);
    let beta0 = extension(7, 11);
    let beta = vec![beta0, beta0 * beta0];
    let tau = vec![extension(3, 5), extension(13, 17)];
    let mut rows = vec![];
    build_eq_poly(&tau, &mut rows);

    for alpha in [E::ZERO, E::ONE, -E::ONE, extension(19, 23)] {
        let powers = powers::<D>(alpha);
        let z1 = compute_z1_mles(&m, &m_mle, &x, nv, &beta, &powers, &tau);
        let z3 = compute_z3_mles::<D, E>(&powers, &r0, &r1, &beta, nv - 1, &tau);
        let (ye, qe) = contract_remainder_quotient::<D, E>(&y, &q, &powers, &rows, &beta);
        let claims = [ye + (alpha * powers[D - 1] + E::ONE) * qe, qe];
        for (mles, claim, vars) in [(z1, claims[0], nv), (z3, claims[1], nv - 1)] {
            let old_claim = sum_over_boolean_hypercube(&mles);
            assert_eq!(claim, old_claim);
            let degree = mles.len();
            let mut old_tables = mles.clone();
            let mut new_tables = mles.clone();
            let mut old_t = Blake3Transcript::new();
            let mut new_t = old_t.clone();
            let (old_proof, old_challenges) = prove(old_claim, &mut old_tables, vars, &mut old_t);
            let (new_proof, new_challenges) = prove(claim, &mut new_tables, vars, &mut new_t);
            assert_eq!(old_challenges, new_challenges);
            assert_eq!(old_t.squeeze(2), new_t.squeeze(2));
            let old_result = old_proof.verify(vars, degree, &mut Blake3Transcript::new());
            let new_result = new_proof.verify(vars, degree, &mut Blake3Transcript::new());
            assert!(old_result.is_ok());
            assert_eq!(old_result, new_result);
            let terminal = new_tables.iter().map(|p| p.evals()[0]).product::<E>();
            assert_eq!(terminal, new_result.unwrap().1);
        }
    }

    // Concrete controls: the helper cannot silently swap rows/components,
    // drop the quotient factor, or hide a modified committed coefficient.
    let alpha = extension(19, 23);
    let powers = powers::<D>(alpha);
    let (ye, qe) = contract_remainder_quotient::<D, E>(&y, &q, &powers, &rows, &beta);
    let total = ye + (alpha * powers[D - 1] + E::ONE) * qe;
    assert_ne!(qe, E::ZERO);
    assert_ne!(total, ye);
    let mut wrong_rows = rows.clone();
    wrong_rows.swap(0, 1);
    assert_ne!(
        contract_remainder_quotient::<D, E>(&y, &q, &powers, &wrong_rows, &beta),
        (ye, qe)
    );
    let mut wrong_beta = beta.clone();
    wrong_beta.swap(0, 1);
    assert_ne!(
        contract_remainder_quotient::<D, E>(&y, &q, &powers, &rows, &wrong_beta),
        (ye, qe)
    );
    let mut corrupted_q = q.clone();
    corrupted_q[0][1].coeffs[0] += B::ONE;
    let (_, bad_qe) = contract_remainder_quotient::<D, E>(&y, &corrupted_q, &powers, &rows, &beta);
    assert_ne!(bad_qe, qe);
    let mut z3 = compute_z3_mles::<D, E>(&powers, &r0, &r1, &beta, nv - 1, &tau);
    let (bad_proof, _) = prove(bad_qe, &mut z3, nv - 1, &mut Blake3Transcript::new());
    assert_eq!(
        bad_proof.verify(nv - 1, 3, &mut Blake3Transcript::new()),
        Err(0)
    );
}

#[test]
#[should_panic(expected = "assertion `left == right` failed")]
fn rejects_truncated_committed_quotient_shape() {
    let (matrix, x) = fixture::<32>();
    let (m, _, _, _, _, _) = Prover::<32, E>::preprocess(&matrix);
    let (y, mut q) = FusedMatvec::new(&m).evaluate(&x);
    q[0][0].coeffs.pop();
    contract_remainder_quotient::<32, E>(
        &y,
        &q,
        &vec![E::ONE; 32],
        &vec![E::ONE; 4],
        &vec![E::ONE; 2],
    );
}

// One consumer workload, invoked explicitly in release mode. The scan timings
// exclude shared table construction (the tables are still used by sumcheck).
#[test]
#[ignore = "explicit public release workload with PCS enabled"]
fn ring_claim_workload_and_real_pcs_consumer() {
    const D: usize = 1024;
    let (matrix, x) = fixture::<D>();
    let (m, cache, mle, base_mle, nv, mut transcript) = Prover::<D, E>::preprocess(&matrix);
    let (y, q) = cache.evaluate(&x);
    let (r0, r1) = compute_r_bpf_mle_evals::<D, E>(&q);
    let alpha = extension(19, 23);
    let beta0 = extension(7, 11);
    let beta = vec![beta0, beta0 * beta0];
    let tau = vec![extension(3, 5), extension(13, 17)];
    let powers = powers::<D>(alpha);
    let z1 = compute_z1_mles(&m, &mle, &x, nv, &beta, &powers, &tau);
    let z3 = compute_z3_mles::<D, E>(&powers, &r0, &r1, &beta, nv - 1, &tau);
    let old = || {
        (
            sum_over_boolean_hypercube(black_box(&z1)),
            sum_over_boolean_hypercube(black_box(&z3)),
        )
    };
    let new = || {
        let mut rows = Vec::with_capacity(y.len());
        build_eq_poly(black_box(&tau), &mut rows);
        let (ye, qe) =
            contract_remainder_quotient::<D, E>(black_box(&y), &q, &powers, &rows, &beta);
        (ye + (alpha * powers[D - 1] + E::ONE) * qe, qe)
    };
    assert_eq!(old(), new());
    for _ in 0..4 {
        black_box(old());
        black_box(new());
    }
    let mut samples = vec![];
    for sample in 0..9 {
        let time = |f: &dyn Fn() -> (E, E)| {
            let start = Instant::now();
            for _ in 0..32 {
                black_box(f());
            }
            start.elapsed().as_nanos() / 32
        };
        let (old_ns, new_ns) = if sample % 2 == 0 {
            (time(&old), time(&new))
        } else {
            let new_ns = time(&new);
            (time(&old), new_ns)
        };
        samples.push((old_ns, new_ns));
        println!(
            "{{\"phase\":\"claim_totals\",\"sample\":{sample},\"old_ns\":{old_ns},\"new_ns\":{new_ns}}}"
        );
    }
    let mut old_ns: Vec<_> = samples.iter().map(|x| x.0).collect();
    let mut new_ns: Vec<_> = samples.iter().map(|x| x.1).collect();
    old_ns.sort();
    new_ns.sort();
    println!(
        "{{\"phase\":\"claim_medians\",\"ring_degree\":{D},\"rows\":4,\"inner\":2,\"components\":2,\"old_ns\":{},\"new_ns\":{}}}",
        old_ns[4], new_ns[4]
    );

    // This calls the modified production method; all three existing PCS
    // openings remain enabled and the unchanged public verifier consumes it.
    let start = Instant::now();
    let proof = Prover::<D, E>::prove(&m, &cache, &mle, &base_mle, nv, &mut transcript, &x, true);
    let prove_ns = start.elapsed().as_nanos();
    assert!(
        proof.r0_mle_proof.is_some() && proof.r1_mle_proof.is_some() && proof.m_mle_proof.is_some()
    );
    let (vm, vnv, mut vt) = Verifier::<D, E>::preprocess(&matrix);
    let verify_start = Instant::now();
    assert!(Verifier::<D, E>::verify(&vm, vnv, &mut vt, &x, &proof).is_ok());
    let verify_ns = verify_start.elapsed().as_nanos();
    for (actual, expected) in proof.y.iter().zip(&y) {
        for k in 0..2 {
            assert_eq!(
                actual.get_ring_element(k).unwrap().coeffs,
                expected.get_ring_element(k).unwrap().coeffs
            );
        }
    }
    let mut wrong = proof.clone();
    let mut row: Vec<_> = wrong.y[0].get_ring_elements().into_iter().cloned().collect();
    row[0].coeffs[0] += B::ONE;
    wrong.y[0] = RLWE::from_ring_elements(row);
    let (_, _, mut wt) = Verifier::<D, E>::preprocess(&matrix);
    // The existing verifier uses unwrap/assert at several refusal points.
    // Count either Err or its existing panic as refusal, not a clean-error API.
    let refusal = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        Verifier::<D, E>::verify(&vm, vnv, &mut wt, &x, &wrong)
    }));
    assert!(!matches!(refusal, Ok(Ok(_))));
    println!(
        "{{\"phase\":\"actual_consumer\",\"pcs_enabled\":true,\"verifier_accepted\":true,\"modified_output_refused\":true,\"output_coefficients_matched\":8192,\"prove_ns\":{prove_ns},\"verify_ns\":{verify_ns}}}"
    );
}
