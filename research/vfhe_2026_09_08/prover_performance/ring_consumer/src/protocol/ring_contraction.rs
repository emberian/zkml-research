//! Shared-point evaluation of the actual quotient and remainder vectors.
//! This is prover arithmetic; commitments and the sumcheck verifier are unchanged.
use crate::{
    arith::{cyclotomic_ring::CyclotomicRing, polynomial_ring::PolynomialRing},
    rlwe::RLWE,
};
use ark_ff::Field;

/// Evaluate both row/component/coefficient tensors with the same outer weights.
/// `powers[t] = alpha^t`; `row_weights` uses the caller's existing eq convention.
/// Component weights are in RLWE order: mask components, then body.
///
/// The quotient representation has 2D storage; its existing committed MLE uses
/// the low D coefficients, which this helper consumes in the identical order.
/// Nothing constructs a second field-sized MLE table or recomputes a basis per
/// coefficient. Multiplying by component and row weights after each dot product
/// is distributivity in the existing field.
pub(crate) fn contract_remainder_quotient<const D: usize, F: Field>(
    y: &[RLWE<CyclotomicRing<D, F::BasePrimeField>>],
    q: &[Vec<PolynomialRing<D, F::BasePrimeField>>],
    powers: &[F],
    row_weights: &[F],
    component_weights: &[F],
) -> (F, F) {
    assert!(D > 0);
    assert_eq!(powers.len(), D);
    assert_eq!(y.len(), q.len());
    assert_eq!(y.len(), row_weights.len());
    let (mut y_eval, mut q_eval) = (F::ZERO, F::ZERO);
    for ((yi, qi), &row_weight) in y.iter().zip(q).zip(row_weights) {
        assert_eq!(yi.rank() + 1, component_weights.len());
        assert_eq!(qi.len(), component_weights.len());
        let (mut row_y, mut row_q) = (F::ZERO, F::ZERO);
        for (k, &beta) in component_weights.iter().enumerate() {
            let yk = yi.get_ring_element(k).expect("validated component shape");
            assert_eq!(yk.coeffs.len(), D);
            assert_eq!(qi[k].coeffs.len(), 2 * D);
            let (mut component_y, mut component_q) = (F::ZERO, F::ZERO);
            for (t, power) in powers.iter().enumerate() {
                component_y += power.mul_by_base_prime_field(&yk.coeffs[t]);
                component_q += power.mul_by_base_prime_field(&qi[k].coeffs[t]);
            }
            row_y += beta * component_y;
            row_q += beta * component_q;
        }
        y_eval += row_weight * row_y;
        q_eval += row_weight * row_q;
    }
    (y_eval, q_eval)
}
