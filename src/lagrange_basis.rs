use std::iter;

use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, PrimeField};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};

use crate::error::Error;

// Efficiently compute the commitments to the Lagrange basis using SRS in O(n log n) time.
// Section 3.3 from the paper BGG17: https://eprint.iacr.org/2017/602.
pub fn commitments<C: AffineCurve>(srs: &[C], domain: &GeneralEvaluationDomain<C::ScalarField>) -> Vec<C> {
    let group_order = domain.size();
    assert!(srs.len() >= group_order);
    assert!(is_pow_2(group_order));

    let n_inv = domain
        .size_as_field_element()
        .inverse()
        .unwrap()
        .into_repr();

    let srs_subset: Vec<C> = srs.iter().take(group_order).cloned().collect();
    let tau_projective: Vec<C::Projective> = srs_subset
        .iter()
        .map(|tau_pow_i| tau_pow_i.into_projective())
        .collect();
    let p_eval_vec: Vec<C::Projective> = domain.fft(&tau_projective);
    let p_eval_reversed_vec = iter::once(p_eval_vec[0]).chain(p_eval_vec.into_iter().skip(1).rev());

    let mut ls: Vec<C::Projective> = p_eval_reversed_vec
        .into_iter()
        .map(|pi| pi.mul(n_inv))
        .collect();
    C::Projective::batch_normalization(&mut ls);

    ls.iter().map(|li| li.into_affine()).collect()
}

// See Page 12 of CQ paper for efficient computation.
pub fn zero_opening_proofs<E: PairingEngine>(
    srs_g1: &[E::G1Affine],
    domain: &GeneralEvaluationDomain<E::Fr>,
    lagrange_basis_w_com1_vec: &[E::G1Affine],
) -> Result<Vec<E::G1Affine>, Error> {
    let domain_size_inverse_fr = domain
        .size_as_field_element()
        .inverse()
        .ok_or(Error::FailedToInverseFieldElement)?;
    let rhs = srs_g1.last()
        .ok_or(Error::InvalidStructuredReferenceStrings)?
        .mul(-domain_size_inverse_fr);

    let domain_size = domain.size();
    let mut opening_proofs: Vec<E::G1Affine> = Vec::with_capacity(domain_size);
    for (i, com) in lagrange_basis_w_com1_vec.iter().enumerate() {
        let lhs = com.mul(domain.element(domain_size - i));
        opening_proofs.push((lhs + rhs).into());
    }

    Ok(opening_proofs)
}

fn is_pow_2(x: usize) -> bool {
    (x & (x - 1)) == 0
}