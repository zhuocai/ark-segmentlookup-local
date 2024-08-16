use crate::domain::roots_of_unity;
use crate::error::Error;
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, PrimeField};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain, UVPolynomial};
use ark_std::One;
use std::iter;
use std::ops::{Div, Mul};

pub(crate) fn lagrange_basis<E: PairingEngine>(
    domain: &Radix2EvaluationDomain<E::Fr>,
) -> Vec<DensePolynomial<E::Fr>> {
    let vanishing_poly: DensePolynomial<E::Fr> = domain.vanishing_polynomial().into();
    let roots_of_unity = roots_of_unity::<E>(&domain);
    let roots_of_unity_div_domain_size: Vec<E::Fr> = roots_of_unity
        .iter()
        .map(|&root| root / domain.size_as_field_element())
        .collect();
    let mut lagrange_basis: Vec<DensePolynomial<E::Fr>> = Vec::with_capacity(domain.size());
    for i in 0..domain.size() {
        let mut poly_base: DensePolynomial<E::Fr> =
            vanishing_poly.div(&DensePolynomial::from_coefficients_vec(vec![
                -roots_of_unity[i],
                E::Fr::one(),
            ]));
        poly_base = poly_base.mul(&DensePolynomial::from_coefficients_vec(vec![
            roots_of_unity_div_domain_size[i],
        ]));
        lagrange_basis.push(poly_base);
    }
    lagrange_basis
}

// Efficiently compute the commitments to the Lagrange basis using SRS in O(n log n) time.
// Section 3.3 from the paper BGG17: https://eprint.iacr.org/2017/602.
pub(crate) fn lagrange_basis_g1<C: AffineCurve>(
    srs: &[C],
    domain: &Radix2EvaluationDomain<C::ScalarField>,
) -> Vec<C> {
    let group_order = domain.size();
    assert!(srs.len() >= group_order);
    assert!(group_order.is_power_of_two());

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
pub(crate) fn zero_opening_proofs<E: PairingEngine>(
    srs_g1: &[E::G1Affine],
    domain: &Radix2EvaluationDomain<E::Fr>,
    g1_lagrange_basis: &[E::G1Affine],
) -> Result<Vec<E::G1Affine>, Error> {
    let domain_size_inverse_fr = domain
        .size_as_field_element()
        .inverse()
        .ok_or(Error::FailedToInverseFieldElement)?;
    let rhs = srs_g1[domain.size() - 1].mul(-domain_size_inverse_fr);

    let domain_size = domain.size();
    let mut opening_proofs: Vec<E::G1Affine> = Vec::with_capacity(domain_size);
    for (i, com) in g1_lagrange_basis.iter().enumerate() {
        let lhs = com.mul(domain.element(domain_size - i));
        opening_proofs.push((lhs + rhs).into());
    }

    Ok(opening_proofs)
}

#[cfg(test)]
mod tests {
    use crate::kzg::{unsafe_setup_from_rng, Kzg};
    use ark_bn254::Bn254;
    use ark_std::rand::rngs::StdRng;
    use ark_std::{test_rng, Zero};

    use super::*;

    type Fr = <Bn254 as PairingEngine>::Fr;
    type G1Affine = <Bn254 as PairingEngine>::G1Affine;

    #[test]
    fn test_zero_opening_proofs() {
        let n = 32;
        let domain = Radix2EvaluationDomain::<Fr>::new(n).unwrap();
        let lagrange_basis = lagrange_basis::<Bn254>(&domain);

        let (srs_g1, _, _, _) =
            unsafe_setup_from_rng::<Bn254, StdRng>(n - 1, n, 0, &mut test_rng());
        let lagrange_basis_1: Vec<G1Affine> = lagrange_basis
            .iter()
            .map(|li| Kzg::<Bn254>::commit_g1(&srs_g1, li).into())
            .collect();

        let zero = Fr::zero();
        let li_proofs_slow: Vec<G1Affine> = lagrange_basis
            .iter()
            .map(|li| Kzg::<Bn254>::open_g1(&srs_g1, li, zero).1)
            .collect();

        let li_proofs_fast =
            zero_opening_proofs::<Bn254>(&srs_g1, &domain, &lagrange_basis_1).unwrap();

        assert_eq!(li_proofs_slow, li_proofs_fast);

        // Different domain size and SRS size.
        let (srs_g1, _, _, _) =
            unsafe_setup_from_rng::<Bn254, StdRng>(n + 100, n, 0, &mut test_rng());
        let li_proofs_fast =
            zero_opening_proofs::<Bn254>(&srs_g1, &domain, &lagrange_basis_1).unwrap();

        assert_eq!(li_proofs_slow, li_proofs_fast);
    }
}
