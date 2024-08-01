use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_ff::{FftField, FftParameters, Field};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_poly::univariate::DensePolynomial;

use crate::error::Error;
use crate::kzg::Kzg;

pub fn vanishing_poly_com2<E: PairingEngine>(
    srs_g2: &[E::G2Affine],
    domain: &Radix2EvaluationDomain<E::Fr>,
) -> E::G2Affine {
    let vanishing_poly: DensePolynomial<E::Fr> = domain.vanishing_polynomial().into();

    Kzg::<E>::commit_g2(&srs_g2, &vanishing_poly).into_affine()
}

pub fn create_domain_from_larger_domain<E: PairingEngine>(
    larger_domain: &Radix2EvaluationDomain<E::Fr>,
    order: usize,
    segment_size: usize,
) -> Result<Radix2EvaluationDomain<E::Fr>, Error> {
    if !order.is_power_of_two() {
        return Err(Error::InvalidEvaluationDomainSize(order));
    }

    let size: u64 = order as u64;
    let log_size_of_group = size.trailing_zeros();
    if log_size_of_group > <E::Fr as FftField>::FftParams::TWO_ADICITY {
        return Err(Error::InvalidEvaluationDomainSize(order));
    }

    let roots_of_unity_v = roots_of_unity::<E>(&larger_domain);
    let group_gen_k = roots_of_unity_v[segment_size];
    let size_as_field_element = E::Fr::from(size);
    let size_inv = size_as_field_element
        .inverse()
        .ok_or(Error::FailedToInverseFieldElement)?;

    let group_gen_inv = group_gen_k
        .inverse()
        .ok_or(Error::FailedToInverseFieldElement)?;

    let generator_inv = E::Fr::multiplicative_generator()
        .inverse()
        .ok_or(Error::FailedToInverseFieldElement)?;

    Ok(Radix2EvaluationDomain {
        size,
        log_size_of_group,
        size_as_field_element,
        size_inv,
        group_gen: group_gen_k,
        group_gen_inv,
        generator_inv,
    })
}

pub fn roots_of_unity<E: PairingEngine>(domain: &Radix2EvaluationDomain<E::Fr>) -> Vec<E::Fr> {
    let domain_elements: Vec<E::Fr> = domain.elements().collect();

    domain_elements
}

#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;
    use ark_std::One;

    use super::*;

    #[test]
    fn test_create_domain_from_large_domain() {
        let num_segments = 16;
        let num_queries = 8;
        let segment_size = 4;

        let order_v = num_queries * segment_size;
        let domain_v = Radix2EvaluationDomain::<<Bn254 as PairingEngine>::Fr>::new(order_v)
            .unwrap();
        let order_k = num_queries;
        let domain_k = create_domain_from_larger_domain::<Bn254>(&domain_v, order_k, segment_size).unwrap();
        let group_gen_k = domain_k.group_gen;
        assert_eq!(group_gen_k.pow([domain_k.size]), <Bn254 as PairingEngine>::Fr::one());
    }
}