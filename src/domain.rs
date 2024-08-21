use crate::error::Error;
use crate::kzg::Kzg;
use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_ff::{FftField, FftParameters, Field};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, Evaluations, Radix2EvaluationDomain};
use ark_std::{One, Zero};

pub(crate) fn vanishing_poly_g2<E: PairingEngine>(
    g2_srs: &[E::G2Affine],
    domain: &Radix2EvaluationDomain<E::Fr>,
) -> E::G2Affine {
    let vanishing_poly: DensePolynomial<E::Fr> = domain.vanishing_polynomial().into();

    Kzg::<E>::commit_g2(&g2_srs, &vanishing_poly).into_affine()
}

pub(crate) fn create_sub_domain<E: PairingEngine>(
    original_domain: &Radix2EvaluationDomain<E::Fr>,
    order: usize,
    segment_size: usize,
) -> Result<Radix2EvaluationDomain<E::Fr>, Error> {
    if segment_size == 0 {
        return Err(Error::InvalidSegmentSize(segment_size));
    }
    if segment_size == 1 {
        return Ok(original_domain.clone());
    }
    if !order.is_power_of_two() {
        return Err(Error::InvalidEvaluationDomainSize(order));
    }
    let original_order = original_domain.size();
    if segment_size > original_order {
        return Err(Error::InvalidSegmentSize(segment_size));
    }
    if segment_size == original_order {
        let domain_1 = Radix2EvaluationDomain::<<E as PairingEngine>::Fr>::new(1)
            .ok_or(Error::FailedToCreateEvaluationDomain)?;
        return Ok(domain_1);
    }

    let size: u64 = order as u64;
    let log_size_of_group = order.trailing_zeros();
    if log_size_of_group > <E::Fr as FftField>::FftParams::TWO_ADICITY {
        return Err(Error::InvalidEvaluationDomainSize(order));
    }

    let roots_of_unity_larger_domain = roots_of_unity::<E>(&original_domain);
    let group_gen = roots_of_unity_larger_domain[segment_size];
    let size_as_field_element = E::Fr::from(size);
    let size_inv = size_as_field_element
        .inverse()
        .ok_or(Error::FailedToInverseFieldElement)?;

    let group_gen_inv = group_gen
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
        group_gen,
        group_gen_inv,
        generator_inv,
    })
}

pub(crate) fn roots_of_unity<E: PairingEngine>(
    domain: &Radix2EvaluationDomain<E::Fr>,
) -> Vec<E::Fr> {
    domain.elements().collect()
}

pub(crate) fn identity_poly<E: PairingEngine>(
    domain: &Radix2EvaluationDomain<E::Fr>,
) -> DensePolynomial<E::Fr> {
    let id_list = vec![E::Fr::one(); domain.size()];

    Evaluations::from_vec_and_domain(id_list, *domain).interpolate()
}

pub(crate) fn divide_by_vanishing_poly_checked<E: PairingEngine>(
    domain: &Radix2EvaluationDomain<E::Fr>,
    poly: &DensePolynomial<E::Fr>,
) -> Result<DensePolynomial<E::Fr>, Error> {
    let (quotient, remainder) = poly
        .divide_by_vanishing_poly(*domain)
        .ok_or(Error::FailedToDivideByVanishingPolynomial)?;

    if !remainder.is_zero() {
        return Err(Error::RemainderAfterDivisionIsNonZero);
    }

    Ok(quotient)
}

#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;

    use super::*;

    #[test]
    fn test_create_domain_from_large_domain() {
        let num_queries = 8;
        let segment_size = 4;

        let order_v = num_queries * segment_size;
        let domain_v =
            Radix2EvaluationDomain::<<Bn254 as PairingEngine>::Fr>::new(order_v).unwrap();
        let order_k = num_queries;
        let domain_k = create_sub_domain::<Bn254>(&domain_v, order_k, segment_size).unwrap();
        let group_gen_k = domain_k.group_gen;
        assert_eq!(
            group_gen_k.pow([domain_k.size]),
            <Bn254 as PairingEngine>::Fr::one()
        );
    }
}
