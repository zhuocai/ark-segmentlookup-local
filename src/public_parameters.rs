use std::cmp::max;
use std::ops::Mul;

use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{FftField, FftParameters, Field, PrimeField};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain, UVPolynomial};
use ark_poly::univariate::DensePolynomial;
use ark_std::{One, UniformRand, Zero};
use ark_std::rand::RngCore;
use ark_std::rand::rngs::StdRng;

use crate::error::Error;
use crate::kzg::{Kzg, unsafe_setup_from_tau};
use crate::lagrange_basis::{commitments, zero_opening_proofs};

#[derive(Debug)]
pub struct PublicParameters<E: PairingEngine> {
    // Number of total segments (n)
    pub(crate) num_segments: usize,
    // Number of queries (segments) in one witness. This is fixed for all queries (k)
    pub(crate) num_queries: usize,
    // Segment size (s)
    pub(crate) segment_size: usize,
    // Table size (n * s)
    pub(crate) table_size: usize,
    // Witness size (k * s)
    pub(crate) witness_size: usize,
    // [tau^i]_1 for i in 0..max*s
    pub(crate) srs_g1: Vec<E::G1Affine>,
    // [tau^i]_2 for i in 0..max*s
    pub(crate) srs_g2: Vec<E::G2Affine>,
    // [z_w(tau)]_2
    z_w_com2: E::G2Affine,
    pub(crate) domain_w: Radix2EvaluationDomain<E::Fr>,
    // [z_v(tau)]_2
    z_v_com2: E::G2Affine,
    pub(crate) domain_v: Radix2EvaluationDomain<E::Fr>,
    // [z_k(tau)]_2
    z_k_com2: E::G2Affine,
    pub(crate) domain_k: Radix2EvaluationDomain<E::Fr>,
    // q_{i, 2} for i in 1..n*s
    // The commitment of quotient polynomials Q_{i, 2} s.t.
    // L^W_i(X) * X = omega^i * L^W_i(X) + Z_W(X) * Q_{i, 2}(X)
    q_2_com1_list: Vec<E::G1Affine>,
    // q_{i, 3} for i in 1..n*s
    pub(crate) q_3_com1_list: Vec<E::G1Affine>,
    // q_{i, 4} for i in 1..n*s
    pub(crate) q_4_com1_list: Vec<E::G1Affine>,
    // [L^W_i(tau)]_1 for i in 1..n*s
    pub(crate) l_w_com1_list: Vec<E::G1Affine>,
    // [L^W_i(tau / w)]_1 for i in 1..n*s
    pub(crate) l_w_inv_w_com1_list: Vec<E::G1Affine>,
    // [(L^W_i(tau) - L^W_i(0)) / tau]_1 for i in 1..n*s
    l_w_zero_opening_proofs: Vec<E::G1Affine>,
    // [L^V_i(tau)]_1 for i in 1..k*s
    pub(crate) l_v_com1_list: Vec<E::G1Affine>,
    // [L^V_i(tau * v)]_1 for i in 1..k*s
    pub(crate) l_v_mul_v_com1_list: Vec<E::G1Affine>,
}

impl<E: PairingEngine> PublicParameters<E> {
    pub fn setup<R: RngCore>(
        rng: &mut R,
        num_segments: usize,
        num_queries: usize,
        segment_size: usize,
    ) -> Result<PublicParameters<E>, Error> {
        let table_size = num_segments * segment_size;
        let witness_size = num_queries * segment_size;

        // Step 1: Choose a random tau. Let max = max(k, n). Compute SRS from tau
        let tau = E::Fr::rand(rng);
        let max_power_of_tau = max(num_segments, num_queries) * segment_size - 1;
        let (srs_g1, srs_g2) = unsafe_setup_from_tau::<E, StdRng>(max_power_of_tau, max_power_of_tau + 1, tau);

        // Step 2: Compute [Z_W(tau)]_2
        let order_w = num_segments * segment_size;
        let domain_w: Radix2EvaluationDomain<E::Fr> = Radix2EvaluationDomain::<E::Fr>::new(order_w)
            .ok_or(Error::FailedToCreateEvaluationDomain)?;
        let z_w_com2 = vanishing_poly_com2::<E>(&srs_g2, &domain_w);

        // Step 2: Compute [Z_V(tau)]_2
        let order_v = num_queries * segment_size;
        let domain_v: Radix2EvaluationDomain<E::Fr> = Radix2EvaluationDomain::<E::Fr>::new(order_v)
            .ok_or(Error::FailedToCreateEvaluationDomain)?;
        let z_v_com2 = vanishing_poly_com2::<E>(&srs_g2, &domain_v);

        // Step 2: Compute [Z_K(tau)]_2
        // K = {v^{is}, i \in [0, k - 1]}
        let order_k = num_queries;
        let domain_k = create_domain_k_from_domain_v::<E>(&domain_v, order_k, segment_size)?;
        let z_k_com2 = vanishing_poly_com2::<E>(&srs_g2, &domain_k);


        // Step 4-a: Compute q_{i, 2} = [Q_{i,2}(tau)]_1 for i in 1..n*s
        // Q_{i,2}(X) = w^i / (ns)
        let roots_of_unity_w: Vec<E::Fr> = roots_of_unity::<E>(&domain_w);
        let quotient_values: Vec<E::Fr> = roots_of_unity_w
            .iter()
            .map(|&x| x / E::Fr::from(order_w as u64))
            .collect();
        let q_2_com1_list = quotient_values
            .iter()
            .map(|&x| srs_g1[0].clone().mul(x).into())
            .collect();


        // Step 4-b: Compute [L^W_i(tau)]_1 for i in 1..n*s
        let l_w_com1_list = commitments(&srs_g1, &domain_w);

        // Step 4-c: Compute [(L^W_i(tau) - L^W_i(0)) / tau]_1 for i in 1..n*s
        // a.k.a. zero openings of the Lagrange basis.
        let l_w_zero_opening_proofs = match
        zero_opening_proofs::<E>(
            &srs_g1,
            &domain_w,
            &l_w_com1_list,
        ) {
            Ok(proofs) => proofs,
            Err(e) => return Err(e),
        };

        // Step 5: Compute [L^V_i(tau)]_1 for i in 1..k*s
        let l_v_com1_list = commitments(&srs_g1, &domain_v);

        // Step 6: Compute [L^V_i(tau*v)]_1 for i in 1..k*s
        // L^V_i(X * v) = L^V_{i-1}(X).
        // We can shift [L^V_i(tau)]_1 to the right by 1 to get the result.
        let mut l_v_mul_v_com1_list: Vec<E::G1Affine> = Vec::with_capacity(order_v);
        if let Some(first) = l_v_com1_list.first().cloned() {
            l_v_com1_list.iter().skip(1).
                for_each(|com| l_v_mul_v_com1_list.push(com.clone()));
            l_v_mul_v_com1_list.push(first);
        } else {
            return Err(Error::InvalidLagrangeBasisCommitments("Lagrange basis commitments for V is empty".to_string()));
        }

        // Step 6: Compute quotient polynomial commitments q_{i, 3} and q_{i, 4} for i in 1..n*s
        // q_{i, 3} = [(w^i / ns) * (tau^n - w^{in}) / (tau - w)]_1
        let ns_inv_fr = domain_w.size_as_field_element().inverse().ok_or(Error::FailedToInverseFieldElement)?;
        let tau_minus_w_pow_i_inv_vec: Vec<E::Fr> = roots_of_unity_w.iter()
            .map(|x| (tau - x).inverse().unwrap_or_else(|| E::Fr::zero())).collect();
        let tau_pow_n_fr = tau.pow([num_segments as u64]);
        let tau_pow_n_minus_w_pow_in_vec: Vec<E::Fr> = (0..order_w)
            .map(|i| tau_pow_n_fr - roots_of_unity_w[i].pow([num_segments as u64]))
            .collect();
        let q_3_com1_list: Vec<E::G1Affine> = (0..order_w).map(|i| {
            let mut q3 = srs_g1[0].clone().mul(roots_of_unity_w[i]);
            q3 = q3.mul(ns_inv_fr.into_repr());
            q3 = q3.mul(tau_pow_n_minus_w_pow_in_vec[i].into_repr());
            q3 = q3.mul(tau_minus_w_pow_i_inv_vec[i].into_repr());

            q3.into_affine()
        }).collect();

        // Step 6: Compute quotient polynomial commitments q_{i, 4} for i in 1..n*s
        // Q_{i,4}(X) = Q_{i+1,3}(X) * (X^n - w^{in}) / (X^n - w^{(i+1)n})
        // q_{i, 4} = q_{i+1, 3} * (tau^n - w^{in}) / (tau^n - w^{(i+1)n})
        let tau_pow_n_minus_w_pow_in_inv_vec: Vec<E::Fr> = tau_pow_n_minus_w_pow_in_vec.iter()
            .map(|x| x.inverse().unwrap_or_else(|| E::Fr::zero())).collect();
        let q_4_com1_list = (0..order_w).map(|i| {
            let next_index = (i + 1) % order_w;
            let mut q4 = q_3_com1_list[next_index].into_projective();
            q4 = q4.mul(tau_pow_n_minus_w_pow_in_vec[i].into_repr());
            q4 = q4.mul(tau_pow_n_minus_w_pow_in_inv_vec[next_index].into_repr());

            q4.into_affine()
        }).collect();

        // Step 6-b: Compute [L^W_i(tau / w)]_1 for i in 1..n*s
        // L^W_i(tau / w) = L^W_{i+1}(tau) * w
        // We can shift [L^W_i(tau)]_1 to the left by 1 to get the result.
        let mut l_w_inv_w_com1_list: Vec<E::G1Affine> = Vec::with_capacity(order_w);
        if let Some(last) = l_w_com1_list.last().cloned() {
            l_w_com1_list.iter().skip(1).
                for_each(|com| l_w_inv_w_com1_list.push(com.clone()));
            l_w_inv_w_com1_list.push(last);
        } else {
            return Err(Error::InvalidLagrangeBasisCommitments("Lagrange basis commitments for W is empty".to_string()));
        }

        Ok(PublicParameters {
            num_segments,
            num_queries,
            segment_size,
            table_size,
            witness_size,
            srs_g1,
            srs_g2,
            z_w_com2,
            domain_w,
            z_v_com2,
            domain_v,
            z_k_com2,
            domain_k,
            q_2_com1_list,
            q_3_com1_list,
            q_4_com1_list,
            l_w_com1_list,
            l_w_inv_w_com1_list,
            l_w_zero_opening_proofs,
            l_v_com1_list,
            l_v_mul_v_com1_list,
        })
    }
}

fn vanishing_poly_com2<E: PairingEngine>(
    srs_g2: &[E::G2Affine],
    domain: &Radix2EvaluationDomain<E::Fr>,
) -> E::G2Affine {
    let vanishing_poly: DensePolynomial<E::Fr> = domain.vanishing_polynomial().into();

    Kzg::<E>::commit_g2(&srs_g2, &vanishing_poly).into_affine()
}

fn create_domain_k_from_domain_v<E: PairingEngine>(
    domain_v: &Radix2EvaluationDomain<E::Fr>,
    order_k: usize,
    segment_size: usize,
) -> Result<Radix2EvaluationDomain<E::Fr>, Error> {
    if !order_k.is_power_of_two() {
        return Err(Error::InvalidEvaluationDomainSize(order_k));
    }

    let size: u64 = order_k as u64;
    let log_size_of_group = size.trailing_zeros();
    if log_size_of_group > <E::Fr as FftField>::FftParams::TWO_ADICITY {
        return Err(Error::InvalidEvaluationDomainSize(order_k));
    }

    let roots_of_unity_v = roots_of_unity::<E>(&domain_v);
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

fn roots_of_unity<E: PairingEngine>(domain: &Radix2EvaluationDomain<E::Fr>) -> Vec<E::Fr> {
    let domain_elements: Vec<E::Fr> = domain.elements().collect();

    domain_elements
}


#[cfg(test)]
mod test {
    use ark_bn254::Bn254;
    use ark_ec::PairingEngine;
    use ark_ff::Field;
    use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
    use ark_std::{One, test_rng};
    use ark_std::rand::rngs::StdRng;

    use crate::public_parameters::{create_domain_k_from_domain_v, PublicParameters};

    #[test]
    fn test_public_parameters_setup() {
        let mut rng = test_rng();
        let pp = PublicParameters::<Bn254>::setup::<StdRng>(
            &mut rng,
            8, 4, 4,
        ).unwrap();
        println!("{:?}", pp);
    }

    #[test]
    fn test_domain_k() {
        let num_segments = 16;
        let num_queries = 8;
        let segment_size = 4;

        let order_v = num_queries * segment_size;
        let domain_v = Radix2EvaluationDomain::<<Bn254 as PairingEngine>::Fr>::new(order_v)
            .unwrap();
        let order_k = num_queries;
        let domain_k = create_domain_k_from_domain_v::<Bn254>(&domain_v, order_k, segment_size).unwrap();
        let group_gen_k = domain_k.group_gen;
        assert_eq!(group_gen_k.pow([domain_k.size]), <Bn254 as PairingEngine>::Fr::one());
    }
}