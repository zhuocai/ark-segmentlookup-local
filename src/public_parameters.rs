use std::cmp::max;

use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, PrimeField};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain};
use ark_poly::univariate::DensePolynomial;
use ark_std::{UniformRand, Zero};
use ark_std::rand::RngCore;
use ark_std::rand::rngs::StdRng;
use fk::UpperToeplitz;

use crate::error::Error;
use crate::kzg::{Kzg, unsafe_setup_from_tau};
use crate::lagrange_basis::{commitments, zero_opening_proofs};

#[derive(Debug)]
pub struct PublicParameters<E: PairingEngine> {
    // Number of total segments (n)
    num_segments: usize,
    // Number of segments in one query. This is fixed for all queries (k)
    num_queries: usize,
    // Segment size (s)
    segment_size: usize,
    // Table size (n * s)
    table_size: usize,
    // [tau^i]_1 for i in 0..max*s
    srs_g1: Vec<E::G1Affine>,
    // [tau^i]_2 for i in 0..max*s
    srs_g2: Vec<E::G2Affine>,
    // [z_w(tau)]_2
    z_w_com2: E::G2Affine,
    // [z_v(tau)]_2
    z_v_com2: E::G2Affine,
    // [z_k(tau)]_2
    z_k_com2: E::G2Affine,

    // // [t(tau)]_2
    // t_com2: Vec<E::G2Affine>,
    // // q_{i, 1} for i in 1..n*s
    // quotient_poly_com1_set_1: Vec<E::G1Affine>,

    // q_{i, 2} for i in 1..n*s
    // The commitment of quotient polynomials Q_{i, 2} s.t.
    // L^W_i(X) * X = omega^i * L^W_i(X) + Z_W(X) * Q_{i, 2}(X)
    quotient_poly_com1_vec_2: Vec<E::G1Affine>,
    // q_{i, 3} for i in 1..n*s
    quotient_poly_com1_vec_3: Vec<E::G1Affine>,
    // q_{i, 4} for i in 1..n*s
    quotient_poly_com1_vec_4: Vec<E::G1Affine>,
    // [L^W_i(tau)]_1 for i in 1..n*s
    lagrange_basis_w_com1_vec: Vec<E::G1Affine>,
    // [L^W_i(tau / w)]_1 for i in 1..n*s
    lagrange_basis_w_inv_com1_vec: Vec<E::G1Affine>,
    // [(L^W_i(tau) - L^W_i(0)) / tau]_1 for i in 1..n*s
    lagrange_basis_w_zero_opening_proofs: Vec<E::G1Affine>,
    // [L^V_i(tau)]_1 for i in 1..k*s
    lagrange_basis_v_com1_vec: Vec<E::G1Affine>,
    // [L^V_i(tau * v)]_1 for i in 1..k*s
    lagrange_basis_v_mul_com1_vec: Vec<E::G1Affine>,
}

impl<E: PairingEngine> PublicParameters<E> {
    pub fn new<R: RngCore>(
        rng: &mut R,
        num_segments: usize,
        num_queries: usize,
        segment_size: usize,
    ) -> Result<PublicParameters<E>, Error> {
        let table_size = num_segments * segment_size;

        // Step 1: Choose a random tau. Let max = max(k, n). Compute SRS from tau
        let tau = E::Fr::rand(rng);
        let max_power_of_tau = max(num_segments, num_queries) * segment_size - 1;
        let (srs_g1, srs_g2) = unsafe_setup_from_tau::<E, StdRng>(max_power_of_tau, max_power_of_tau + 1, tau);

        // Step 2: Compute [Z_W(tau)]_2
        let order_w = num_segments * segment_size;
        let domain_w: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::<E::Fr>::new(order_w)
            .ok_or(Error::FailedToCreateGeneralEvaluationDomain)?;
        let z_w_com2 = vanishing_poly_com2::<E>(&srs_g2, &domain_w);

        // Step 2: Compute [Z_V(tau)]_2
        let order_v = num_queries * segment_size;
        let domain_v: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::<E::Fr>::new(order_v)
            .ok_or(Error::FailedToCreateGeneralEvaluationDomain)?;
        let z_v_com2 = vanishing_poly_com2::<E>(&srs_g2, &domain_v);

        // Step 2: Compute [Z_K(tau)]_2
        let order_k = num_queries;
        let domain_k: GeneralEvaluationDomain<E::Fr> = GeneralEvaluationDomain::<E::Fr>::new(order_k)
            .ok_or(Error::FailedToCreateGeneralEvaluationDomain)?;
        let z_k_com2 = vanishing_poly_com2::<E>(&srs_g2, &domain_k);

        // Step 4-a: Compute q_{i, 2} = [Q_{i,2}(tau)]_1 for i in 1..n*s
        // Q_{i,2}(X) = w^i / (ns)
        let roots_of_unity_w: Vec<E::Fr> = roots_of_unity::<E>(&domain_w);
        let quotient_values: Vec<E::Fr> = roots_of_unity_w
            .iter()
            .map(|&x| x / E::Fr::from(order_w as u64))
            .collect();
        let quotient_poly_com1_vec_2 = quotient_values
            .iter()
            .map(|&x| srs_g1[0].clone().mul(x).into())
            .collect();


        // Step 4-b: Compute [L^W_i(tau)]_1 for i in 1..n*s
        let lagrange_basis_w_com1_vec = commitments(&srs_g1, &domain_w);

        // Step 4-c: Compute [(L^W_i(tau) - L^W_i(0)) / tau]_1 for i in 1..n*s
        // a.k.a. zero openings of the Lagrange basis.
        let lagrange_basis_w_zero_opening_proofs = match
        zero_opening_proofs::<E>(
            &srs_g1,
            &domain_w,
            &lagrange_basis_w_com1_vec,
        ) {
            Ok(proofs) => proofs,
            Err(e) => return Err(e),
        };

        // Step 5: Compute [L^V_i(tau)]_1 for i in 1..k*s
        let lagrange_basis_v_com1_vec = commitments(&srs_g1, &domain_v);

        // Step 6: Compute [L^V_i(tau*v)]_1 for i in 1..k*s
        // L^V_i(X * v) = L^V_{i-1}(X).
        // We can shift [L^V_i(tau)]_1 to the right by 1 to get the result.
        let mut lagrange_basis_v_mul_com1_vec: Vec<E::G1Affine> = Vec::with_capacity(order_v);
        if let Some(first) = lagrange_basis_v_com1_vec.first().cloned() {
            lagrange_basis_v_com1_vec.iter().skip(1).
                for_each(|com| lagrange_basis_v_mul_com1_vec.push(com.clone()));
            lagrange_basis_v_mul_com1_vec.push(first);
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
        let quotient_poly_com1_vec_3: Vec<E::G1Affine> = (0..order_w).map(|i| {
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
        let quotient_poly_com1_vec_4 = (0..order_w).map(|i| {
            let next_index = (i + 1) % order_w;
            let mut q4 = quotient_poly_com1_vec_3[next_index].into_projective();
            q4 = q4.mul(tau_pow_n_minus_w_pow_in_vec[i].into_repr());
            q4 = q4.mul(tau_pow_n_minus_w_pow_in_inv_vec[next_index].into_repr());

            q4.into_affine()
        }).collect();

        // Step 6-b: Compute [L^W_i(tau / w)]_1 for i in 1..n*s
        // L^W_i(tau / w) = L^W_{i+1}(tau) * w
        // We can shift [L^W_i(tau)]_1 to the left by 1 to get the result.
        let mut lagrange_basis_w_inv_com1_vec: Vec<E::G1Affine> = Vec::with_capacity(order_w);
        if let Some(last) = lagrange_basis_w_com1_vec.last().cloned() {
            lagrange_basis_w_com1_vec.iter().skip(1).
                for_each(|com| lagrange_basis_w_inv_com1_vec.push(com.clone()));
            lagrange_basis_w_inv_com1_vec.push(last);
        } else {
            return Err(Error::InvalidLagrangeBasisCommitments("Lagrange basis commitments for W is empty".to_string()));
        }

        Ok(PublicParameters {
            num_segments,
            num_queries,
            segment_size,
            table_size,
            srs_g1,
            srs_g2,
            z_w_com2,
            z_v_com2,
            z_k_com2,
            quotient_poly_com1_vec_2,
            quotient_poly_com1_vec_3,
            quotient_poly_com1_vec_4,
            lagrange_basis_w_com1_vec,
            lagrange_basis_w_inv_com1_vec,
            lagrange_basis_w_zero_opening_proofs,
            lagrange_basis_v_com1_vec,
            lagrange_basis_v_mul_com1_vec,
        })
    }
}

fn vanishing_poly_com2<E: PairingEngine>(
    srs_g2: &[E::G2Affine],
    domain: &GeneralEvaluationDomain<E::Fr>,
) -> E::G2Affine {
    let vanishing_poly: DensePolynomial<E::Fr> = domain.vanishing_polynomial().into();

    Kzg::<E>::commit_g2(&srs_g2, &vanishing_poly).into_affine()
}

fn roots_of_unity<E: PairingEngine>(domain: &GeneralEvaluationDomain<E::Fr>) -> Vec<E::Fr> {
    let domain_elements: Vec<E::Fr> = domain.elements().collect();

    domain_elements
}


fn compute_quotients<E: PairingEngine>(
    t: &DensePolynomial<E::Fr>,
    domain: &GeneralEvaluationDomain<E::Fr>,
    srs_g1: &[E::G1Affine],
) -> Result<Vec<E::G1Affine>, Error> {
    /*
        - N (table size) is always pow2
        - Toeplitz multiplication will happen in 2 * N, so appending zero commitments on hs is not needed
    */
    let toeplitz = UpperToeplitz::from_poly(t);

    let mut srs_proj: Vec<E::G1Projective> = srs_g1.iter().map(|t| t.into_projective()).collect();
    srs_proj.reverse();

    let h_commitments: Vec<E::G1Projective> = toeplitz.mul_by_vec(&srs_proj);
    if h_commitments.len() != 2 * domain.size() {
        return Err(Error::InvalidCommitmentLength(format!(
            "Expected h_commitments length to be {}, but was {}",
            2 * domain.size(),
            h_commitments.len()
        )));
    }

    let ks: Vec<_> = domain.fft(&h_commitments[..domain.size()]);

    let n_inv = domain.size_as_field_element()
        .inverse()
        .ok_or(Error::FailedToInverseFieldElement)?;
    let normalized_roots: Vec<E::Fr> = domain.elements().map(|g_i| g_i * n_inv).collect();

    let mut qs: Vec<E::G1Projective> = ks
        .iter()
        .zip(normalized_roots)
        .map(|(ki, normalizer_i)| ki.mul(normalizer_i.into_repr()))
        .collect();

    E::G1Projective::batch_normalization(&mut qs);

    Ok(qs.iter().map(|qi| qi.into_affine()).collect())
}

#[cfg(test)]
mod test {
    use ark_bn254::Bn254;
    use ark_std::rand::rngs::StdRng;
    use ark_std::test_rng;

    use crate::public_parameters::PublicParameters;

    #[test]
    fn test_public_parameters_new() {
        let mut rng = test_rng();
        let pp = PublicParameters::<Bn254>::new::<StdRng>(
            &mut rng,
            8, 4, 4,
        ).unwrap();
        println!("{:?}", pp);
    }
}