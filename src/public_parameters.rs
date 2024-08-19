use std::cmp::max;

use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, PrimeField};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_std::rand::rngs::StdRng;
use ark_std::{UniformRand, Zero};

use crate::domain::{create_sub_domain, identity_poly, roots_of_unity, vanishing_poly_g2};
use crate::error::Error;
use crate::kzg::unsafe_setup_from_tau;
use crate::lagrange_basis::{lagrange_basis, lagrange_basis_g1, zero_opening_proofs};

#[derive(Debug)]
pub struct PublicParameters<E: PairingEngine> {
    // Number of total segments in the table (n).
    pub(crate) num_table_segments: usize,
    // Number of segments in the witness. This is fixed for all queries (k).
    pub(crate) num_witness_segments: usize,
    // Segment size (s).
    pub(crate) segment_size: usize,
    // Table size (n * s).
    pub(crate) table_element_size: usize,
    // Witness size (k * s).
    pub(crate) witness_element_size: usize,
    // [tau^i]_1 for i in 0..max*s.
    pub(crate) g1_srs: Vec<E::G1Affine>,
    // [tau^i]_2 for i in 0..max*s.
    pub(crate) g2_srs: Vec<E::G2Affine>,
    // [Z_W(tau)]_2.
    pub(crate) g2_zw: E::G2Affine,
    // q_{i, 2} for i in 1..n*s.
    // The commitment of quotient polynomials Q_{i, 2} s.t.
    // L^W_i(X) * X = omega^i * L^W_i(X) + Z_W(X) * Q_{i, 2}(X).
    pub(crate) g1_q2_list: Vec<E::G1Affine>,
    // q_{i, 3} for i in 1..n*s.
    pub(crate) g1_q3_list: Vec<E::G1Affine>,
    // [L^W_i(tau)]_1 for i in 1..n*s.
    pub(crate) g1_l_w_list: Vec<E::G1Affine>,
    // [(L^W_i(tau) - L^W_i(0)) / tau]_1 for i in 1..n*s.
    pub(crate) g1_l_w_opening_proofs_at_zero: Vec<E::G1Affine>,
    // [L^V_i(tau)]_1 for i in 1..k*s.
    pub(crate) g1_l_v_list: Vec<E::G1Affine>,

    // Domain W, V, and K.
    pub(crate) domain_w: Radix2EvaluationDomain<E::Fr>,
    pub(crate) domain_v: Radix2EvaluationDomain<E::Fr>,
    pub(crate) domain_k: Radix2EvaluationDomain<E::Fr>,

    // Caulk Sub-protocol parameters.
    pub(crate) g1_srs_caulk: Vec<E::G1Affine>,
    pub(crate) g2_srs_caulk: Vec<E::G2Affine>,
    pub(crate) log_num_table_segments: usize,
    pub(crate) domain_log_n: Radix2EvaluationDomain<E::Fr>,
    pub(crate) lagrange_basis_log_n: Vec<DensePolynomial<E::Fr>>,
    pub(crate) identity_poly_k: DensePolynomial<E::Fr>,
}

impl<E: PairingEngine> PublicParameters<E> {
    pub fn setup(
        rng: &mut StdRng,
        num_table_segments: usize,
        num_witness_segments: usize,
        segment_size: usize,
    ) -> Result<PublicParameters<E>, Error> {
        let table_element_size = num_table_segments * segment_size;
        let witness_element_size = num_witness_segments * segment_size;
        let log_num_table_segments = max(num_table_segments.trailing_zeros() as usize, 2);

        // Step 1: Choose a random tau. Let max = max(k, n). Compute SRS from tau.
        let tau = E::Fr::rand(rng);
        let max_pow_of_tau_g1 = max(num_table_segments, num_witness_segments) * segment_size - 1;
        let max_pow_of_tau_caulk_g1 = (num_witness_segments.pow(2) - 1) * log_num_table_segments;
        let (g1_srs, g2_srs, g1_srs_caulk, g2_srs_caulk) =
            unsafe_setup_from_tau::<E, StdRng>(max_pow_of_tau_g1, max_pow_of_tau_caulk_g1, tau);

        // Step 2: Compute [Z_W(tau)]_2.
        let order_w = num_table_segments * segment_size;
        let domain_w: Radix2EvaluationDomain<E::Fr> = Radix2EvaluationDomain::<E::Fr>::new(order_w)
            .ok_or(Error::FailedToCreateEvaluationDomain)?;
        let g2_zw = vanishing_poly_g2::<E>(&g2_srs, &domain_w);

        // Step 2: Compute [Z_V(tau)]_2.
        let order_v = num_witness_segments * segment_size;
        let domain_v: Radix2EvaluationDomain<E::Fr> = Radix2EvaluationDomain::<E::Fr>::new(order_v)
            .ok_or(Error::FailedToCreateEvaluationDomain)?;

        // Step 2: Compute [Z_K(tau)]_2.
        // K = {v^{is}, i \in [0, k - 1]}.
        let order_k = num_witness_segments;
        let domain_k = create_sub_domain::<E>(&domain_v, order_k, segment_size)?;

        // Step 4-a: Compute q_{i, 2} = [Q_{i,2}(tau)]_1 for i in 1..n*s.
        // Q_{i,2}(X) = w^i / (ns).
        let roots_of_unity_w: Vec<E::Fr> = roots_of_unity::<E>(&domain_w);
        let quotient_values: Vec<E::Fr> = roots_of_unity_w
            .iter()
            .map(|&x| x / E::Fr::from(order_w as u64))
            .collect();
        let g1_q2_list = quotient_values
            .iter()
            .map(|&x| g1_srs[0].clone().mul(x).into())
            .collect();

        // Step 4-b: Compute [L^W_i(tau)]_1 for i in 1..n*s.
        let g1_l_w_list = lagrange_basis_g1(&g1_srs, &domain_w);

        // Step 4-c: Compute [(L^W_i(tau) - L^W_i(0)) / tau]_1 for i in 1..n*s.
        // a.k.a. zero openings of the Lagrange basis.
        let g1_l_w_opening_proofs_at_zero =
            match zero_opening_proofs::<E>(&g1_srs, &domain_w, &g1_l_w_list) {
                Ok(proofs) => proofs,
                Err(e) => return Err(e),
            };

        // Step 5: Compute [L^V_i(tau)]_1 for i in 1..k*s.
        let g1_l_v_list = lagrange_basis_g1(&g1_srs, &domain_v);

        // Step 6: Compute quotient polynomial commitments q_{i, 3} and q_{i, 4} for i in 1..n*s.
        // q_{i, 3} = [(w^i / ns) * (tau^n - w^{in}) / (tau - w^i)]_1.
        let fr_inv_ns = domain_w
            .size_as_field_element()
            .inverse()
            .ok_or(Error::FailedToInverseFieldElement)?;
        let inv_tau_sub_w_pow_i_list: Vec<E::Fr> = roots_of_unity_w
            .iter()
            .map(|x| (tau - x).inverse().unwrap_or_else(|| E::Fr::zero()))
            .collect();
        let fr_tau_pow_n = tau.pow([num_table_segments as u64]);
        let tau_pow_n_sub_w_pow_in_list: Vec<E::Fr> = (0..order_w)
            .map(|i| fr_tau_pow_n - roots_of_unity_w[i].pow([num_table_segments as u64]))
            .collect();
        let g1_q3_list: Vec<E::G1Affine> = (0..order_w)
            .map(|i| {
                let mut q3 = g1_srs[0].clone().mul(roots_of_unity_w[i]);
                q3 = q3.mul(fr_inv_ns.into_repr());
                q3 = q3.mul(tau_pow_n_sub_w_pow_in_list[i].into_repr());
                q3 = q3.mul(inv_tau_sub_w_pow_i_list[i].into_repr());

                q3.into_affine()
            })
            .collect();

        let domain_log_n: Radix2EvaluationDomain<E::Fr> =
            Radix2EvaluationDomain::<E::Fr>::new(log_num_table_segments)
                .ok_or(Error::FailedToCreateEvaluationDomain)?;
        let lagrange_basis_log_n = lagrange_basis::<E>(&domain_log_n);
        let identity_poly_k = identity_poly::<E>(&domain_k);

        Ok(PublicParameters {
            num_table_segments,
            num_witness_segments,
            segment_size,
            table_element_size,
            witness_element_size,
            g1_srs,
            g2_srs,
            g2_zw,
            g1_q2_list,
            g1_q3_list,
            g1_l_w_list,
            g1_l_w_opening_proofs_at_zero,
            g1_l_v_list,
            domain_w,
            domain_v,
            domain_k,

            g1_srs_caulk,
            g2_srs_caulk,
            log_num_table_segments,
            domain_log_n,
            lagrange_basis_log_n,
            identity_poly_k,
        })
    }
}

#[cfg(test)]
mod test {
    use ark_bn254::Bn254;
    use ark_std::test_rng;

    use super::*;

    #[test]
    fn test_public_parameters_setup() {
        let mut rng = test_rng();
        PublicParameters::<Bn254>::setup(&mut rng, 8, 4, 4).unwrap();
    }
}
