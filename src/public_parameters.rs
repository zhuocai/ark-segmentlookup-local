use crate::domain::{
    create_domain_with_generator, create_sub_domain, identity_poly, roots_of_unity,
    vanishing_poly_commitment_affine,
};
use crate::error::Error;
use crate::kzg::unsafe_setup_from_tau;
use crate::lagrange_basis::{lagrange_basis_g1, zero_opening_proofs};
use ark_ec::{pairing::Pairing, CurveGroup};
use ark_ff::{FftField, Field};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_std::rand::rngs::StdRng;
use ark_std::rand::Rng;
use ark_std::{One, UniformRand, Zero};
use rayon::prelude::*;
use std::cmp::max;
use std::ops::{Mul, MulAssign};

#[derive(Debug)]
pub struct PublicParameters<P: Pairing> {
    // Number of total segments in the table (n).
    pub num_table_segments: usize,
    // Number of segments in the witness. This is fixed for all queries (k).
    pub num_witness_segments: usize,
    // Segment size (s).
    pub segment_size: usize,
    // Table size (n * s).
    pub(crate) table_element_size: usize,
    // Witness size (k * s).
    pub(crate) witness_element_size: usize,
    // [tau^i]_1 for i in 0..max*s.
    pub g1_affine_srs: Vec<P::G1Affine>,
    // [tau^i]_2 for i in 0..max*s.
    pub g2_affine_srs: Vec<P::G2Affine>,
    // [Z_W(tau)]_2.
    pub g2_affine_zw: P::G2Affine,
    // [Z_V(tau)]_2.
    pub g2_affine_zv: P::G2Affine,
    // [Z_K(tau)]_2.
    pub g2_affine_zk: P::G2Affine,
    // q_{i, 2} for i in 1..n*s.
    // The commitment of quotient polynomials Q_{i, 2} s.t.
    // L^W_i(X) * X = omega^i * L^W_i(X) + Z_W(X) * Q_{i, 2}(X).
    pub(crate) g1_affine_list_q2: Vec<P::G1Affine>,
    // q_{i, 3} for i in 1..n*s.
    pub(crate) g1_affine_list_q3: Vec<P::G1Affine>,
    // [L^W_i(tau)]_1 for i in 1..n*s.
    pub(crate) g1_affine_list_lw: Vec<P::G1Affine>,
    // [(L^W_i(tau) - L^W_i(0)) / tau]_1 for i in 1..n*s.
    pub(crate) g1_affine_lw_opening_proofs_at_zero: Vec<P::G1Affine>,
    // [L^V_i(tau)]_1 for i in 1..k*s.
    pub(crate) g1_affine_list_lv: Vec<P::G1Affine>,

    // Domain W, V, and K.
    pub domain_w: Radix2EvaluationDomain<P::ScalarField>,
    pub domain_v: Radix2EvaluationDomain<P::ScalarField>,
    pub domain_k: Radix2EvaluationDomain<P::ScalarField>,

    pub(crate) domain_coset_v: Radix2EvaluationDomain<P::ScalarField>,

    pub(crate) partial_inv_zk_at_coset_v_values: Vec<P::ScalarField>,

    // Caulk Sub-protocol parameters.
    pub(crate) g1_affine_srs_caulk: Vec<P::G1Affine>,
    pub(crate) g2_affine_srs_caulk: Vec<P::G2Affine>,
    pub(crate) log_num_table_segments: usize,
    pub(crate) domain_log_n: Radix2EvaluationDomain<P::ScalarField>,
    pub(crate) identity_poly_k: DensePolynomial<P::ScalarField>,
}

impl<P: Pairing> PublicParameters<P> {
    pub fn builder() -> PublicParametersBuilder<P> {
        PublicParametersBuilder::<P>::default()
    }
}

pub struct PublicParametersBuilder<P: Pairing> {
    num_table_segments: Option<usize>,
    num_witness_segments: Option<usize>,
    segment_size: Option<usize>,
    tau: Option<P::ScalarField>,
    domain_generator_w: Option<P::ScalarField>,
    domain_generator_v: Option<P::ScalarField>,
}

impl<P: Pairing> PublicParametersBuilder<P> {
    fn default() -> Self {
        Self {
            num_table_segments: None,
            num_witness_segments: None,
            segment_size: None,
            tau: None,
            domain_generator_w: None,
            domain_generator_v: None,
        }
    }

    /// Sets the number of table segments.
    pub fn num_table_segments(mut self, num: usize) -> Self {
        self.num_table_segments = Some(num);
        self
    }

    /// Sets the number of witness segments.
    pub fn num_witness_segments(mut self, num: usize) -> Self {
        self.num_witness_segments = Some(num);
        self
    }

    /// Sets the segment size.
    pub fn segment_size(mut self, size: usize) -> Self {
        self.segment_size = Some(size);
        self
    }

    /// Sets a specific tau value.
    pub fn tau(mut self, tau: P::ScalarField) -> Self {
        self.tau = Some(tau);
        self
    }

    /// Sets a specific generator for domain W.
    pub fn domain_generator_w(mut self, gen: P::ScalarField) -> Self {
        self.domain_generator_w = Some(gen);
        self
    }

    /// Sets a specific generator for domain V.
    pub fn domain_generator_v(mut self, gen: P::ScalarField) -> Self {
        self.domain_generator_v = Some(gen);
        self
    }

    pub fn build<R: Rng + ?Sized>(self, rng: &mut R) -> Result<PublicParameters<P>, Error> {
        // Extract parameters or set defaults.
        let num_table_segments = self
            .num_table_segments
            .ok_or(Error::MissingParameter("num_table_segments"))?;
        let num_witness_segments = self
            .num_witness_segments
            .ok_or(Error::MissingParameter("num_witness_segments"))?;
        let segment_size = self
            .segment_size
            .ok_or(Error::MissingParameter("segment_size"))?;
        let tau = self.tau.unwrap_or_else(|| P::ScalarField::rand(rng));

        // Compute the other sizes.
        let table_element_size = num_table_segments * segment_size;
        let witness_element_size = num_witness_segments * segment_size;
        let log_num_table_segments = max(num_table_segments.trailing_zeros() as usize, 2);

        // Step 1: Compute SRS from tau.
        let max_pow_of_tau_g1 = max(num_table_segments, num_witness_segments) * segment_size - 1;
        let caulk_max_pow_of_tau_g1 =
            (num_witness_segments + 1) * log_num_table_segments.next_power_of_two();
        let (g1_affine_srs, g2_affine_srs, g1_affine_srs_caulk, g2_affine_srs_caulk) =
            unsafe_setup_from_tau::<P, StdRng>(max_pow_of_tau_g1, caulk_max_pow_of_tau_g1, tau);

        // Step 2: Define domains.
        // Compute [Z_W(tau)]_2.
        let order_w = num_table_segments * segment_size;
        let domain_w = if let Some(domain_generator_w) = self.domain_generator_w {
            create_domain_with_generator::<P::ScalarField>(domain_generator_w, order_w)?
        } else {
            Radix2EvaluationDomain::<P::ScalarField>::new(order_w)
                .ok_or(Error::FailedToCreateEvaluationDomain)?
        };
        let g2_affine_zw = vanishing_poly_commitment_affine::<P::G2>(&g2_affine_srs, &domain_w);

        // Compute [Z_V(tau)]_2.
        let order_v = num_witness_segments * segment_size;
        let domain_v = if let Some(domain_generator_v) = self.domain_generator_v {
            create_domain_with_generator::<P::ScalarField>(domain_generator_v, order_v)?
        } else {
            Radix2EvaluationDomain::<P::ScalarField>::new(order_v)
                .ok_or(Error::FailedToCreateEvaluationDomain)?
        };
        let g2_affine_zv = vanishing_poly_commitment_affine::<P::G2>(&g2_affine_srs, &domain_v);

        // Compute [Z_K(tau)]_2.
        // K = {v^{is}, i \in [0, k - 1]}.
        let order_k = num_witness_segments;
        let domain_k = create_sub_domain::<P>(&domain_v, order_k, segment_size)?;
        let g2_affine_zk = vanishing_poly_commitment_affine::<P::G2>(&g2_affine_srs, &domain_k);

        let domain_coset_v = domain_v
            .get_coset(P::ScalarField::GENERATOR)
            .ok_or(Error::FailedToCreateEvaluationDomain)?;

        let partial_roots_of_unity_coset_v: Vec<P::ScalarField> = (0..segment_size)
            .into_par_iter()
            .map(|i| domain_coset_v.element(i))
            .collect();

        let fr_one = P::ScalarField::one();
        let partial_inv_zk_at_coset_v_values: Result<Vec<P::ScalarField>, Error> =
            partial_roots_of_unity_coset_v
                .par_iter()
                .map(|&x| {
                    let val = x.pow([order_k as u64]) - fr_one;
                    let inv = val.inverse().ok_or(Error::FailedToInverseFieldElement)?;

                    Ok(inv)
                })
                .collect();
        let partial_inv_zk_at_coset_v_values = partial_inv_zk_at_coset_v_values?;

        // Step 4-a: Compute q_{i, 2} = [Q_{i,2}(tau)]_1 for i in 1..n*s.
        // Q_{i,2}(X) = w^i / (ns).
        let roots_of_unity_w: Vec<P::ScalarField> = roots_of_unity::<P>(&domain_w);
        let quotient_values: Vec<P::ScalarField> = roots_of_unity_w
            .par_iter()
            .map(|&x| x / P::ScalarField::from(order_w as u64))
            .collect();
        let g1_affine_list_q2 = quotient_values
            .par_iter()
            .map(|&x| g1_affine_srs[0].mul(x).into())
            .collect();

        // Step 4-b: Compute [L^W_i(tau)]_1 for i in 1..n*s.
        let g1_affine_list_lw = lagrange_basis_g1::<P::G1>(&g1_affine_srs, &domain_w)?;

        // Step 4-c: Compute [(L^W_i(tau) - L^W_i(0)) / tau]_1 for i in 1..n*s.
        // a.k.a. zero openings of the Lagrange basis.
        let g1_affine_lw_opening_proofs_at_zero =
            zero_opening_proofs::<P>(&g1_affine_srs, &domain_w, &g1_affine_list_lw)?;

        // Step 5: Compute [L^V_i(tau)]_1 for i in 1..k*s.
        let g1_affine_list_lv = lagrange_basis_g1::<P::G1>(&g1_affine_srs, &domain_v)?;

        // Step 6: Compute quotient polynomial commitments q_{i, 3} and q_{i, 4} for i
        // in 1..n*s. q_{i, 3} = [(w^i / ns) * (tau^n - w^{in}) / (tau -
        // w^i)]_1.
        let fr_inv_ns = domain_w
            .size_as_field_element()
            .inverse()
            .ok_or(Error::FailedToInverseFieldElement)?;
        let inv_tau_sub_w_pow_i_list: Vec<P::ScalarField> = roots_of_unity_w
            .par_iter()
            .map(|x| {
                (tau - x)
                    .inverse()
                    .unwrap_or_else(|| P::ScalarField::zero())
            })
            .collect();
        let fr_tau_pow_n = tau.pow([num_table_segments as u64]);
        let tau_pow_n_sub_w_pow_in_list: Vec<P::ScalarField> = (0..order_w)
            .into_par_iter()
            .map(|i| fr_tau_pow_n - roots_of_unity_w[i].pow([num_table_segments as u64]))
            .collect();
        let g1_affine_list_q3: Vec<P::G1Affine> = (0..order_w)
            .into_par_iter()
            .map(|i| {
                let mut q3 = g1_affine_srs[0].mul(roots_of_unity_w[i]);
                q3.mul_assign(fr_inv_ns);
                q3.mul_assign(tau_pow_n_sub_w_pow_in_list[i]);
                q3.mul_assign(inv_tau_sub_w_pow_i_list[i]);

                q3.into_affine()
            })
            .collect();

        let domain_log_n: Radix2EvaluationDomain<P::ScalarField> =
            Radix2EvaluationDomain::<P::ScalarField>::new(log_num_table_segments)
                .ok_or(Error::FailedToCreateEvaluationDomain)?;
        let identity_poly_k = identity_poly::<P>(&domain_k);

        Ok(PublicParameters {
            num_table_segments,
            num_witness_segments,
            segment_size,
            table_element_size,
            witness_element_size,

            g1_affine_srs,
            g2_affine_srs,
            g2_affine_zw,
            g2_affine_zv,
            g2_affine_zk,
            g1_affine_list_q2,
            g1_affine_list_q3,
            g1_affine_list_lw,
            g1_affine_lw_opening_proofs_at_zero,
            g1_affine_list_lv,

            domain_w,
            domain_v,
            domain_k,
            domain_coset_v,

            partial_inv_zk_at_coset_v_values,

            g1_affine_srs_caulk,
            g2_affine_srs_caulk,
            log_num_table_segments,
            domain_log_n,
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
    fn test_public_parameters_builder() {
        let mut rng = test_rng();
        PublicParameters::<Bn254>::builder()
            .num_table_segments(8)
            .num_witness_segments(4)
            .segment_size(4)
            .build(&mut rng)
            .unwrap();
    }
}
