use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::ops::{Div, Mul, Neg, Sub};

use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_poly::{EvaluationDomain, UVPolynomial};
use ark_poly::univariate::DensePolynomial;
use ark_std::{One, Zero};

use crate::error::Error;
use crate::kzg::Kzg;
use crate::public_parameters::PublicParameters;
use crate::rng::FiatShamirRng;
use crate::table::PreprocessedParameters;
use crate::witness::Witness;

pub struct Prover<E: PairingEngine, FS: FiatShamirRng> {
    _e: PhantomData<E>,
    _fs: PhantomData<FS>,
}

pub struct Proof<E: PairingEngine> {
    m_com1: E::G1Affine,
    m_inv_w_com1: E::G1Affine,
    l_com1: E::G1Affine,
    l_mul_v_com1: E::G1Affine,

}

impl<E: PairingEngine, FS: FiatShamirRng> Prover<E, FS> {
    pub fn prove(
        pp: &PublicParameters<E>,
        tpp: &PreprocessedParameters<E>,
        witness: &Witness<E>,
        statement: E::G1Affine,
    ) -> Result<Proof<E>, Error> {
        // Round 1-1: Compute the multiplicity polynomial M of degree (ns - 1),
        // and send [M(tau)]_1 and [M(tau / w)]_1 to the verifier.
        // Round 1-2: Compute and send [Q_M(tau)]_1 using the SRS and Lemma 4.
        let mut multiplicities = BTreeMap::<usize, usize>::default();
        for &i in witness.queried_segment_indices.iter() {
            if i > pp.num_segments {
                return Err(Error::InvalidSegmentIndex(i));
            }

            let segment_index_multiplicity = multiplicities
                .entry(i)
                .or_insert(0);
            *segment_index_multiplicity += 1;
        }
        let mut m_com1 = E::G1Affine::zero(); // [M(tau)]_1
        let mut m_inv_w_com1 = E::G1Affine::zero(); // [M(tau / w)]_1
        let mut q_m_com1 = E::G1Affine::zero(); // [Q_M(tau)]_1
        for (&i, &m) in multiplicities.iter() {
            let segment_element_indices = i * pp.segment_size..(i + 1) * pp.segment_size;
            let multiplicity_fr = E::Fr::from(m as u64);
            for j in segment_element_indices {
                // Linear combination of [L^W_i(tau)]_1
                m_com1 = pp.l_w_com1_list[j]
                    .mul(multiplicity_fr)
                    .add_mixed(&m_com1)
                    .into_affine();
                // Linear combination of [L^W_i(tau / w)]_1
                m_inv_w_com1 = pp.l_w_inv_w_com1_list[j]
                    .mul(multiplicity_fr)
                    .add_mixed(&m_inv_w_com1)
                    .into_affine();
                // Linear combination of q_{i, 3}
                q_m_com1 = pp.q_3_com1_list[j]
                    .mul(multiplicity_fr)
                    .add_mixed(&q_m_com1)
                    .into_affine();
                // Linear combination of q_{i, 4}
                q_m_com1 = pp.q_4_com1_list[j]
                    .mul(multiplicity_fr)
                    .neg()
                    .add_mixed(&q_m_com1)
                    .into_affine();
            }
        }
        // TODO: Send [M(tau)]_1, [M(tau / w)]_1, and [Q_M(tau)]_1 to the verifier

        // Round 1-3: Compute the indexing polynomial L(X) of degree (ks - 1),
        // which maps the segment element indices from the witness to the table.
        // Round 1-5: Compute another indexing polynomial D(X) of degree (k - 1).
        // For each i \in [0, k - 1], D(v^{is}) = L(v^{is}) = w^{js}
        let mut l_poly_evaluations: Vec<E::Fr> = Vec::with_capacity(pp.witness_size);
        let mut l_com1 = E::G1Affine::zero(); // [L(tau)]_1
        let mut l_mul_v_com1 = E::G1Affine::zero(); // [L(tau * v)]_1
        let roots_of_unity_w: Vec<E::Fr> = pp.domain_w.elements().collect();
        let mut witness_element_index: usize = 0;
        let mut d_poly_evaluations: Vec<E::Fr> = Vec::with_capacity(pp.num_queries);
        for &seg_index in witness.queried_segment_indices.iter() {
            let segment_element_indices = seg_index * pp.segment_size..(seg_index + 1) * pp.segment_size;
            for j in segment_element_indices {
                let root_of_unity_w = roots_of_unity_w[j];
                l_poly_evaluations.push(root_of_unity_w);
                // Linear combination of [L^V_i(tau)]_1
                l_com1 = pp.l_v_com1_list[witness_element_index]
                    .mul(root_of_unity_w)
                    .add_mixed(&l_com1)
                    .into_affine();
                // Linear combination of [L^V_i(tau * v)]_1
                l_mul_v_com1 = pp.l_v_mul_v_com1_list[witness_element_index]
                    .mul(root_of_unity_w)
                    .add_mixed(&l_mul_v_com1)
                    .into_affine();
                witness_element_index += 1;
            }
            
            let root_of_unity_w = roots_of_unity_w[seg_index * pp.segment_size];
            d_poly_evaluations.push(root_of_unity_w);
        }
        // TODO: Send [L(tau)]_1 and [L(tau * v)]_1 to the verifier

        // Round 1-4: Compute the quotient polynomial Q_L(X) s.t.
        // (X^k - 1)*(L(Xv) - w*L(X)) = Z_V(X)*Q_L(X),
        // and send [Q_L(tau)]_1 to the verifier.
        // Inverse FFT costs O(ks log(ks)) operations
        let l_poly_coefficients = pp.domain_v.ifft(&l_poly_evaluations);
        // The coefficients of L(Xv). We can scale each L(X) polynomial coefficients by v^i
        let domain_v_elements: Vec<E::Fr> = pp.domain_v.elements().collect();
        let l_mul_v_poly_coefficients: Vec<E::Fr> = l_poly_coefficients
            .iter()
            .enumerate()
            .map(|(i, &c)| c * domain_v_elements[i])
            .collect();
        let l_mul_v_poly = DensePolynomial::from_coefficients_vec(l_mul_v_poly_coefficients);
        // The coefficients of w*L(X).
        let domain_w_generator = roots_of_unity_w[1];
        let w_mul_l_poly_coefficients: Vec<E::Fr> = l_poly_coefficients
            .iter()
            .map(|&c| c * domain_w_generator)
            .collect();
        let w_mul_l_poly = DensePolynomial::from_coefficients_vec(w_mul_l_poly_coefficients);
        // The coefficients of f(X) = X^k - 1
        let mut x_pow_k_minus_one_poly_coefficients = vec![E::Fr::zero(); pp.witness_size];
        x_pow_k_minus_one_poly_coefficients[pp.num_queries] = E::Fr::one();
        x_pow_k_minus_one_poly_coefficients[0] = -E::Fr::one();
        let x_pow_k_minus_one_poly = DensePolynomial::from_coefficients_vec(x_pow_k_minus_one_poly_coefficients);
        let domain_v_vanishing_poly: DensePolynomial<E::Fr> = pp.domain_v.vanishing_polynomial().into();
        let mut q_l_poly = l_mul_v_poly.sub(&w_mul_l_poly);
        q_l_poly = q_l_poly.div(&domain_v_vanishing_poly);
        q_l_poly = q_l_poly.mul(&x_pow_k_minus_one_poly);
        let q_l_com1 = Kzg::<E>::commit_g1(&pp.srs_g1, &q_l_poly)
            .into_affine();
        // TODO: Send [Q_L(tau)]_1 to the verifier
        
        // Round 1-6: Compute Q_D s.t. L(X) - D(X) = Z_K(X)*Q_D(X),
        // and send [Q_D(tau)]_1 to the verifier. 
        let l_poly = DensePolynomial::from_coefficients_vec(l_poly_coefficients);
        let d_poly = DensePolynomial::from_coefficients_vec(d_poly_evaluations);
        let mut q_d_poly = l_poly.sub(&d_poly);
        let domain_k_vanishing_poly: DensePolynomial<E::Fr> = pp.domain_k.vanishing_polynomial().into();
        q_d_poly = q_d_poly.div(&domain_k_vanishing_poly);
        let q_d_com1 = Kzg::<E>::commit_g1(&pp.srs_g1, &q_d_poly)
            .into_affine();
        // TODO: Send [Q_D(tau)]_1 to the verifier
        
        

        todo!()
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;
    use ark_ec::PairingEngine;
    use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};

    #[test]
    fn test_domain_generator() {
        let size = 8;
        let domain = Radix2EvaluationDomain::<<Bn254 as PairingEngine>::Fr>::new(size).unwrap();
        let domain_elements: Vec<_> = domain.elements().collect();
        assert_eq!(domain_elements[1], domain.group_gen);
    }
}