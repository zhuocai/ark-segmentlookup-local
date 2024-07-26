use std::collections::BTreeMap;
use std::ops::{Add, Div, Mul, Sub};

use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain, UVPolynomial};
use ark_poly::univariate::DensePolynomial;
use ark_std::{One, Zero};

use crate::error::Error;
use crate::kzg::Kzg;
use crate::public_parameters::PublicParameters;
use crate::rng::FiatShamirRng;
use crate::witness::Witness;

pub struct Proof<E: PairingEngine> {
    // Round 1 message
    pub(crate) m_com1: E::G1Affine, // [M(tau)]_1
    pub(crate) m_div_w_com1: E::G1Affine, // [M(tau / w)]_1
    pub(crate) q_m_com1: E::G1Affine, // [Q_M(tau)]_1
    l_com1: E::G1Affine, // [L(tau)]_1
    l_mul_v_com1: E::G1Affine, // [L(tau * v)]_1
    q_l_com1: E::G1Affine, // [Q_L(tau)]_1
    d_com1: E::G1Affine, // [D(tau)]_1
    q_d_com1: E::G1Affine, // [Q_D(tau)]_1
}

pub fn prove<E: PairingEngine, FS: FiatShamirRng>(
    pp: &PublicParameters<E>,
    // tpp: &PreprocessedParameters<E>,
    witness: &Witness<E>,
    // statement: E::G1Affine,
) -> Result<Proof<E>, Error> {
    // Round 1-1: Compute the multiplicity polynomial M of degree (ns - 1),
    // and send [M(tau)]_1 and [M(tau / w)]_1 to the verifier.
    // Round 1-2: Compute and send [Q_M(tau)]_1 using the SRS and Lemma 4.
    let multiplicities = segment_multiplicities(
        &witness.queried_segment_indices,
        pp.num_segments,
    )?;
    let MultiplicityPolynomialsAndQuotient {
        m_com1,
        m_div_w_com1,
        q_m_com1,
    } = com1_multiplicity_polynomials_and_quotient::<E>(
        &multiplicities,
        &pp.l_w_com1_list,
        &pp.l_w_div_w_com1_list,
        &pp.q_3_com1_list,
        &pp.q_4_com1_list,
        pp.segment_size,
    );

    // Round 1-3: Compute the indexing polynomial L(X) of degree (ks - 1),
    // which maps the segment element indices from the witness to the table.
    // Round 1-5: Compute another indexing polynomial D(X) of degree (k - 1).
    // For each i \in [0, k - 1], D(v^{is}) = L(v^{is}) = w^{js}
    // Round 1-4: Compute the quotient polynomial Q_L(X) s.t.
    // (X^k - 1)*(L(Xv) - w*L(X)) = Z_V(X)*Q_L(X),
    // and send [Q_L(tau)]_1 to the verifier.
    // Inverse FFT costs O(ks log(ks)) operations
    // Round 1-6: Compute Q_D s.t. L(X) - D(X) = Z_K(X)*Q_D(X),
    // and send [Q_D(tau)]_1 to the verifier.
    let IndexPolynomialsAndQuotients {
        l_com1,
        l_mul_v_com1,
        d_com1,
        q_l_com1,
        q_d_com1,
    } = com1_index_polynomials_and_quotients::<E>(
        &pp.domain_w,
        &pp.domain_k,
        &pp.domain_v,
        &pp.l_v_com1_list,
        &pp.l_v_mul_v_com1_list,
        &pp.srs_g1,
        &witness.queried_segment_indices,
        pp.witness_size,
        pp.segment_size,
        pp.num_queries,
    );

    // Round 2 is performed by the verifier

    // Round 3 - Round 8:
    // Using the instantiation of Lemma 5,
    // the prover and verifier engage in a protocol that polynomial L is well-formed.


    // todo!()

    Ok(Proof {
        m_com1,
        m_div_w_com1,
        q_m_com1,
        l_com1,
        l_mul_v_com1,
        q_l_com1,
        d_com1,
        q_d_com1,
    })
}

fn segment_multiplicities(
    queried_segment_indices: &[usize],
    num_segments: usize,
) -> Result<BTreeMap<usize, usize>, Error> {
    let mut multiplicities = BTreeMap::<usize, usize>::default();
    for &i in queried_segment_indices.iter() {
        if i > num_segments {
            return Err(Error::InvalidSegmentIndex(i));
        }

        let segment_index_multiplicity = multiplicities
            .entry(i)
            .or_insert(0);
        *segment_index_multiplicity += 1;
    }

    Ok(multiplicities)
}

// Multiplicity polynomials and the quotient,
// containing [M(tau)]_1, [M(tau / w)]_1, and [Q_M(tau)]_1.
struct MultiplicityPolynomialsAndQuotient<E: PairingEngine> {
    m_com1: E::G1Affine,
    m_div_w_com1: E::G1Affine,
    q_m_com1: E::G1Affine,
}

// Compute [M(tau)]_1, [M(tau / w)]_1, and [Q_M(tau)]_1
fn com1_multiplicity_polynomials_and_quotient<E: PairingEngine>(
    multiplicities: &BTreeMap<usize, usize>,
    l_w_com1_list: &[E::G1Affine],
    l_w_div_w_com1_list: &[E::G1Affine],
    q_3_com1_list: &[E::G1Affine],
    q_4_com1_list: &[E::G1Affine],
    segment_size: usize,
) -> MultiplicityPolynomialsAndQuotient<E> {
    let mut m_com1_proj = E::G1Projective::zero(); // [M(tau)]_1
    let mut m_div_w_com1_proj = E::G1Projective::zero(); // [M(tau / w)]_1
    let mut q_m_com1_proj = E::G1Projective::zero(); // [Q_M(tau)]_1
    for (&i, &m) in multiplicities.iter() {
        let segment_element_indices = i * segment_size..(i + 1) * segment_size;
        let multiplicity_fr = E::Fr::from(m as u64);
        for elem_index in segment_element_indices {
            // Linear combination of [L^W_i(tau)]_1
            m_com1_proj = l_w_com1_list[elem_index]
                .mul(multiplicity_fr)
                .add(m_com1_proj);
            // Linear combination of [L^W_i(tau / w)]_1
            m_div_w_com1_proj = l_w_div_w_com1_list[elem_index]
                .mul(multiplicity_fr)
                .add(m_div_w_com1_proj);
            // Linear combination of q_{i, 3}
            q_m_com1_proj = q_3_com1_list[elem_index]
                .mul(multiplicity_fr)
                .add(q_m_com1_proj);
            // Linear combination of q_{i, 4}
            q_m_com1_proj = q_4_com1_list[elem_index]
                .mul(-multiplicity_fr) // negate the coefficient
                .add(q_m_com1_proj);
        }
    }

    MultiplicityPolynomialsAndQuotient {
        m_com1: m_com1_proj.into_affine(),
        m_div_w_com1: m_div_w_com1_proj.into_affine(),
        q_m_com1: q_m_com1_proj.into_affine(),
    }
}

// Index polynomials and the quotients,
// containing [L(tau)]_1, [L(tau * v)]_1, [D(tau)]_1, [Q_L(tau)]_1, and [Q_D(tau)]_1.
struct IndexPolynomialsAndQuotients<E: PairingEngine> {
    l_com1: E::G1Affine,
    l_mul_v_com1: E::G1Affine,
    d_com1: E::G1Affine,
    q_l_com1: E::G1Affine,
    q_d_com1: E::G1Affine,
}

// Compute the commitments of [L(tau)]_1, [L(tau*v)]_1, [D(tau)]_1, [Q_L(tau)]_1, and [Q_D(tau)]_1
fn com1_index_polynomials_and_quotients<E: PairingEngine>(
    domain_w: &Radix2EvaluationDomain<E::Fr>,
    domain_k: &Radix2EvaluationDomain<E::Fr>,
    domain_v: &Radix2EvaluationDomain<E::Fr>,
    l_v_com1_list: &[E::G1Affine],
    l_v_mul_v_com1_list: &[E::G1Affine],
    srs_g1: &[E::G1Affine],
    queried_segment_indices: &[usize],
    witness_size: usize,
    segment_size: usize,
    num_queries: usize,
) -> IndexPolynomialsAndQuotients<E> {
    let mut l_poly_evaluations: Vec<E::Fr> = Vec::with_capacity(witness_size);
    let mut l_com1_proj = E::G1Projective::zero(); // [L(tau)]_1
    let mut l_mul_v_com1_proj = E::G1Projective::zero(); // [L(tau * v)]_1
    let roots_of_unity_w: Vec<E::Fr> = domain_w.elements().collect();
    let mut witness_element_index: usize = 0;
    let mut d_poly_evaluations: Vec<E::Fr> = Vec::with_capacity(num_queries);
    for &seg_index in queried_segment_indices.iter() {
        let segment_element_indices = seg_index * segment_size..(seg_index + 1) * segment_size;
        for j in segment_element_indices {
            let root_of_unity_w = roots_of_unity_w[j];
            l_poly_evaluations.push(root_of_unity_w);
            // Linear combination of [L^V_i(tau)]_1
            l_com1_proj = l_v_com1_list[witness_element_index]
                .mul(root_of_unity_w)
                .add(l_com1_proj);
            // Linear combination of [L^V_i(tau * v)]_1
            l_mul_v_com1_proj = l_v_mul_v_com1_list[witness_element_index]
                .mul(root_of_unity_w)
                .add(l_mul_v_com1_proj);
            witness_element_index += 1;
        }

        let root_of_unity_w = roots_of_unity_w[seg_index * segment_size];
        d_poly_evaluations.push(root_of_unity_w);
    }

    let d_poly_coefficients = domain_k.ifft(&d_poly_evaluations);
    let d_poly = DensePolynomial::from_coefficients_vec(d_poly_coefficients);
    let d_com1 = Kzg::<E>::commit_g1(srs_g1, &d_poly)
        .into_affine();

    // Compute the quotient polynomial Q_L(X) s.t. (X^k - 1)*(L(Xv) - w*L(X)) = Z_V(X)*Q_L(X),
    // Inverse FFT costs O(ks log(ks)) operations
    let l_poly_coefficients = domain_v.ifft(&l_poly_evaluations);
    // The coefficients of L(Xv). We can scale each L(X) polynomial coefficients by v^i
    let domain_v_elements: Vec<E::Fr> = domain_v.elements().collect();
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
    let mut x_pow_k_sub_one_poly_coefficients = vec![E::Fr::zero(); witness_size];
    x_pow_k_sub_one_poly_coefficients[num_queries] = E::Fr::one();
    x_pow_k_sub_one_poly_coefficients[0] = -E::Fr::one();
    let x_pow_k_sub_one_poly = DensePolynomial::from_coefficients_vec(x_pow_k_sub_one_poly_coefficients);
    let domain_v_vanishing_poly: DensePolynomial<E::Fr> = domain_v.vanishing_polynomial().into();
    let mut q_l_poly = l_mul_v_poly.sub(&w_mul_l_poly);
    q_l_poly = q_l_poly.div(&domain_v_vanishing_poly);
    q_l_poly = q_l_poly.mul(&x_pow_k_sub_one_poly);
    let q_l_com1 = Kzg::<E>::commit_g1(&srs_g1, &q_l_poly)
        .into_affine();

    // Compute Q_D s.t. L(X) - D(X) = Z_K(X)*Q_D(X).
    let l_poly = DensePolynomial::from_coefficients_vec(l_poly_coefficients);
    let d_poly = DensePolynomial::from_coefficients_vec(d_poly_evaluations);
    let mut q_d_poly = l_poly.sub(&d_poly);
    let domain_k_vanishing_poly: DensePolynomial<E::Fr> = domain_k.vanishing_polynomial().into();
    q_d_poly = q_d_poly.div(&domain_k_vanishing_poly);
    let q_d_com1 = Kzg::<E>::commit_g1(&srs_g1, &q_d_poly)
        .into_affine();

    IndexPolynomialsAndQuotients {
        l_com1: l_com1_proj.into_affine(),
        l_mul_v_com1: l_mul_v_com1_proj.into_affine(),
        d_com1,
        q_l_com1,
        q_d_com1,
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Neg;

    use ark_bn254::Bn254;
    use ark_ff::Field;
    use ark_std::{test_rng, UniformRand};

    use super::*;

    type Fr = <Bn254 as PairingEngine>::Fr;
    type G1Affine = <Bn254 as PairingEngine>::G1Affine;
    type G2Affine = <Bn254 as PairingEngine>::G2Affine;

    #[test]
    fn test_mul_and_neg() {
        let mut rng = test_rng();
        let s1 = Fr::rand(&mut rng);
        let s2 = Fr::rand(&mut rng);
        let p1 = G1Affine::prime_subgroup_generator().mul(s1).into_affine();
        assert_eq!(p1.mul(s2).neg(), p1.mul(-s2));
    }

    #[test]
    fn test_domain_generator() {
        let size = 8;
        let domain = Radix2EvaluationDomain::<<Bn254 as PairingEngine>::Fr>::new(size).unwrap();
        let domain_elements: Vec<_> = domain.elements().collect();
        assert_eq!(domain_elements[1], domain.group_gen);
    }

    #[test]
    fn test_segment_multiplicities() {
        let queried_segment_indices = vec![0, 1, 2, 3, 0, 1, 2, 3];
        let num_segments = 4;
        let multiplicities = segment_multiplicities(
            &queried_segment_indices,
            num_segments,
        ).unwrap();
        assert_eq!(multiplicities.len(), 4);
        assert_eq!(multiplicities[&0], 2);
        assert_eq!(multiplicities[&1], 2);
        assert_eq!(multiplicities[&2], 2);
        assert_eq!(multiplicities[&3], 2);
    }

    #[test]
    fn test_com1_multiplicity_polynomials_and_quotient() {
        let mut rng = test_rng();
        let num_segments = 16;
        let num_queries = 8;
        let segment_size = 4;
        let pp = PublicParameters::<Bn254>::setup(
            &mut rng,
            num_segments,
            num_queries,
            segment_size,
        ).unwrap();
        let queried_segment_indices = vec![0, 1, 2, 3, 0, 1, 2, 3];
        let multiplicities = segment_multiplicities(
            &queried_segment_indices,
            num_segments,
        ).unwrap();

        // Construct polynomial M(X) using Inverse FFT.
        let mut m_poly_evaluations = vec![Fr::zero(); pp.table_size];
        for (&i, &m) in multiplicities.iter() {
            let segment_element_indices = i * segment_size..(i + 1) * segment_size;
            let multiplicity_fr = Fr::from(m as u64);
            for j in segment_element_indices {
                m_poly_evaluations[j] = multiplicity_fr;
            }
        }
        let m_poly_coefficients = pp.domain_w.ifft(&m_poly_evaluations);
        let m_poly = DensePolynomial::from_coefficients_vec(m_poly_coefficients.clone());
        let m_com1_expected = Kzg::<Bn254>::commit_g1(&pp.srs_g1, &m_poly)
            .into_affine();
        let domain_w_generator_inv = pp.domain_w.group_gen_inv;
        let m_div_w_poly_coefficients: Vec<Fr> = m_poly_coefficients
            .iter()
            .enumerate()
            .map(|(i, &c)| c * domain_w_generator_inv.pow(&[i as u64]))
            .collect();
        let m_div_w_poly = DensePolynomial::from_coefficients_vec(m_div_w_poly_coefficients);
        let m_div_w_com1_expected = Kzg::<Bn254>::commit_g1(&pp.srs_g1, &m_div_w_poly)
            .into_affine();

        let mut x_pow_n_sub_one_poly_coefficients = vec![Fr::zero(); pp.table_size];
        x_pow_n_sub_one_poly_coefficients[pp.num_segments] = Fr::one();
        x_pow_n_sub_one_poly_coefficients[0] = -Fr::one();
        let x_pow_n_sub_one_poly = DensePolynomial::from_coefficients_vec(x_pow_n_sub_one_poly_coefficients);
        let mut q_m_poly = m_poly.clone();
        q_m_poly = q_m_poly.sub(&m_div_w_poly);
        q_m_poly = q_m_poly.naive_mul(&x_pow_n_sub_one_poly);
        q_m_poly = q_m_poly.div(&pp.domain_w.vanishing_polynomial().into());
        let q_m_com1_expected = Kzg::<Bn254>::commit_g1(&pp.srs_g1, &q_m_poly).into_affine();

        let MultiplicityPolynomialsAndQuotient {
            m_com1: m_com1_got,
            m_div_w_com1: m_div_w_com1_got,
            q_m_com1: q_m_com1_got,
        } =
            com1_multiplicity_polynomials_and_quotient::<Bn254>(
                &multiplicities,
                &pp.l_w_com1_list,
                &pp.l_w_div_w_com1_list,
                &pp.q_3_com1_list,
                &pp.q_4_com1_list,
                segment_size,
            );

        assert_eq!(m_com1_expected, m_com1_got);
        assert_eq!(m_div_w_com1_expected, m_div_w_com1_got);
        assert_eq!(q_m_com1_expected, q_m_com1_got);
    }
}