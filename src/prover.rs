use std::collections::BTreeMap;
use std::ops::{Add, Div, Mul, Sub};

use crate::error::Error;
use crate::kzg::Kzg;
use crate::multi_unity::{multi_unity_prove, MultiUnityProof};
use crate::public_parameters::PublicParameters;
use crate::transcript::Transcript;
use crate::witness::Witness;
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain, UVPolynomial};
use ark_std::rand::prelude::StdRng;
use ark_std::{One, Zero};

pub struct Proof<E: PairingEngine> {
    // Round 1 message
    pub(crate) g1_m: E::G1Affine,       // [M(tau)]_1
    pub(crate) g1_m_div_w: E::G1Affine, // [M(tau / w)]_1
    pub(crate) g1_q_m: E::G1Affine,     // [Q_M(tau)]_1
    g1_l: E::G1Affine,                  // [L(tau)]_1
    g1_l_mul_v: E::G1Affine,            // [L(tau * v)]_1
    g1_q_l: E::G1Affine,                // [Q_L(tau)]_1
    pub(crate) g1_d: E::G1Affine,       // [D(tau)]_1
    g1_q_d: E::G1Affine,                // [Q_D(tau)]_1

    pub(crate) multi_unity_proof: MultiUnityProof<E>,
}

pub fn prove<E: PairingEngine>(
    pp: &PublicParameters<E>,
    transcript: &mut Transcript<E::Fr>,
    // tpp: &PreprocessedParameters<E>,
    witness: &Witness<E>,
    // statement: E::G1Affine,
    rng: &mut StdRng,
) -> Result<Proof<E>, Error> {
    // Round 1-1: Compute the multiplicity polynomial M of degree (ns - 1),
    // and send [M(tau)]_1 and [M(tau / w)]_1 to the verifier.
    // Round 1-2: Compute and send [Q_M(tau)]_1 using the SRS and Lemma 4.
    let multiplicities = segment_multiplicities(&witness.queried_segment_indices, pp.num_segments)?;
    let MultiplicityPolynomialsAndQuotient {
        g1_m,
        g1_m_div_w,
        g1_q_m,
    } = multiplicity_polynomials_and_quotient_g1::<E>(
        &multiplicities,
        &pp.g1_l_w_list,
        &pp.g1_l_w_div_w_list,
        &pp.g1_q3_list,
        &pp.g1_q4_list,
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
        g1_l,
        g1_l_mul_v,
        g1_d,
        poly_d,
        g1_q_l,
        g1_q_d,
    } = index_polynomials_and_quotients_g1::<E>(
        &pp.domain_w,
        &pp.domain_k,
        &pp.domain_v,
        &pp.g1_l_v_list,
        &pp.g1_l_v_mul_v_list,
        &pp.g1_srs,
        &witness.queried_segment_indices,
        pp.witness_size,
        pp.segment_size,
        pp.num_queries,
    );

    // Round 2 is performed by the verifier

    // Round 3 - Round 8:
    // Using the instantiation of Lemma 5,
    // the prover and verifier engage in a protocol that polynomial L is well-formed.
    let multi_unity_proof = match multi_unity_prove(pp, transcript, &poly_d, &g1_d, rng) {
        Ok(proof) => proof,
        Err(e) => return Err(e),
    };

    // todo!()

    Ok(Proof {
        g1_m,
        g1_m_div_w,
        g1_q_m,
        g1_l,
        g1_l_mul_v,
        g1_q_l,
        g1_d,
        g1_q_d,
        multi_unity_proof,
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

        let segment_index_multiplicity = multiplicities.entry(i).or_insert(0);
        *segment_index_multiplicity += 1;
    }

    Ok(multiplicities)
}

// Multiplicity polynomials and the quotient,
// containing [M(tau)]_1, [M(tau / w)]_1, and [Q_M(tau)]_1.
struct MultiplicityPolynomialsAndQuotient<E: PairingEngine> {
    g1_m: E::G1Affine,
    g1_m_div_w: E::G1Affine,
    g1_q_m: E::G1Affine,
}

// Compute [M(tau)]_1, [M(tau / w)]_1, and [Q_M(tau)]_1
fn multiplicity_polynomials_and_quotient_g1<E: PairingEngine>(
    multiplicities: &BTreeMap<usize, usize>,
    g1_l_w_list: &[E::G1Affine],
    g1_l_w_div_w_list: &[E::G1Affine],
    g1_q3_list: &[E::G1Affine],
    g1_q4_list: &[E::G1Affine],
    segment_size: usize,
) -> MultiplicityPolynomialsAndQuotient<E> {
    let mut g1_m_proj = E::G1Projective::zero(); // [M(tau)]_1
    let mut g1_m_div_w_proj = E::G1Projective::zero(); // [M(tau / w)]_1
    let mut g1_q_m_proj = E::G1Projective::zero(); // [Q_M(tau)]_1
    for (&i, &m) in multiplicities.iter() {
        let segment_element_indices = i * segment_size..(i + 1) * segment_size;
        let multiplicity_fr = E::Fr::from(m as u64);
        for elem_index in segment_element_indices {
            // Linear combination of [L^W_i(tau)]_1
            g1_m_proj = g1_l_w_list[elem_index].mul(multiplicity_fr).add(g1_m_proj);
            // Linear combination of [L^W_i(tau / w)]_1
            g1_m_div_w_proj = g1_l_w_div_w_list[elem_index]
                .mul(multiplicity_fr)
                .add(g1_m_div_w_proj);
            // Linear combination of q_{i, 3}
            g1_q_m_proj = g1_q3_list[elem_index].mul(multiplicity_fr).add(g1_q_m_proj);
            // Linear combination of q_{i, 4}
            g1_q_m_proj = g1_q4_list[elem_index]
                .mul(-multiplicity_fr) // negate the coefficient
                .add(g1_q_m_proj);
        }
    }

    MultiplicityPolynomialsAndQuotient {
        g1_m: g1_m_proj.into_affine(),
        g1_m_div_w: g1_m_div_w_proj.into_affine(),
        g1_q_m: g1_q_m_proj.into_affine(),
    }
}

// Index polynomials and the quotients,
// containing [L(tau)]_1, [L(tau * v)]_1, [D(tau)]_1, [Q_L(tau)]_1, and [Q_D(tau)]_1.
struct IndexPolynomialsAndQuotients<E: PairingEngine> {
    g1_l: E::G1Affine,
    g1_l_mul_v: E::G1Affine,
    g1_d: E::G1Affine,
    poly_d: DensePolynomial<E::Fr>,
    g1_q_l: E::G1Affine,
    g1_q_d: E::G1Affine,
}

// Compute the commitments of [L(tau)]_1, [L(tau*v)]_1, [D(tau)]_1, [Q_L(tau)]_1, and [Q_D(tau)]_1
fn index_polynomials_and_quotients_g1<E: PairingEngine>(
    domain_w: &Radix2EvaluationDomain<E::Fr>,
    domain_k: &Radix2EvaluationDomain<E::Fr>,
    domain_v: &Radix2EvaluationDomain<E::Fr>,
    g1_l_v_list: &[E::G1Affine],
    g1_l_v_mul_v_list: &[E::G1Affine],
    g1_srs: &[E::G1Affine],
    queried_segment_indices: &[usize],
    witness_size: usize,
    segment_size: usize,
    num_queries: usize,
) -> IndexPolynomialsAndQuotients<E> {
    let mut poly_eval_list_l: Vec<E::Fr> = Vec::with_capacity(witness_size);
    let mut g1_l_proj = E::G1Projective::zero(); // [L(tau)]_1
    let mut g1_l_mul_v_proj = E::G1Projective::zero(); // [L(tau * v)]_1
    let roots_of_unity_w: Vec<E::Fr> = domain_w.elements().collect();
    let mut witness_element_index: usize = 0;
    let mut poly_eval_list_d: Vec<E::Fr> = Vec::with_capacity(num_queries);
    for &seg_index in queried_segment_indices.iter() {
        let segment_element_indices = seg_index * segment_size..(seg_index + 1) * segment_size;
        for j in segment_element_indices {
            let root_of_unity_w = roots_of_unity_w[j];
            poly_eval_list_l.push(root_of_unity_w);
            // Linear combination of [L^V_i(tau)]_1
            g1_l_proj = g1_l_v_list[witness_element_index]
                .mul(root_of_unity_w)
                .add(g1_l_proj);
            // Linear combination of [L^V_i(tau * v)]_1
            g1_l_mul_v_proj = g1_l_v_mul_v_list[witness_element_index]
                .mul(root_of_unity_w)
                .add(g1_l_mul_v_proj);
            witness_element_index += 1;
        }

        let root_of_unity_w = roots_of_unity_w[seg_index * segment_size];
        poly_eval_list_d.push(root_of_unity_w);
    }

    let poly_coeff_list_d = domain_k.ifft(&poly_eval_list_d);
    let poly_d = DensePolynomial::from_coefficients_vec(poly_coeff_list_d);
    let g1_d = Kzg::<E>::commit_g1(g1_srs, &poly_d).into_affine();

    // Compute the quotient polynomial Q_L(X) s.t. (X^k - 1)*(L(Xv) - w*L(X)) = Z_V(X)*Q_L(X),
    // Inverse FFT costs O(ks log(ks)) operations
    let poly_coeff_list_l = domain_v.ifft(&poly_eval_list_l);
    // The coefficients of L(Xv). We can scale each L(X) polynomial coefficients by v^i
    let domain_v_elements: Vec<E::Fr> = domain_v.elements().collect();
    let poly_coeff_list_l_mul_v: Vec<E::Fr> = poly_coeff_list_l
        .iter()
        .enumerate()
        .map(|(i, &c)| c * domain_v_elements[i])
        .collect();
    let poly_l_mul_v = DensePolynomial::from_coefficients_vec(poly_coeff_list_l_mul_v);
    // The coefficients of w*L(X).
    let domain_w_generator = roots_of_unity_w[1];
    let poly_coeff_list_w_mul_l: Vec<E::Fr> = poly_coeff_list_l
        .iter()
        .map(|&c| c * domain_w_generator)
        .collect();
    let poly_w_mul_l = DensePolynomial::from_coefficients_vec(poly_coeff_list_w_mul_l);
    // The coefficients of f(X) = X^k - 1
    let mut poly_coeff_list_x_pow_k_sub_one = vec![E::Fr::zero(); witness_size];
    poly_coeff_list_x_pow_k_sub_one[num_queries] = E::Fr::one();
    poly_coeff_list_x_pow_k_sub_one[0] = -E::Fr::one();
    let poly_x_pow_k_sub_one =
        DensePolynomial::from_coefficients_vec(poly_coeff_list_x_pow_k_sub_one);
    let vanishing_poly_v: DensePolynomial<E::Fr> = domain_v.vanishing_polynomial().into();
    let mut poly_q_l = poly_l_mul_v.sub(&poly_w_mul_l);
    poly_q_l = poly_q_l.div(&vanishing_poly_v);
    poly_q_l = poly_q_l.mul(&poly_x_pow_k_sub_one);
    let g1_q_l = Kzg::<E>::commit_g1(&g1_srs, &poly_q_l).into_affine();

    // Compute Q_D s.t. L(X) - D(X) = Z_K(X)*Q_D(X).
    let poly_l = DensePolynomial::from_coefficients_vec(poly_coeff_list_l);
    let mut poly_q_d = poly_l.sub(&poly_d);
    let vanishing_poly_k: DensePolynomial<E::Fr> = domain_k.vanishing_polynomial().into();
    poly_q_d = poly_q_d.div(&vanishing_poly_k);
    let g1_q_d = Kzg::<E>::commit_g1(&g1_srs, &poly_q_d).into_affine();

    IndexPolynomialsAndQuotients {
        g1_l: g1_l_proj.into_affine(),
        g1_l_mul_v: g1_l_mul_v_proj.into_affine(),
        g1_d,
        poly_d,
        g1_q_l,
        g1_q_d,
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Neg;

    use super::*;
    use crate::table::{rand_segments, Table};
    use ark_bn254::Bn254;
    use ark_ff::Field;
    use ark_std::rand::RngCore;
    use ark_std::{test_rng, UniformRand};

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
        let multiplicities =
            segment_multiplicities(&queried_segment_indices, num_segments).unwrap();
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
        let pp =
            PublicParameters::<Bn254>::setup(&mut rng, num_segments, num_queries, segment_size)
                .unwrap();
        let queried_segment_indices = vec![0, 1, 2, 3, 0, 1, 2, 3];
        let multiplicities =
            segment_multiplicities(&queried_segment_indices, num_segments).unwrap();

        // Construct polynomial M(X) using Inverse FFT.
        let mut poly_eval_m_list = vec![Fr::zero(); pp.table_size];
        for (&i, &m) in multiplicities.iter() {
            let segment_element_indices = i * segment_size..(i + 1) * segment_size;
            let fr_multiplicity = Fr::from(m as u64);
            for j in segment_element_indices {
                poly_eval_m_list[j] = fr_multiplicity;
            }
        }
        let poly_coeff_list_m = pp.domain_w.ifft(&poly_eval_m_list);
        let poly_m = DensePolynomial::from_coefficients_vec(poly_coeff_list_m.clone());
        let g1_m_expected = Kzg::<Bn254>::commit_g1(&pp.g1_srs, &poly_m).into_affine();
        let inv_generator_domain_w = pp.domain_w.group_gen_inv;
        let poly_coeff_list_m_div_w: Vec<Fr> = poly_coeff_list_m
            .iter()
            .enumerate()
            .map(|(i, &c)| c * inv_generator_domain_w.pow(&[i as u64]))
            .collect();
        let poly_m_div_w = DensePolynomial::from_coefficients_vec(poly_coeff_list_m_div_w);
        let g1_m_div_w_expected = Kzg::<Bn254>::commit_g1(&pp.g1_srs, &poly_m_div_w).into_affine();

        let mut poly_coeff_list_x_pow_n_sub_one = vec![Fr::zero(); pp.table_size];
        poly_coeff_list_x_pow_n_sub_one[pp.num_segments] = Fr::one();
        poly_coeff_list_x_pow_n_sub_one[0] = -Fr::one();
        let poly_x_pow_n_sub_one =
            DensePolynomial::from_coefficients_vec(poly_coeff_list_x_pow_n_sub_one);
        let mut poly_q_m = poly_m.clone();
        poly_q_m = poly_q_m.sub(&poly_m_div_w);
        poly_q_m = poly_q_m.naive_mul(&poly_x_pow_n_sub_one);
        poly_q_m = poly_q_m.div(&pp.domain_w.vanishing_polynomial().into());
        let g1_q_m_expected = Kzg::<Bn254>::commit_g1(&pp.g1_srs, &poly_q_m).into_affine();

        let MultiplicityPolynomialsAndQuotient {
            g1_m: g1_m_got,
            g1_m_div_w: g1_m_div_w_got,
            g1_q_m: g1_q_m_got,
        } = multiplicity_polynomials_and_quotient_g1::<Bn254>(
            &multiplicities,
            &pp.g1_l_w_list,
            &pp.g1_l_w_div_w_list,
            &pp.g1_q3_list,
            &pp.g1_q4_list,
            segment_size,
        );

        assert_eq!(g1_m_expected, g1_m_got);
        assert_eq!(g1_m_div_w_expected, g1_m_div_w_got);
        assert_eq!(g1_q_m_expected, g1_q_m_got);
    }

    // TODO: add test cases with different parameters,
    // e.g., (8, 4, 4), (4, 8, 4).

    #[test]
    fn test_prove() {
        let mut rng = test_rng();
        let pp =
            PublicParameters::setup(&mut rng, 16, 8, 4).expect("Failed to setup public parameters");
        let segments = rand_segments::generate(&pp);
        let segment_slices: Vec<&[<Bn254 as PairingEngine>::Fr]> =
            segments.iter().map(|segment| segment.as_slice()).collect();
        let t = Table::<Bn254>::new(&pp, &segment_slices).expect("Failed to create table");

        let queried_segment_indices: Vec<usize> = (0..pp.num_queries)
            .map(|_| rng.next_u32() as usize % pp.num_segments)
            .collect();

        let witness = Witness::new(&pp, &t, &queried_segment_indices).unwrap();

        let mut transcript = Transcript::<<Bn254 as PairingEngine>::Fr>::new();

        let rng = &mut test_rng();

        prove::<Bn254>(&pp, &mut transcript, &witness, rng).unwrap();
    }
}
