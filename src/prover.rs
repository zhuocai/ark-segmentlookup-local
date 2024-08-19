use std::collections::BTreeMap;
use std::ops::{Add, Mul, Sub};

use crate::domain::roots_of_unity;
use crate::error::Error;
use crate::kzg::Kzg;
use crate::multi_unity::{multi_unity_prove, MultiUnityProof};
use crate::public_parameters::PublicParameters;
use crate::table::{Table, TablePreprocessedParameters};
use crate::transcript::{Label, Transcript};
use crate::witness::Witness;
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::Field;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, Polynomial, Radix2EvaluationDomain, UVPolynomial};
use ark_std::rand::prelude::StdRng;
use ark_std::{One, Zero};

pub struct Proof<E: PairingEngine> {
    pub(crate) g1_m: E::G1Affine,       // [M(tau)]_1
    pub(crate) g1_m_div_w: E::G1Affine, // [M(tau / w)]_1
    pub(crate) g1_qm: E::G1Affine,      // [Q_M(tau)]_1
    pub(crate) g1_l: E::G1Affine,       // [L(tau)]_1
    pub(crate) g1_l_div_v: E::G1Affine, // [L(tau / v)]_1
    pub(crate) g1_ql: E::G1Affine,      // [Q_L(tau)]_1
    pub(crate) g1_d: E::G1Affine,       // [D(tau)]_1
    pub(crate) g1_qd: E::G1Affine,      // [Q_D(tau)]_1
    pub(crate) g1_a: E::G1Affine,       // [A(tau)]_1
    pub(crate) g1_qa: E::G1Affine,      // [Q_A(tau)]_1
    pub(crate) g1_qb: E::G1Affine,      // [Q_B(tau)]_1
    pub(crate) g1_a0: E::G1Affine,      // [A_0(tau)]_1
    pub(crate) g1_b0: E::G1Affine,      // [B_0(tau)]_1
    pub(crate) g1_px: E::G1Affine,      // [P_A(tau)]_1 or [P_B(tau)]_1 or zero
    pub(crate) g1_hp: E::G1Affine,      // [H_P(tau)]_1

    pub(crate) fr_b0_at_gamma: E::Fr, // b_{0,gamma} = B_0(gamma)
    pub(crate) fr_f_at_gamma: E::Fr,  // f_{gamma} = F(gamma)
    pub(crate) fr_l_at_gamma: E::Fr,  // l_{gamma} = L(gamma)
    pub(crate) fr_a_at_zero: E::Fr,   // a_0 = A(0)
    pub(crate) fr_l_at_gamma_div_v: E::Fr, // l_{gamma,v} = L(gamma / v)
    pub(crate) fr_ql_at_gamma: E::Fr, // q_{gamma,L} = Q_L(gamma)
    pub(crate) fr_d_at_gamma: E::Fr,  // d_{gamma} = D(gamma)
    pub(crate) fr_qd_at_gamma: E::Fr, // q_{gamma, D} = Q_D(gamma)

    pub(crate) multi_unity_proof: MultiUnityProof<E>, // Proof of the Caulk Sub-protocol
}

pub fn prove<E: PairingEngine>(
    pp: &PublicParameters<E>,
    table: &Table<E>,
    tpp: &TablePreprocessedParameters<E>,
    witness: &Witness<E>,
    rng: &mut StdRng,
) -> Result<Proof<E>, Error> {
    let mut transcript = Transcript::<E::Fr>::new();

    // Round 1-1: Compute the multiplicity polynomial M of degree (ns - 1),
    // and send [M(tau)]_1 and [M(tau / w)]_1 to the verifier.
    // Round 1-2: Compute and send [Q_M(tau)]_1 using the SRS and Lemma 4.
    let segment_multiplicities =
        segment_multiplicities(&witness.queried_segment_indices, pp.num_table_segments)?;
    let MultiplicityPolynomialsAndQuotient {
        g1_m,
        g1_m_div_w,
        g1_qm,
    } = multiplicity_polynomials_and_quotient_g1::<E>(
        &segment_multiplicities,
        &pp.g1_l_w_list,
        &pp.g1_q3_list,
        pp.segment_size,
        pp.table_element_size,
    );

    transcript.append_elements(&[
        (Label::G1M, g1_m),
        (Label::G1MDivW, g1_m_div_w),
        (Label::G1Qm, g1_qm),
    ])?;

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
        g1_l_div_v,
        g1_d,
        g1_ql,
        g1_qd,
        poly_l,
        poly_ql,
        poly_l_div_v,
        poly_eval_list_l,
        poly_coset_eval_list_l,
        poly_d,
        poly_qd,
    } = index_polynomials_and_quotients_g1::<E>(
        &pp.domain_w,
        &pp.domain_k,
        &pp.domain_v,
        &pp.g1_l_v_list,
        &pp.g1_srs,
        &witness.queried_segment_indices,
        pp.witness_element_size,
        pp.segment_size,
        pp.num_witness_segments,
    )?;

    transcript.append_elements(&[
        (Label::G1L, g1_l),
        (Label::G1LDivV, g1_l_div_v),
        (Label::G1Ql, g1_ql),
        (Label::G1D, g1_d),
        (Label::G1Qd, g1_qd),
    ])?;

    // Round 2 is performed by the verifier.

    // Round 3 - Round 8:
    // Using the instantiation of Lemma 5,
    // the prover and verifier engage in a protocol that polynomial L is well-formed.
    let multi_unity_proof = multi_unity_prove(pp, &mut transcript, &poly_d, &g1_d, rng)?;

    // Round 9: The verifier sends random scalar fields beta, delta to the prover.
    // Use Fiat-Shamir heuristic to make the protocol non-interactive.
    let beta = transcript.get_and_append_challenge(Label::ChallengeBeta)?;
    let delta = transcript.get_and_append_challenge(Label::ChallengeDelta)?;

    // Round 10-1: The prover computes A(X) of degree ns-1 in sparse form,
    // and sends [A(tau)]_1 to the verifier.
    // Round 10-2: The prover computes [Q_A(tau)]_1 using the SRS and Lemma 4.
    let mut sparse_poly_eval_list_a = BTreeMap::<usize, E::Fr>::default();
    let mut g1_proj_a = E::G1Projective::zero();
    let mut g1_proj_qa = E::G1Projective::zero();
    let roots_of_unity_w = roots_of_unity::<E>(&pp.domain_w);

    for (&segment_index, &multiplicity) in segment_multiplicities.iter() {
        let segment_element_indices =
            segment_index * pp.segment_size..(segment_index + 1) * pp.segment_size;
        for elem_index in segment_element_indices {
            let fr_a_i = (beta + table.values[elem_index] + delta * roots_of_unity_w[elem_index])
                .inverse()
                .ok_or(Error::FailedToInverseFieldElement)?
                * E::Fr::from(multiplicity as u64);

            sparse_poly_eval_list_a.insert(elem_index, fr_a_i);
            g1_proj_a = g1_proj_a + pp.g1_l_w_list[elem_index].mul(fr_a_i);
            g1_proj_qa = g1_proj_qa + tpp.g1_q1_list[elem_index].mul(fr_a_i);
            g1_proj_qa = g1_proj_qa + pp.g1_q2_list[elem_index].mul(delta.mul(fr_a_i));
        }
    }

    let g1_a = g1_proj_a.into_affine();
    let g1_qa = g1_proj_qa.into_affine();

    // Round 10-3: The prover computes B(X) of degree ks-1.
    let poly_eval_list_b: Result<Vec<E::Fr>, Error> = (0..pp.witness_element_size)
        .map(|i| {
            (beta + witness.poly_eval_list_f[i] + delta * poly_eval_list_l[i])
                .inverse()
                .ok_or(Error::FailedToInverseFieldElement)
        })
        .collect();
    let poly_eval_list_b = poly_eval_list_b?;
    let poly_coeff_list_b = pp.domain_v.ifft(&poly_eval_list_b);
    let poly_b = DensePolynomial::from_coefficients_vec(poly_coeff_list_b);

    // Round 10-4: The prover computes [Q_B(tau)]_1 using the SRS and Lemma 4.
    let poly_coset_eval_list_b = pp.domain_v.coset_fft(&poly_b);
    let poly_coset_eval_list_f = pp.domain_v.coset_fft(&witness.poly_f);
    let fr_one = E::Fr::one();
    let mut poly_coset_eval_list_qb: Vec<E::Fr> = poly_coset_eval_list_b
        .iter()
        .zip(poly_coset_eval_list_f.iter())
        .zip(poly_coset_eval_list_l.iter())
        .map(|((&b_i, &f_i), &l_i)| (b_i * (beta + f_i + delta * l_i)) - fr_one)
        .collect();
    pp.domain_v
        .divide_by_vanishing_poly_on_coset_in_place(&mut poly_coset_eval_list_qb);
    let poly_coeff_list_qb = pp.domain_v.coset_ifft(&poly_coset_eval_list_qb);
    let poly_qb = DensePolynomial::from_coefficients_vec(poly_coeff_list_qb);
    let g1_qb = Kzg::<E>::commit_g1(&pp.g1_srs, &poly_qb).into_affine();

    // Round 10-5: The prover computes A_0(X) = (A(X) - A(0)) / X, B_0(X) = (B(X) - B(0)) / X,
    // and sends [A_0(tau)]_1 and [B_0(tau)]_1 to the verifier.
    let mut g1_proj_a0 = E::G1Projective::zero();
    for (&i, &a_i) in sparse_poly_eval_list_a.iter() {
        g1_proj_a0 = g1_proj_a0 + pp.g1_l_w_opening_proofs_at_zero[i].mul(a_i);
    }
    let g1_a0 = g1_proj_a0.into_affine();
    let poly_b0 = DensePolynomial::from_coefficients_slice(&poly_b.coeffs[1..]);
    let g1_b0 = Kzg::<E>::commit_g1(&pp.g1_srs, &poly_b0).into_affine();

    // Round 10-6: Degree check.
    // This step is only necessary when k != n.
    let mut g1_px = E::G1Affine::zero();
    if pp.num_table_segments > pp.num_witness_segments {
        // If n > k, the prover computes P_B(X) and sends [P_B(tau)]_1 to the verifier.
        let coeff_shift = (pp.num_table_segments - pp.num_witness_segments) * pp.segment_size - 1;
        let mut poly_coeff_list_pb = vec![E::Fr::zero(); coeff_shift];
        poly_coeff_list_pb.extend_from_slice(&poly_b0.coeffs);
        let poly_pb = DensePolynomial::from_coefficients_vec(poly_coeff_list_pb);
        g1_px = Kzg::<E>::commit_g1(&pp.g1_srs, &poly_pb).into_affine();
    } else if pp.num_table_segments < pp.num_witness_segments {
        // If n < k, the prover computes P_A(X) and sends [P_A(tau)]_1 to the verifier.
        // We can use Inverse FFT to compute the polynomial A(X),
        // since the runtime does not exceed O(ks log ks) as n < k.
        let mut poly_eval_list_a = vec![E::Fr::zero(); pp.table_element_size];
        for (&i, &a_i) in sparse_poly_eval_list_a.iter() {
            poly_eval_list_a[i] = a_i;
        }
        let poly_coeff_list_a = pp.domain_w.ifft(&poly_eval_list_a);
        let poly_coeff_list_a0 = poly_coeff_list_a[1..].to_vec();
        let coeff_shift = (pp.num_witness_segments - pp.num_table_segments) * pp.segment_size - 1;
        let mut poly_coeff_list_pa = vec![E::Fr::zero(); coeff_shift];
        poly_coeff_list_pa.extend_from_slice(&poly_coeff_list_a0);
        let poly_pa = DensePolynomial::from_coefficients_vec(poly_coeff_list_pa);
        g1_px = Kzg::<E>::commit_g1(&pp.g1_srs, &poly_pa).into_affine();
    }

    transcript.append_elements(&[
        (Label::G1A, g1_a),
        (Label::G1Qa, g1_qa),
        (Label::G1Qb, g1_qb),
        (Label::G1A0, g1_a0),
        (Label::G1B0, g1_b0),
        (Label::G1Px, g1_px),
    ])?;

    // Round 11-3: The verifier sends random scalar gamma to the prover.
    // Use Fiat-Shamir heuristic to make the protocol non-interactive.
    let gamma = transcript.get_and_append_challenge(Label::ChallengeGamma)?;

    // Round 12: The prover sends b_{0,gamma} = B_0(gamma), f_{gamma} = F(gamma),
    // l_{gamma} = L(gamma), a_0 = A(0), l_{gamma,v} = L(v*gamma), q_{gamma,L} = Q_L(gamma),
    // d_{gamma} = D(gamma), and q_{gamma, D} = Q_D(gamma) to the verifier.
    let fr_b0_at_gamma = poly_b0.evaluate(&gamma);
    let fr_f_at_gamma = witness.poly_f.evaluate(&gamma);
    let fr_l_at_gamma = poly_l.evaluate(&gamma);
    // Compute a_0 using sumcheck lemma.
    let fr_a_at_zero = {
        let fr_b_at_zero = poly_b.evaluate(&E::Fr::zero());
        let table_elem_size = pp.num_table_segments * pp.segment_size;
        let fr_inv_table_elem_size = E::Fr::from(table_elem_size as u64)
            .inverse()
            .ok_or(Error::FailedToInverseFieldElement)?;
        let witness_elem_size = pp.num_witness_segments * pp.segment_size;
        let fr_witness_elem_size = E::Fr::from(witness_elem_size as u64);

        fr_b_at_zero * fr_witness_elem_size * fr_inv_table_elem_size
    };
    let fr_gamma_div_v = gamma / pp.domain_v.group_gen;
    let fr_l_at_gamma_div_v = poly_l.evaluate(&fr_gamma_div_v);
    let fr_ql_at_gamma = poly_ql.evaluate(&gamma);
    let fr_d_at_gamma = poly_d.evaluate(&gamma);
    let fr_qd_at_gamma = poly_qd.evaluate(&gamma);

    transcript.append_elements(&[
        (Label::FrB0AtGamma, fr_b0_at_gamma),
        (Label::FrFAtGamma, fr_f_at_gamma),
        (Label::FrLAtGamma, fr_l_at_gamma),
        (Label::FrAAtZero, fr_a_at_zero),
        (Label::FrLAtGammaDivV, fr_l_at_gamma_div_v),
        (Label::FrQlAtGamma, fr_ql_at_gamma),
        (Label::FrDAtGamma, fr_d_at_gamma),
        (Label::FrQdAtGamma, fr_qd_at_gamma),
    ])?;

    // Round 11-3: Use Fiat-Shamir transform to sample eta.
    let eta = transcript.get_and_append_challenge(Label::ChallengeEta)?;

    // Round 14: Compute the commitment of H_P(X) = (P(X) - p_{gamma}) / (X - gamma),
    // which is a KZG batch opening proof of the polynomials to be checked,
    // and send [H_P(tau)]_1 to the verifier.
    let g1_hp = Kzg::<E>::batch_open_g1(
        &pp.g1_srs,
        &[
            poly_l_div_v,
            poly_l,
            poly_ql,
            poly_d,
            poly_qd,
            poly_b0,
            witness.poly_f.clone(),
            poly_qb,
        ],
        gamma,
        eta,
    );

    Ok(Proof {
        g1_m,
        g1_m_div_w,
        g1_qm,
        g1_l,
        g1_l_div_v,
        g1_ql,
        g1_d,
        g1_qd,
        g1_a,
        g1_qa,
        g1_qb,
        g1_a0,
        g1_b0,
        g1_px,
        g1_hp,

        fr_b0_at_gamma,
        fr_f_at_gamma,
        fr_l_at_gamma,
        fr_a_at_zero,
        fr_l_at_gamma_div_v,
        fr_ql_at_gamma,
        fr_d_at_gamma,
        fr_qd_at_gamma,

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
    g1_qm: E::G1Affine,
}

// Compute [M(tau)]_1, [M(tau / w)]_1, and [Q_M(tau)]_1.
fn multiplicity_polynomials_and_quotient_g1<E: PairingEngine>(
    segment_multiplicities: &BTreeMap<usize, usize>,
    g1_l_w_list: &[E::G1Affine],
    g1_q3_list: &[E::G1Affine],
    // g1_q4_list: &[E::G1Affine],
    segment_size: usize,
    table_element_size: usize,
) -> MultiplicityPolynomialsAndQuotient<E> {
    let mut g1_proj_m = E::G1Projective::zero(); // [M(tau)]_1
    let mut g1_proj_m_div_w = E::G1Projective::zero(); // [M(tau / w)]_1
    let mut g1_proj_qm = E::G1Projective::zero(); // [Q_M(tau)]_1
    for (&i, &m) in segment_multiplicities.iter() {
        let segment_element_indices = i * segment_size..(i + 1) * segment_size;
        let fr_mul = E::Fr::from(m as u64);
        for elem_index in segment_element_indices {
            // Linear combination of [L^W_i(tau)]_1.
            g1_proj_m = g1_l_w_list[elem_index].mul(fr_mul).add(g1_proj_m);
            // Linear combination of [L^W_i(tau / w)]_1.
            // L^W_i(tau / w) = L^W_{i+1}(tau).
            // We can shift [L^W_i(tau)]_1 to the left by 1 to get [L^W_i(tau / w)]_1.
            let shifted_elem_index = (elem_index + 1) % table_element_size;
            g1_proj_m_div_w = g1_l_w_list[shifted_elem_index]
                .mul(fr_mul)
                .add(g1_proj_m_div_w);
            // Linear combination of q_{i, 3}.
            g1_proj_qm = g1_q3_list[elem_index].mul(fr_mul).add(g1_proj_qm);
            // Linear combination of q_{i, 4}.
            // q_{i, 4} is equivalent to shift q_{i, 3} to the left by 1.
            let shifted_elem_index = (elem_index + 1) % table_element_size;
            g1_proj_qm = g1_q3_list[shifted_elem_index]
                .mul(-fr_mul) // negate the coefficient
                .add(g1_proj_qm);
        }
    }

    MultiplicityPolynomialsAndQuotient {
        g1_m: g1_proj_m.into_affine(),
        g1_m_div_w: g1_proj_m_div_w.into_affine(),
        g1_qm: g1_proj_qm.into_affine(),
    }
}

// Index polynomials and the quotients,
// containing [L(tau)]_1, [L(tau * v)]_1, [D(tau)]_1, [Q_L(tau)]_1, and [Q_D(tau)]_1.
struct IndexPolynomialsAndQuotients<E: PairingEngine> {
    g1_l: E::G1Affine,
    g1_l_div_v: E::G1Affine,
    g1_d: E::G1Affine,
    g1_ql: E::G1Affine,
    g1_qd: E::G1Affine,
    poly_l: DensePolynomial<E::Fr>,
    poly_ql: DensePolynomial<E::Fr>,
    poly_l_div_v: DensePolynomial<E::Fr>,
    poly_eval_list_l: Vec<E::Fr>,
    poly_coset_eval_list_l: Vec<E::Fr>,
    poly_d: DensePolynomial<E::Fr>,
    poly_qd: DensePolynomial<E::Fr>,
}

// Compute the commitments of [L(tau)]_1, [L(tau*v)]_1, [D(tau)]_1, [Q_L(tau)]_1, and [Q_D(tau)]_1.
fn index_polynomials_and_quotients_g1<E: PairingEngine>(
    domain_w: &Radix2EvaluationDomain<E::Fr>,
    domain_k: &Radix2EvaluationDomain<E::Fr>,
    domain_v: &Radix2EvaluationDomain<E::Fr>,
    g1_l_v_list: &[E::G1Affine],
    g1_srs: &[E::G1Affine],
    queried_segment_indices: &[usize],
    witness_size: usize,
    segment_size: usize,
    num_queries: usize,
) -> Result<IndexPolynomialsAndQuotients<E>, Error> {
    let mut poly_eval_list_l: Vec<E::Fr> = Vec::with_capacity(witness_size);
    let mut g1_proj_l = E::G1Projective::zero(); // [L(tau)]_1
    let mut g1_proj_l_div_v = E::G1Projective::zero(); // [L(tau / v)]_1
    let roots_of_unity_w: Vec<E::Fr> = roots_of_unity::<E>(&domain_w);
    let mut witness_element_index: usize = 0;
    let mut poly_eval_list_d: Vec<E::Fr> = Vec::with_capacity(num_queries);
    for &seg_index in queried_segment_indices.iter() {
        let segment_element_indices = seg_index * segment_size..(seg_index + 1) * segment_size;
        for elem_index in segment_element_indices {
            let root_of_unity_w = roots_of_unity_w[elem_index];
            poly_eval_list_l.push(root_of_unity_w);
            // Linear combination of [L^V_i(tau)]_1.
            g1_proj_l = g1_l_v_list[witness_element_index]
                .mul(root_of_unity_w)
                .add(g1_proj_l);
            // Linear combination of [L^V_i(tau / v)]_1.
            // L^V_i(tau / v) = L^V_{i+1}(tau).
            // We can shift [L^V_i(tau)]_1 to the left by 1
            // to get [L^V_i(tau / v)]_1.
            let shifted_witness_elem_index = (witness_element_index + 1) % witness_size;
            g1_proj_l_div_v = g1_l_v_list[shifted_witness_elem_index]
                .mul(root_of_unity_w)
                .add(g1_proj_l_div_v);
            witness_element_index += 1;
        }

        let root_of_unity_w = roots_of_unity_w[seg_index * segment_size];
        poly_eval_list_d.push(root_of_unity_w);
    }

    let poly_coeff_list_d = domain_k.ifft(&poly_eval_list_d);
    let poly_d = DensePolynomial::from_coefficients_vec(poly_coeff_list_d);
    let g1_d = Kzg::<E>::commit_g1(g1_srs, &poly_d).into_affine();

    // Compute the quotient polynomial Q_L(X) s.t. (X^k - 1) * (L(X) - w * L(X / v)) = Z_V(X) * Q_L(X),
    // Inverse FFT costs O(ks log(ks)) operations.
    let poly_coeff_list_l = domain_v.ifft(&poly_eval_list_l);
    // The coefficients of L(X / v).
    // We can divide each L(X) polynomial coefficients by v^i.
    let roots_of_unity_v: Vec<E::Fr> = roots_of_unity::<E>(&domain_v);
    let poly_coeff_list_l_div_v: Vec<E::Fr> = poly_coeff_list_l
        .iter()
        .enumerate()
        .map(|(i, &c)| c / roots_of_unity_v[i])
        .collect();
    let poly_l_div_v = DensePolynomial::from_coefficients_slice(&poly_coeff_list_l_div_v);
    // The coefficients of w * L(X / v).
    // We can multiply each L(X / v) polynomial coefficients by w.
    let generator_w = domain_w.group_gen;
    let poly_coeff_list_w_mul_l_div_v: Vec<E::Fr> = poly_coeff_list_l_div_v
        .iter()
        .map(|&c| c * generator_w)
        .collect();
    let poly_w_mul_l_div_v = DensePolynomial::from_coefficients_vec(poly_coeff_list_w_mul_l_div_v);
    // Compute y(X) = X^k - 1, which is the vanishing polynomial of Domain V.
    let poly_x_pow_k_sub_one = domain_k.vanishing_polynomial().into();
    let poly_l = DensePolynomial::from_coefficients_vec(poly_coeff_list_l);
    let mut poly_ql = poly_l.sub(&poly_w_mul_l_div_v);
    poly_ql = poly_ql.mul(&poly_x_pow_k_sub_one);
    let remainder: DensePolynomial<E::Fr>;
    (poly_ql, remainder) = poly_ql
        .divide_by_vanishing_poly(*domain_v)
        .ok_or(Error::FailedToDivideByVanishingPolynomial)?;
    if !remainder.is_zero() {
        return Err(Error::RemainderAfterDivisionIsNonZero);
    }
    let g1_ql = Kzg::<E>::commit_g1(&g1_srs, &poly_ql).into_affine();

    // Compute Q_D s.t. L(X) - D(X) = Z_K(X) * Q_D(X).
    let mut poly_qd = poly_l.sub(&poly_d);
    let remainder: DensePolynomial<E::Fr>;
    (poly_qd, remainder) = poly_qd
        .divide_by_vanishing_poly(*domain_k)
        .ok_or(Error::FailedToDivideByVanishingPolynomial)?;
    if !remainder.is_zero() {
        return Err(Error::RemainderAfterDivisionIsNonZero);
    }
    let g1_qd = Kzg::<E>::commit_g1(&g1_srs, &poly_qd).into_affine();

    let poly_coset_eval_list_l = domain_v.coset_fft(&poly_l);

    Ok(IndexPolynomialsAndQuotients {
        g1_l: g1_proj_l.into_affine(),
        g1_l_div_v: g1_proj_l_div_v.into_affine(),
        g1_d,
        g1_ql,
        g1_qd,
        poly_l,
        poly_ql,
        poly_l_div_v,
        poly_eval_list_l,
        poly_coset_eval_list_l,
        poly_d,
        poly_qd,
    })
}

#[cfg(test)]
mod tests {
    use std::ops::Neg;

    use super::*;
    use crate::table::rand_segments;
    use ark_bn254::Bn254;
    use ark_std::rand::RngCore;
    use ark_std::{test_rng, UniformRand};

    type Fr = <Bn254 as PairingEngine>::Fr;
    type G1Affine = <Bn254 as PairingEngine>::G1Affine;
    // type G2Affine = <Bn254 as PairingEngine>::G2Affine;

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
    fn test_multiplicity_polynomials_and_quotient_g1() {
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
        let mut poly_eval_m_list = vec![Fr::zero(); pp.table_element_size];
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
        let inv_generator_w = pp.domain_w.group_gen_inv;
        let poly_coeff_list_m_div_w: Vec<Fr> = poly_coeff_list_m
            .iter()
            .enumerate()
            .map(|(i, &c)| c * inv_generator_w.pow(&[i as u64]))
            .collect();
        let poly_m_div_w = DensePolynomial::from_coefficients_vec(poly_coeff_list_m_div_w);
        let g1_m_div_w_expected = Kzg::<Bn254>::commit_g1(&pp.g1_srs, &poly_m_div_w).into_affine();

        let mut poly_coeff_list_x_pow_n_sub_one = vec![Fr::zero(); pp.table_element_size];
        poly_coeff_list_x_pow_n_sub_one[pp.num_table_segments] = Fr::one();
        poly_coeff_list_x_pow_n_sub_one[0] = -Fr::one();
        let poly_x_pow_n_sub_one =
            DensePolynomial::from_coefficients_vec(poly_coeff_list_x_pow_n_sub_one);
        let mut poly_qm = poly_m.clone();
        poly_qm = poly_qm.sub(&poly_m_div_w);
        poly_qm = poly_qm.naive_mul(&poly_x_pow_n_sub_one);
        let remainder: DensePolynomial<Fr>;
        (poly_qm, remainder) = poly_qm.divide_by_vanishing_poly(pp.domain_w).unwrap();
        assert!(remainder.is_zero());
        let g1_qm_expected = Kzg::<Bn254>::commit_g1(&pp.g1_srs, &poly_qm).into_affine();

        let MultiplicityPolynomialsAndQuotient {
            g1_m: g1_m_got,
            g1_m_div_w: g1_m_div_w_got,
            g1_qm: g1_qm_got,
        } = multiplicity_polynomials_and_quotient_g1::<Bn254>(
            &multiplicities,
            &pp.g1_l_w_list,
            &pp.g1_q3_list,
            segment_size,
            pp.table_element_size,
        );

        assert_eq!(g1_m_expected, g1_m_got);
        assert_eq!(g1_m_div_w_expected, g1_m_div_w_got);
        assert_eq!(g1_qm_expected, g1_qm_got);
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
        let t = Table::<Bn254>::new(&pp, &segment_slices).unwrap();

        let queried_segment_indices: Vec<usize> = (0..pp.num_witness_segments)
            .map(|_| rng.next_u32() as usize % pp.num_table_segments)
            .collect();

        let witness = Witness::new(&pp, &t, &queried_segment_indices).unwrap();

        let tpp = t.preprocess(&pp).unwrap();

        let rng = &mut test_rng();

        prove::<Bn254>(&pp, &t, &tpp, &witness, rng).unwrap();
    }
}
