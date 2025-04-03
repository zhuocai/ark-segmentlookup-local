use crate::domain::{
    divide_by_vanishing_poly_checked, divide_by_vanishing_poly_on_coset_in_place, roots_of_unity,
};
use crate::error::Error;
use crate::kzg::Kzg;
use crate::multi_unity::{multi_unity_prove, MultiUnityProof};
use crate::public_parameters::PublicParameters;
use crate::table::TablePreprocessedParameters;
use crate::transcript::{Label, Transcript};
use crate::witness::Witness;
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Field;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, EvaluationDomain, Polynomial, Radix2EvaluationDomain};
use ark_std::rand::Rng;
use ark_std::{One, Zero};
use dashmap::DashMap;
use rayon::prelude::*;
use std::ops::{AddAssign, Mul};

pub struct Proof<P: Pairing> {
    pub(crate) g1_affine_m: P::G1Affine,       // [M(tau)]_1
    pub(crate) g1_affine_m_div_w: P::G1Affine, // [M(tau / w)]_1
    pub(crate) g1_affine_qm: P::G1Affine,      // [Q_M(tau)]_1
    pub(crate) g1_affine_l: P::G1Affine,       // [L(tau)]_1
    pub(crate) g1_affine_l_div_v: P::G1Affine, // [L(tau / v)]_1
    pub(crate) g1_affine_ql: P::G1Affine,      // [Q_L(tau)]_1
    pub(crate) g1_affine_d: P::G1Affine,       // [D(tau)]_1
    pub(crate) g1_affine_qd: P::G1Affine,      // [Q_D(tau)]_1
    pub(crate) g1_affine_a: P::G1Affine,       // [A(tau)]_1
    pub(crate) g1_affine_qa: P::G1Affine,      // [Q_A(tau)]_1
    pub(crate) g1_affine_qb: P::G1Affine,      // [Q_B(tau)]_1
    pub(crate) g1_affine_a0: P::G1Affine,      // [A_0(tau)]_1
    pub(crate) g1_affine_b0: P::G1Affine,      // [B_0(tau)]_1
    pub(crate) g1_affine_px: P::G1Affine,      // [P_A(tau)]_1 or [P_B(tau)]_1 or zero
    pub(crate) g1_affine_hp: P::G1Affine,      // [H_P(tau)]_1

    pub(crate) fr_b0_at_gamma: P::ScalarField, // b_{0,gamma} = B_0(gamma)
    pub(crate) fr_f_at_gamma: P::ScalarField,  // f_{gamma} = F(gamma)
    pub(crate) fr_l_at_gamma: P::ScalarField,  // l_{gamma} = L(gamma)
    pub(crate) fr_a_at_zero: P::ScalarField,   // a_0 = A(0)
    pub(crate) fr_l_at_gamma_div_v: P::ScalarField, // l_{gamma,v} = L(gamma / v)
    pub(crate) fr_ql_at_gamma: P::ScalarField, // q_{gamma,L} = Q_L(gamma)
    pub(crate) fr_d_at_gamma: P::ScalarField,  // d_{gamma} = D(gamma)
    pub(crate) fr_qd_at_gamma: P::ScalarField, // q_{gamma, D} = Q_D(gamma)

    pub(crate) multi_unity_proof: MultiUnityProof<P>, // Proof of the Caulk Sub-protocol
}

pub fn prove<P: Pairing, R: Rng + ?Sized>(
    pp: &PublicParameters<P>,
    tpp: &TablePreprocessedParameters<P>,
    witness: &Witness<P>,
    statement: P::G1Affine,
    rng: &mut R,
) -> Result<Proof<P>, Error> {
    let mut transcript = Transcript::<P::ScalarField>::new();
    transcript.append_elements(&[
        (Label::PublicParameters, pp.hash_representation.clone()),
        (
            Label::TablePreprocessedParameters,
            tpp.hash_representation.clone(),
        ),
    ])?;
    transcript.append_element(Label::Statement, &statement)?;

    // Round 1-1: Compute the multiplicity polynomial M of degree (ns - 1),
    // and send [M(tau)]_1 and [M(tau / w)]_1 to the verifier.
    // Round 1-2: Compute and send [Q_M(tau)]_1 using the SRS and Lemma 4.
    let segment_multiplicities =
        compute_segment_multiplicities(&witness.segment_indices, pp.num_table_segments)?;
    let MultiplicityPolynomialsAndQuotient {
        g1_affine_m,
        g1_affine_m_div_w,
        g1_affine_qm,
    } = compute_multiplicity_polynomials_and_quotient::<P>(
        &segment_multiplicities,
        &pp.g1_affine_list_lw,
        &pp.g1_affine_list_q3,
        pp.segment_size,
        pp.table_element_size,
    );

    transcript.append_elements(&[
        (Label::G1M, g1_affine_m),
        (Label::G1MDivW, g1_affine_m_div_w),
        (Label::G1Qm, g1_affine_qm),
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
    let roots_of_unity_w = roots_of_unity::<P>(&pp.domain_w);
    let roots_of_unity_v = roots_of_unity::<P>(&pp.domain_v);
    let domain_generator_w = pp.domain_w.group_gen;
    let IndexPolynomialsAndQuotients {
        g1_affine_l,
        g1_affine_l_div_v,
        g1_affine_d,
        g1_affine_ql,
        g1_affine_qd,
        poly_l,
        poly_ql,
        poly_l_div_v,
        poly_eval_list_l,
        poly_eval_list_d,
        poly_d,
        poly_qd,
    } = compute_index_polynomials_and_quotients::<P>(
        &pp.domain_k,
        &pp.domain_v,
        &pp.domain_coset_v,
        &roots_of_unity_w,
        &roots_of_unity_v,
        &pp.partial_inv_zk_at_coset_v_values,
        &pp.g1_affine_list_lv,
        &pp.g1_affine_srs,
        &witness.segment_indices,
        domain_generator_w,
        pp.witness_element_size,
        pp.segment_size,
    )?;

    transcript.append_elements(&[
        (Label::G1L, g1_affine_l),
        (Label::G1LDivV, g1_affine_l_div_v),
        (Label::G1Ql, g1_affine_ql),
        (Label::G1D, g1_affine_d),
        (Label::G1Qd, g1_affine_qd),
    ])?;

    // Round 2 is performed by the verifier.

    // Round 3 - Round 8:
    // Using the instantiation of Lemma 5,
    // the prover and verifier engage in a protocol that polynomial L is
    // well-formed.
    let multi_unity_proof = multi_unity_prove(
        pp,
        &mut transcript,
        &poly_eval_list_d,
        &poly_d,
        &g1_affine_d,
        rng,
    )?;

    // Round 9: The verifier sends random scalar fields beta, delta to the prover.
    // Use Fiat-Shamir heuristic to make the protocol non-interactive.
    let beta = transcript.squeeze_challenge(Label::ChallengeBeta)?;
    let delta = transcript.squeeze_challenge(Label::ChallengeDelta)?;

    // Round 10-1: The prover computes A(X) of degree ns-1 in sparse form,
    // and sends [A(tau)]_1 to the verifier.
    // Round 10-2: The prover computes [Q_A(tau)]_1 using the SRS and Lemma 4.
    // Round 10-5: The prover computes A_0(X) = (A(X) - A(0)) / X,
    // and sends [A_0(tau)]_1 to the verifier.
    let PolynomialAAndQuotient {
        g1_affine_a,
        g1_affine_qa,
        g1_affine_a0,
        sparse_poly_eval_list_a,
    }: PolynomialAAndQuotient<P> = compute_polynomial_a_and_quotient(
        beta,
        delta,
        &tpp.adjusted_table_values,
        &segment_multiplicities,
        pp.segment_size,
        &roots_of_unity_w,
        &pp.g1_affine_list_lw,
        &tpp.g1_affine_list_q1,
        &pp.g1_affine_list_q2,
        &pp.g1_affine_lw_opening_proofs_at_zero,
    )?;

    // Round 10-3: The prover computes B(X) of degree ks-1.
    // Round 10-4: The prover computes [Q_B(tau)]_1 using the SRS and Lemma 4.
    // Round 10-5: The prover computes B_0(X) = (B(X) - B(0)) / X,
    // and sends [B_0(tau)]_1 to the verifier.
    let PolynomialBAndQuotient {
        poly_b,
        poly_qb,
        poly_b0,
        g1_affine_qb,
        g1_affine_b0,
    } = compute_polynomial_b_and_quotient(
        beta,
        delta,
        &witness,
        pp.witness_element_size,
        &pp.domain_v,
        &pp.domain_coset_v,
        &poly_eval_list_l,
        &poly_l,
        &pp.g1_affine_srs,
    )?;

    // Round 10-6: Degree check.
    // This step is only necessary when k != n.
    let g1_affine_px = compute_degree_check_g1_affine::<P>(
        pp.num_table_segments,
        pp.num_witness_segments,
        pp.segment_size,
        pp.table_element_size,
        &poly_b0,
        &pp.g1_affine_srs,
        &sparse_poly_eval_list_a,
        &pp.domain_w,
    );

    transcript.append_elements(&[
        (Label::G1A, g1_affine_a),
        (Label::G1Qa, g1_affine_qa),
        (Label::G1Qb, g1_affine_qb),
        (Label::G1A0, g1_affine_a0),
        (Label::G1B0, g1_affine_b0),
        (Label::G1Px, g1_affine_px),
    ])?;

    // Round 11-3: The verifier sends random scalar gamma to the prover.
    // Use Fiat-Shamir heuristic to make the protocol non-interactive.
    let gamma = transcript.squeeze_challenge(Label::ChallengeGamma)?;

    // Round 12: The prover sends b_{0,gamma} = B_0(gamma), f_{gamma} = F(gamma),
    // l_{gamma} = L(gamma), a_0 = A(0), l_{gamma,v} = L(v*gamma), q_{gamma,L}
    // = Q_L(gamma), d_{gamma} = D(gamma), and q_{gamma, D} = Q_D(gamma)
    // to the verifier.
    let fr_b0_at_gamma = poly_b0.evaluate(&gamma);
    let fr_f_at_gamma = witness.poly.evaluate(&gamma);
    let fr_l_at_gamma = poly_l.evaluate(&gamma);
    // Compute a_0 using sumcheck lemma.
    let fr_a_at_zero = {
        let fr_b_at_zero = poly_b.evaluate(&P::ScalarField::zero());
        let table_elem_size = pp.num_table_segments * pp.segment_size;
        let fr_inv_table_elem_size = P::ScalarField::from(table_elem_size as u64)
            .inverse()
            .ok_or(Error::FailedToInverseFieldElement)?;
        let witness_elem_size = pp.num_witness_segments * pp.segment_size;
        let fr_witness_elem_size = P::ScalarField::from(witness_elem_size as u64);

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
    let eta = transcript.squeeze_challenge(Label::ChallengeEta)?;

    // Round 14: Compute the commitment of H_P(X)
    // = (P(X) - p_{gamma}) / (X - gamma),
    // which is a KZG batch opening proof of the polynomials to be
    // checked, and send [H_P(tau)]_1 to the verifier.
    let g1_affine_hp = Kzg::<P::G1>::batch_open(
        &pp.g1_affine_srs,
        &[
            poly_l_div_v,
            poly_l,
            poly_ql,
            poly_d,
            poly_qd,
            poly_b0,
            witness.poly.clone(),
            poly_qb,
        ],
        gamma,
        eta,
    );

    Ok(Proof {
        g1_affine_m,
        g1_affine_m_div_w,
        g1_affine_qm,
        g1_affine_l,
        g1_affine_l_div_v,
        g1_affine_ql,
        g1_affine_d,
        g1_affine_qd,
        g1_affine_a,
        g1_affine_qa,
        g1_affine_qb,
        g1_affine_a0,
        g1_affine_b0,
        g1_affine_px,
        g1_affine_hp,

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

fn compute_segment_multiplicities(
    queried_segment_indices: &[usize],
    num_segments: usize,
) -> Result<DashMap<usize, usize>, Error> {
    let multiplicities = DashMap::new();

    queried_segment_indices.par_iter().try_for_each(|&i| {
        if i >= num_segments {
            return Err(Error::InvalidSegmentIndex(i));
        }

        multiplicities
            .entry(i)
            .and_modify(|count| *count += 1)
            .or_insert(1);

        Ok(())
    })?;

    Ok(multiplicities)
}

// Multiplicity polynomials and the quotient,
// containing [M(tau)]_1, [M(tau / w)]_1, and [Q_M(tau)]_1.
struct MultiplicityPolynomialsAndQuotient<P: Pairing> {
    g1_affine_m: P::G1Affine,
    g1_affine_m_div_w: P::G1Affine,
    g1_affine_qm: P::G1Affine,
}

fn compute_multiplicity_polynomials_and_quotient<P: Pairing>(
    segment_multiplicities: &DashMap<usize, usize>,
    g1_affine_list_lw: &[P::G1Affine],
    g1_affine_list_q3: &[P::G1Affine],
    segment_size: usize,
    table_element_size: usize,
) -> MultiplicityPolynomialsAndQuotient<P> {
    // Compute partial [M(tau)]_1, [M(tau / w)]_1, and [Q_M(tau)]_1 in parallel.
    let (g1_m, g1_m_div_w, g1_qm) = segment_multiplicities
        .par_iter()
        .map(|entry| {
            let i = *entry.key();
            let m = *entry.value();
            let mut g1_m_partial = P::G1::zero();
            let mut g1_m_div_w_partial = P::G1::zero();
            let mut g1_qm_partial = P::G1::zero();
            let segment_element_indices = i * segment_size..(i + 1) * segment_size;
            let fr_mul = P::ScalarField::from(m as u64);
            for elem_index in segment_element_indices {
                // Linear combination of [L^W_i(tau)]_1.
                g1_m_partial.add_assign(g1_affine_list_lw[elem_index].mul(fr_mul));
                // Linear combination of [L^W_i(tau / w)]_1.
                // L^W_i(tau / w) = L^W_{i+1}(tau).
                let shifted_elem_index = (elem_index + 1) % table_element_size;
                g1_m_div_w_partial.add_assign(g1_affine_list_lw[shifted_elem_index].mul(fr_mul));
                // Linear combination of q_{i, 3}.
                g1_qm_partial.add_assign(g1_affine_list_q3[elem_index].mul(fr_mul));
                // Linear combination of q_{i, 4}.
                // q_{i, 4} is equivalent to shift q_{i, 3} to the left by 1.
                let shifted_elem_index = (elem_index + 1) % table_element_size;
                // Negate the coefficient of multiplicity.
                g1_qm_partial.add_assign(g1_affine_list_q3[shifted_elem_index].mul(-fr_mul));
            }

            (g1_m_partial, g1_m_div_w_partial, g1_qm_partial)
        })
        .reduce(
            || (P::G1::zero(), P::G1::zero(), P::G1::zero()),
            |(g1_m1, g1_m_div_w1, g1_qm1), (g1_m2, g1_m_div_w2, g1_qm2)| {
                (g1_m1 + g1_m2, g1_m_div_w1 + g1_m_div_w2, g1_qm1 + g1_qm2)
            },
        );

    let g1_affine_list = P::G1::normalize_batch(&[g1_m, g1_m_div_w, g1_qm]);

    MultiplicityPolynomialsAndQuotient {
        g1_affine_m: g1_affine_list[0],
        g1_affine_m_div_w: g1_affine_list[1],
        g1_affine_qm: g1_affine_list[2],
    }
}

// Index polynomials and the quotients,
// containing [L(tau)]_1, [L(tau * v)]_1, [D(tau)]_1, [Q_L(tau)]_1, and
// [Q_D(tau)]_1.
struct IndexPolynomialsAndQuotients<P: Pairing> {
    g1_affine_l: P::G1Affine,
    g1_affine_l_div_v: P::G1Affine,
    g1_affine_d: P::G1Affine,
    g1_affine_ql: P::G1Affine,
    g1_affine_qd: P::G1Affine,
    poly_l: DensePolynomial<P::ScalarField>,
    poly_ql: DensePolynomial<P::ScalarField>,
    poly_l_div_v: DensePolynomial<P::ScalarField>,
    poly_eval_list_l: Vec<P::ScalarField>,
    poly_eval_list_d: Vec<P::ScalarField>,
    poly_d: DensePolynomial<P::ScalarField>,
    poly_qd: DensePolynomial<P::ScalarField>,
}

// Compute the commitments of [L(tau)]_1, [L(tau*v)]_1, [D(tau)]_1,
// [Q_L(tau)]_1, and [Q_D(tau)]_1.
fn compute_index_polynomials_and_quotients<P: Pairing>(
    domain_k: &Radix2EvaluationDomain<P::ScalarField>,
    domain_v: &Radix2EvaluationDomain<P::ScalarField>,
    domain_coset_v: &Radix2EvaluationDomain<P::ScalarField>,
    roots_of_unity_w: &[P::ScalarField],
    roots_of_unity_v: &[P::ScalarField],
    partial_inv_zk_at_coset_v_values: &[P::ScalarField],
    g1_affine_list_lv: &[P::G1Affine],
    g1_affine_srs: &[P::G1Affine],
    queried_segment_indices: &[usize],
    domain_generator_w: P::ScalarField,
    witness_size: usize,
    segment_size: usize,
) -> Result<IndexPolynomialsAndQuotients<P>, Error> {
    let (poly_eval_list_l, g1_l, g1_l_div_v, poly_eval_list_d) = queried_segment_indices
        .par_iter()
        .enumerate() // Get both index and segment.
        .map(|(i, &seg_index)| {
            let mut partial_poly_eval_list_l = Vec::with_capacity(segment_size);
            let mut partial_g1_l = P::G1::zero();
            let mut partial_g1_l_div_v = P::G1::zero();
            let mut partial_poly_eval_list_d = Vec::with_capacity(1);

            // Compute the range of element indices for this segment.
            let segment_element_start = seg_index * segment_size;
            let segment_element_end = (seg_index + 1) * segment_size;
            let segment_element_indices = segment_element_start..segment_element_end;

            for (j, elem_index) in segment_element_indices.enumerate() {
                let root_of_unity_w = roots_of_unity_w[elem_index];
                partial_poly_eval_list_l.push(root_of_unity_w);

                // Compute witness_element_index based on segment position and element position.
                let witness_element_index = i * segment_size + j;

                // Linear combination of [L^V_i(tau)]_1.
                partial_g1_l
                    .add_assign(g1_affine_list_lv[witness_element_index].mul(root_of_unity_w));

                // Linear combination of [L^V_i(tau / v)]_1.
                // L^V_i(tau / v) = L^V_{i+1}(tau).
                // We can shift [L^V_i(tau)]_1 to the left by 1
                // to get [L^V_i(tau / v)]_1.
                let shifted_witness_elem_index = (witness_element_index + 1) % witness_size;
                partial_g1_l_div_v.add_assign(
                    g1_affine_list_lv[shifted_witness_elem_index].mul(root_of_unity_w),
                );
            }

            // Push the first root of unity for this segment to poly_eval_list_d.
            let root_of_unity_w = roots_of_unity_w[seg_index * segment_size];
            partial_poly_eval_list_d.push(root_of_unity_w);

            // Return the partial results.
            (
                partial_poly_eval_list_l,
                partial_g1_l,
                partial_g1_l_div_v,
                partial_poly_eval_list_d,
            )
        })
        .reduce(
            || (Vec::new(), P::G1::zero(), P::G1::zero(), Vec::new()), // Initial accumulator
            |mut acc, (part_l, part_g1_l, part_g1_l_div_v, part_d)| {
                acc.0.extend(part_l); // Combine poly_eval_list_l
                acc.1.add_assign(part_g1_l); // Combine g1_l
                acc.2.add_assign(part_g1_l_div_v); // Combine g1_l_div_v
                acc.3.extend(part_d); // Combine poly_eval_list_d
                acc
            },
        );

    let poly_coeff_list_d = domain_k.ifft(&poly_eval_list_d);
    let poly_d = DensePolynomial::from_coefficients_vec(poly_coeff_list_d);
    let g1_affine_d = Kzg::<P::G1>::commit(g1_affine_srs, &poly_d).into_affine();

    // Compute the quotient polynomial Q_L(X) s.t. (X^k - 1) * (L(X) - w * L(X / v))
    // = Z_V(X) * Q_L(X), Inverse FFT costs O(ks log(ks)) operations.
    let poly_coeff_list_l = domain_v.ifft(&poly_eval_list_l);
    // The coefficients of L(X / v).
    // We can divide each L(X) polynomial coefficients by v^i.
    let poly_coeff_list_l_div_v: Vec<P::ScalarField> = poly_coeff_list_l
        .par_iter()
        .enumerate()
        .map(|(i, &c)| c / roots_of_unity_v[i])
        .collect();
    let poly_l_div_v = DensePolynomial::from_coefficients_slice(&poly_coeff_list_l_div_v);
    // The coefficients of w * L(X / v).
    // We can multiply each L(X / v) polynomial coefficients by w.
    let poly_coeff_list_w_mul_l_div_v: Vec<P::ScalarField> = poly_coeff_list_l_div_v
        .par_iter()
        .map(|&c| c * domain_generator_w)
        .collect();
    let poly_w_mul_l_div_v = DensePolynomial::from_coefficients_vec(poly_coeff_list_w_mul_l_div_v);
    // Compute y(X) = X^k - 1, which is the vanishing polynomial of Domain V.
    let poly_x_pow_k_sub_one = domain_k.vanishing_polynomial().into();
    let poly_l = DensePolynomial::from_coefficients_vec(poly_coeff_list_l);
    let mut poly_ql = &poly_l - &poly_w_mul_l_div_v;
    poly_ql = poly_ql.mul(&poly_x_pow_k_sub_one);
    let poly_ql = divide_by_vanishing_poly_checked::<P>(domain_v, &poly_ql)?;
    let g1_affine_ql = Kzg::<P::G1>::commit(&g1_affine_srs, &poly_ql).into_affine();

    // Compute Q_D s.t. L(X) - D(X) = Z_K(X) * Q_D(X).
    let mut poly_qd = &poly_l - &poly_d;
    domain_coset_v.fft_in_place(&mut poly_qd.coeffs);
    let partial_size = partial_inv_zk_at_coset_v_values.len();
    let poly_coset_eval_list_qd = poly_qd.coeffs;
    let poly_coset_eval_list_qd = poly_coset_eval_list_qd
        .par_iter()
        .enumerate()
        .map(|(i, &c)| {
            let inv_zk_at_coset_v = partial_inv_zk_at_coset_v_values[i % partial_size];
            c * inv_zk_at_coset_v
        })
        .collect::<Vec<_>>();
    let poly_coeff_list_qd = domain_coset_v.ifft(&poly_coset_eval_list_qd);
    let poly_qd = DensePolynomial::from_coefficients_vec(poly_coeff_list_qd);
    let g1_affine_qd = Kzg::<P::G1>::commit(&g1_affine_srs, &poly_qd).into_affine();

    Ok(IndexPolynomialsAndQuotients {
        g1_affine_l: g1_l.into_affine(),
        g1_affine_l_div_v: g1_l_div_v.into_affine(),
        g1_affine_d,
        g1_affine_ql,
        g1_affine_qd,
        poly_l,
        poly_ql,
        poly_l_div_v,
        poly_eval_list_l,
        poly_eval_list_d,
        poly_d,
        poly_qd,
    })
}

struct PolynomialAAndQuotient<P: Pairing> {
    g1_affine_a: P::G1Affine,
    g1_affine_qa: P::G1Affine,
    g1_affine_a0: P::G1Affine,
    sparse_poly_eval_list_a: DashMap<usize, P::ScalarField>,
}

fn compute_polynomial_a_and_quotient<P: Pairing>(
    beta: P::ScalarField,
    delta: P::ScalarField,
    table_values: &[P::ScalarField],
    segment_multiplicities: &DashMap<usize, usize>,
    segment_size: usize,
    roots_of_unity_w: &[P::ScalarField],
    g1_affine_lw_list: &[P::G1Affine],
    g1_affine_q1_list: &[P::G1Affine],
    g1_affine_q2_list: &[P::G1Affine],
    g1_affine_lw_opening_proofs_at_zero: &[P::G1Affine],
) -> Result<PolynomialAAndQuotient<P>, Error> {
    let sparse_poly_eval_list_a = DashMap::<usize, P::ScalarField>::default();

    // Parallel computation of g1_a and g1_qa
    let (g1_a, g1_qa) = segment_multiplicities
        .par_iter()
        .try_fold(
            || (P::G1::zero(), P::G1::zero()),
            |(mut g1_a_partial, mut g1_qa_partial), entry| {
                let segment_index = *entry.key();
                let multiplicity = *entry.value();

                let segment_element_indices =
                    segment_index * segment_size..(segment_index + 1) * segment_size;
                for elem_index in segment_element_indices {
                    let fr_a_i =
                        (beta + table_values[elem_index] + delta * roots_of_unity_w[elem_index])
                            .inverse()
                            .ok_or(Error::FailedToInverseFieldElement)?
                            * P::ScalarField::from(multiplicity as u64);

                    // Insert into DashMap (thread-safe)
                    sparse_poly_eval_list_a.insert(elem_index, fr_a_i);

                    // Accumulate partial G1 points
                    g1_a_partial.add_assign(g1_affine_lw_list[elem_index].mul(fr_a_i));
                    g1_qa_partial.add_assign(g1_affine_q1_list[elem_index].mul(fr_a_i));
                    g1_qa_partial.add_assign(g1_affine_q2_list[elem_index].mul(delta.mul(fr_a_i)));
                }

                Ok((g1_a_partial, g1_qa_partial))
            },
        )
        .try_reduce(
            || (P::G1::zero(), P::G1::zero()),
            |(g1_a1, g1_qa1), (g1_a2, g1_qa2)| {
                let mut combined_g1_a = g1_a1;
                combined_g1_a.add_assign(&g1_a2);
                let mut combined_g1_qa = g1_qa1;
                combined_g1_qa.add_assign(&g1_qa2);
                Ok((combined_g1_a, combined_g1_qa))
            },
        )?;

    // Parallel computation of g1_a0
    let g1_a0 = sparse_poly_eval_list_a
        .par_iter()
        .map(|entry| {
            let i = *entry.key();
            let a_i = *entry.value();

            g1_affine_lw_opening_proofs_at_zero[i].mul(a_i)
        })
        .reduce(|| P::G1::zero(), |acc, x| acc + x)
        .into_affine();

    Ok(PolynomialAAndQuotient {
        g1_affine_a: g1_a.into_affine(),
        g1_affine_qa: g1_qa.into_affine(),
        g1_affine_a0: g1_a0,
        sparse_poly_eval_list_a,
    })
}

struct PolynomialBAndQuotient<P: Pairing> {
    poly_b: DensePolynomial<P::ScalarField>,
    poly_qb: DensePolynomial<P::ScalarField>,
    poly_b0: DensePolynomial<P::ScalarField>,
    g1_affine_qb: P::G1Affine,
    g1_affine_b0: P::G1Affine,
}

fn compute_polynomial_b_and_quotient<P: Pairing>(
    beta: P::ScalarField,
    delta: P::ScalarField,
    witness: &Witness<P>,
    witness_element_size: usize,
    domain_v: &Radix2EvaluationDomain<P::ScalarField>,
    domain_coset_v: &Radix2EvaluationDomain<P::ScalarField>,
    poly_eval_list_l: &[P::ScalarField],
    poly_l: &DensePolynomial<P::ScalarField>,
    g1_affine_srs: &[P::G1Affine],
) -> Result<PolynomialBAndQuotient<P>, Error> {
    let poly_eval_list_b: Result<Vec<P::ScalarField>, Error> = (0..witness_element_size)
        .into_par_iter()
        .map(|i| {
            (beta + witness.evaluations[i] + delta * poly_eval_list_l[i])
                .inverse()
                .ok_or(Error::FailedToInverseFieldElement)
        })
        .collect();
    let mut poly_eval_list_b = poly_eval_list_b?;
    domain_v.ifft_in_place(&mut poly_eval_list_b);
    let poly_coeff_list_b = poly_eval_list_b;
    let poly_b = DensePolynomial::from_coefficients_vec(poly_coeff_list_b);

    // Round 10-4: The prover computes [Q_B(tau)]_1 using the SRS and Lemma 4.
    let poly_coset_eval_list_l = domain_coset_v.fft(&poly_l);
    let poly_coset_eval_list_b = domain_coset_v.fft(&poly_b);
    let poly_coset_eval_list_f = domain_coset_v.fft(&witness.poly);
    let fr_one = P::ScalarField::one();
    let mut poly_coset_eval_list_qb: Vec<P::ScalarField> = poly_coset_eval_list_b
        .par_iter()
        .zip(poly_coset_eval_list_f.par_iter())
        .zip(poly_coset_eval_list_l.par_iter())
        .map(|((&b_i, &f_i), &l_i)| (b_i * (beta + f_i + delta * l_i)) - fr_one)
        .collect();
    domain_coset_v.ifft_in_place(&mut poly_coset_eval_list_qb);
    let poly_coeff_list_qb = poly_coset_eval_list_qb;

    let mut poly_qb = DensePolynomial::from_coefficients_vec(poly_coeff_list_qb);
    divide_by_vanishing_poly_on_coset_in_place::<P::G1>(&domain_v, &mut poly_qb.coeffs)?;
    let g1_qb = Kzg::<P::G1>::commit(g1_affine_srs, &poly_qb);

    let poly_b0 = DensePolynomial::from_coefficients_slice(&poly_b.coeffs[1..]);
    let g1_b0 = Kzg::<P::G1>::commit(g1_affine_srs, &poly_b0);

    let g1_affine_list = P::G1::normalize_batch(&[g1_qb, g1_b0]);

    Ok(PolynomialBAndQuotient {
        poly_b,
        poly_qb,
        poly_b0,
        g1_affine_qb: g1_affine_list[0],
        g1_affine_b0: g1_affine_list[1],
    })
}

fn compute_degree_check_g1_affine<P: Pairing>(
    num_table_segments: usize,
    num_witness_segments: usize,
    segment_size: usize,
    table_element_size: usize,
    poly_b0: &DensePolynomial<P::ScalarField>,
    g1_affine_srs: &[P::G1Affine],
    sparse_poly_eval_list_a: &DashMap<usize, P::ScalarField>,
    domain_w: &Radix2EvaluationDomain<P::ScalarField>,
) -> P::G1Affine {
    if num_table_segments > num_witness_segments {
        // If n > k, the prover computes P_B(X) and sends [P_B(tau)]_1 to the verifier.
        let coeff_shift = (num_table_segments - num_witness_segments) * segment_size - 1;

        Kzg::<P::G1>::commit_with_offset(&g1_affine_srs, &poly_b0, coeff_shift).into_affine()
    } else if num_table_segments < num_witness_segments {
        // If n < k, the prover computes P_A(X) and sends [P_A(tau)]_1 to the verifier.
        // We can use Inverse FFT to compute the polynomial A(X),
        // since the runtime does not exceed O(ks log ks) as n < k.
        let mut poly_eval_list_a = vec![P::ScalarField::zero(); table_element_size];

        // Step 1: Collect all (index, value) pairs in parallel
        let entries: Vec<(usize, P::ScalarField)> = sparse_poly_eval_list_a
            .par_iter()
            .map(|entry| (*entry.key(), *entry.value()))
            .collect();

        // Step 2: Assign the collected values sequentially
        for (i, a_i) in entries {
            poly_eval_list_a[i] = a_i;
        }

        // Proceed with Inverse FFT and commitment
        domain_w.ifft_in_place(&mut poly_eval_list_a);
        let poly_coeff_list_a = poly_eval_list_a;
        let poly_coeff_list_a0 = poly_coeff_list_a[1..].to_vec();
        let poly_a0 = DensePolynomial::from_coefficients_slice(&poly_coeff_list_a0);

        let coeff_shift = (num_witness_segments - num_table_segments) * segment_size - 1;

        Kzg::<P::G1>::commit_with_offset(&g1_affine_srs, &poly_a0, coeff_shift).into_affine()
    } else {
        P::G1Affine::zero()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::table::{rand_segments, Table};
    use ark_bls12_381::Bls12_381;
    use ark_ec::PrimeGroup;
    use ark_std::rand::RngCore;
    use ark_std::{test_rng, UniformRand};
    use std::ops::{Neg, Sub};

    type Fr = <Bls12_381 as Pairing>::ScalarField;
    type G1 = <Bls12_381 as Pairing>::G1;

    #[test]
    fn test_mul_and_neg() {
        let mut rng = test_rng();
        let s1 = Fr::rand(&mut rng);
        let s2 = Fr::rand(&mut rng);
        let p1 = G1::generator().mul(s1).into_affine();
        assert_eq!(p1.mul(s2).neg(), p1.mul(-s2));
    }

    #[test]
    fn test_domain_generator() {
        let size = 8;
        let domain = Radix2EvaluationDomain::<<Bls12_381 as Pairing>::ScalarField>::new(size).unwrap();
        let domain_elements: Vec<_> = domain.elements().collect();
        assert_eq!(domain_elements[1], domain.group_gen);
    }

    #[test]
    fn test_compute_segment_multiplicities() {
        let queried_segment_indices = vec![0, 1, 2, 3, 0, 1, 2, 3];
        let num_segments = 4;
        let multiplicities =
            compute_segment_multiplicities(&queried_segment_indices, num_segments).unwrap();
        assert_eq!(multiplicities.len(), 4);
        assert_eq!(*multiplicities.get(&0).unwrap().value(), 2);
        assert_eq!(*multiplicities.get(&1).unwrap().value(), 2);
        assert_eq!(*multiplicities.get(&2).unwrap().value(), 2);
        assert_eq!(*multiplicities.get(&3).unwrap().value(), 2);
    }

    #[test]
    fn test_compute_multiplicity_polynomials_and_quotient() {
        let mut rng = test_rng();
        let num_table_segments = 16;
        let num_witness_segments = 8;
        let segment_size = 4;
        let pp = PublicParameters::<Bls12_381>::builder()
            .num_table_segments(num_table_segments)
            .num_witness_segments(num_witness_segments)
            .segment_size(segment_size)
            .build(&mut rng)
            .expect("Failed to setup public parameters");
        let queried_segment_indices = vec![0, 1, 2, 3, 0, 1, 2, 3];
        let multiplicities =
            compute_segment_multiplicities(&queried_segment_indices, num_table_segments).unwrap();

        // Construct polynomial M(X) using Inverse FFT.
        let mut poly_eval_m_list = vec![Fr::zero(); pp.table_element_size];
        multiplicities.iter().for_each(|entry| {
            let i = *entry.key();
            let m = *entry.value();
            let segment_element_indices = i * segment_size..(i + 1) * segment_size;
            let fr_multiplicity = Fr::from(m as u64);
            for j in segment_element_indices {
                poly_eval_m_list[j] = fr_multiplicity;
            }
        });
        let poly_coeff_list_m = pp.domain_w.ifft(&poly_eval_m_list);
        let poly_m = DensePolynomial::from_coefficients_vec(poly_coeff_list_m.clone());
        let g1_affine_m_expected = Kzg::<G1>::commit(&pp.g1_affine_srs, &poly_m).into_affine();
        let inv_generator_w = pp.domain_w.group_gen_inv;
        let poly_coeff_list_m_div_w: Vec<Fr> = poly_coeff_list_m
            .par_iter()
            .enumerate()
            .map(|(i, &c)| c * inv_generator_w.pow(&[i as u64]))
            .collect();
        let poly_m_div_w = DensePolynomial::from_coefficients_vec(poly_coeff_list_m_div_w);
        let g1_affine_m_div_w_expected =
            Kzg::<G1>::commit(&pp.g1_affine_srs, &poly_m_div_w).into_affine();

        let mut poly_coeff_list_x_pow_n_sub_one = vec![Fr::zero(); pp.table_element_size];
        poly_coeff_list_x_pow_n_sub_one[pp.num_table_segments] = Fr::one();
        poly_coeff_list_x_pow_n_sub_one[0] = -Fr::one();
        let poly_x_pow_n_sub_one =
            DensePolynomial::from_coefficients_vec(poly_coeff_list_x_pow_n_sub_one);
        let mut poly_qm = poly_m.clone();
        poly_qm = poly_qm.sub(&poly_m_div_w);
        poly_qm = poly_qm.naive_mul(&poly_x_pow_n_sub_one);
        let poly_qm = divide_by_vanishing_poly_checked::<Bls12_381>(&pp.domain_w, &poly_qm).unwrap();
        let g1_affine_qm_expected = Kzg::<G1>::commit(&pp.g1_affine_srs, &poly_qm).into_affine();

        let MultiplicityPolynomialsAndQuotient {
            g1_affine_m: g1_affine_m_got,
            g1_affine_m_div_w: g1_affine_m_div_w_got,
            g1_affine_qm: g1_affine_qm_got,
        } = compute_multiplicity_polynomials_and_quotient::<Bls12_381>(
            &multiplicities,
            &pp.g1_affine_list_lw,
            &pp.g1_affine_list_q3,
            segment_size,
            pp.table_element_size,
        );

        assert_eq!(g1_affine_m_expected, g1_affine_m_got);
        assert_eq!(g1_affine_m_div_w_expected, g1_affine_m_div_w_got);
        assert_eq!(g1_affine_qm_expected, g1_affine_qm_got);
    }

    #[test]
    fn test_successful_prove() {
        let mut rng = test_rng();
        let inputs = [(4, 8, 4), (8, 4, 4), (8, 16, 4), (16, 8, 4)];
        for (num_table_segments, num_witness_segments, segment_size) in inputs.into_iter() {
            let pp = PublicParameters::<Bls12_381>::builder()
                .num_table_segments(num_table_segments)
                .num_witness_segments(num_witness_segments)
                .segment_size(segment_size)
                .build(&mut rng)
                .expect("Failed to setup public parameters");
            let segments = rand_segments::generate(&pp);

            let t = Table::new(&pp, segments).unwrap();

            let queried_segment_indices: Vec<usize> = (0..pp.num_witness_segments)
                .map(|_| rng.next_u32() as usize % pp.num_table_segments)
                .collect();

            let witness = Witness::new(&pp, &t.values, &queried_segment_indices).unwrap();
            let statement = witness.generate_statement(&pp.g1_affine_srs);

            let tpp = t.preprocess(&pp).unwrap();

            let rng = &mut test_rng();

            prove(&pp, &tpp, &witness, statement, rng).unwrap();
        }
    }
}
