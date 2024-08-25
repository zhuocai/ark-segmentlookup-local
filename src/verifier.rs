use crate::error::Error;
use crate::multi_unity::multi_unity_verify;
use crate::prover::Proof;
use crate::public_parameters::PublicParameters;
use crate::table::TablePreprocessedParameters;
use crate::transcript::{Label, Transcript};
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Field;
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_std::rand::Rng;
use ark_std::{One, Zero};
use std::ops::{Add, AddAssign, Mul, MulAssign, Neg};

pub fn verify<P: Pairing, R: Rng + ?Sized>(
    pp: &PublicParameters<P>,
    tpp: &TablePreprocessedParameters<P>,
    statement: P::G1Affine,
    proof: &Proof<P>,
    rng: &mut R,
) -> Result<(), Error> {
    let mut transcript = Transcript::<P::ScalarField>::new();

    // Round 2: The first pairing check.
    // This is intended to check the correctness of multiplicity polynomials.
    first_pairing_check(&proof, &pp.g2_srs, pp.g2_zw, pp.num_table_segments)?;

    transcript.append_elements(&[
        (Label::G1M, proof.g1_m),
        (Label::G1MDivW, proof.g1_m_div_w),
        (Label::G1Qm, proof.g1_qm),
        (Label::G1L, proof.g1_l),
        (Label::G1LDivV, proof.g1_l_div_v),
        (Label::G1Ql, proof.g1_ql),
        (Label::G1D, proof.g1_d),
        (Label::G1Qd, proof.g1_qd),
    ])?;

    // Round 3-8: Multi-unity check.
    if !multi_unity_verify(
        pp,
        &mut transcript,
        &proof.g1_d,
        &proof.multi_unity_proof,
        rng,
    )? {
        return Err(Error::FailedToCheckMultiUnity);
    }

    let beta = transcript.get_and_append_challenge(Label::ChallengeBeta)?;
    let delta = transcript.get_and_append_challenge(Label::ChallengeDelta)?;

    // Round 11: The second pairing check.
    // This is intended to check the correctness of polynomial A.
    second_pairing_check::<P>(
        &proof, beta, delta, proof.g1_m, tpp.g2_t, pp.g2_zw, &pp.g2_srs,
    )?;

    // Round 11: Degree pairing check.
    degree_check(
        &proof,
        pp.num_table_segments,
        pp.num_witness_segments,
        pp.segment_size,
        &pp.g2_srs,
    )?;

    transcript.append_elements(&[
        (Label::G1A, proof.g1_a),
        (Label::G1Qa, proof.g1_qa),
        (Label::G1Qb, proof.g1_qb),
        (Label::G1A0, proof.g1_a0),
        (Label::G1B0, proof.g1_b0),
        (Label::G1Px, proof.g1_px),
    ])?;

    let gamma = transcript.get_and_append_challenge(Label::ChallengeGamma)?;

    transcript.append_elements(&[
        (Label::FrB0AtGamma, proof.fr_b0_at_gamma),
        (Label::FrFAtGamma, proof.fr_f_at_gamma),
        (Label::FrLAtGamma, proof.fr_l_at_gamma),
        (Label::FrAAtZero, proof.fr_a_at_zero),
        (Label::FrLAtGammaDivV, proof.fr_l_at_gamma_div_v),
        (Label::FrQlAtGamma, proof.fr_ql_at_gamma),
        (Label::FrDAtGamma, proof.fr_d_at_gamma),
        (Label::FrQdAtGamma, proof.fr_qd_at_gamma),
    ])?;

    let eta = transcript.get_and_append_challenge(Label::ChallengeEta)?;

    // Round 15-4: The third pairing check.
    let g2_one = pp.g2_srs[0];
    let g2_tau = pp.g2_srs[1];
    third_pairing_check(
        &proof,
        statement,
        beta,
        delta,
        gamma,
        eta,
        pp.num_table_segments,
        pp.num_witness_segments,
        pp.segment_size,
        &pp.domain_v,
        g2_tau,
        g2_one,
    )?;

    // Round 15-4: The fourth pairing check.
    fourth_pairing_check(&proof, g2_tau, g2_one)?;

    // Round 15-4: The first point check.
    first_point_check(
        &proof,
        gamma,
        pp.num_witness_segments,
        &pp.domain_v,
        &pp.domain_w,
    )?;

    // Round 15-4: The second point check.
    second_point_check(&proof, gamma, &pp.domain_k)?;

    Ok(())
}

fn first_pairing_check<P: Pairing>(
    proof: &Proof<P>,
    g2_srs: &[P::G2Affine],
    g2_zw: P::G2Affine,
    num_table_segments: usize,
) -> Result<(), Error> {
    let g1_m = proof.g1_m;
    let g1_neg_m_div_w = -proof.g1_m_div_w.into_group();
    let g2_tau_pow_ns = g2_srs[num_table_segments];
    let g2_neg_one = -g2_srs[0].into_group();
    let g1_qm = proof.g1_qm;
    let g2_zw = g2_zw;

    let left_pairing = P::pairing(g1_m + g1_neg_m_div_w, g2_tau_pow_ns + g2_neg_one);
    let right_pairing = P::pairing(g1_qm, g2_zw);

    if left_pairing != right_pairing {
        return Err(Error::Pairing1Failed);
    }

    Ok(())
}

fn second_pairing_check<P: Pairing>(
    proof: &Proof<P>,
    beta: P::ScalarField,
    delta: P::ScalarField,
    g1_m: P::G1Affine,
    g2_t: P::G2Affine,
    g2_zw: P::G2Affine,
    g2_srs: &[P::G2Affine],
) -> Result<(), Error> {
    let g1_a = proof.g1_a;
    let g2_t = g2_t;
    let g2_tau = g2_srs[1];
    let left_pairing = P::pairing(g1_a, g2_t + g2_tau.mul(delta).into_affine());

    let g1_qa = proof.g1_qa;
    let g1_neg_beta_mul_a = g1_a.mul(-beta).into_affine();
    let g2_one = g2_srs[0];
    let right_pairing = P::multi_pairing(
        &[g1_qa, g1_m.add(g1_neg_beta_mul_a).into_affine()],
        &[g2_zw, g2_one],
    );

    if left_pairing != right_pairing {
        return Err(Error::Pairing2Failed);
    }

    Ok(())
}

fn degree_check<P: Pairing>(
    proof: &Proof<P>,
    num_table_segments: usize,
    num_witness_segments: usize,
    segment_size: usize,
    g2_srs: &[P::G2Affine],
) -> Result<(), Error> {
    let g1_px = proof.g1_px;
    let g2_one = g2_srs[0];
    if num_table_segments > num_witness_segments {
        let deg_tau = (num_table_segments - num_witness_segments) * segment_size - 1;
        let g1_b0 = proof.g1_b0;
        let left_pairing = P::pairing(g1_b0, g2_srs[deg_tau]);
        let right_pairing = P::pairing(g1_px, g2_one);

        if left_pairing != right_pairing {
            return Err(Error::DegreeCheckFailed);
        }
    } else if num_table_segments < num_witness_segments {
        let deg_tau = (num_witness_segments - num_table_segments) * segment_size - 1;
        let g1_a0 = proof.g1_a0;
        let left_pairing = P::pairing(g1_a0, g2_srs[deg_tau]);
        let right_pairing = P::pairing(g1_px, g2_one);

        if left_pairing != right_pairing {
            return Err(Error::DegreeCheckFailed);
        }
    }

    Ok(())
}

fn third_pairing_check<P: Pairing>(
    proof: &Proof<P>,
    statement: P::G1Affine,
    beta: P::ScalarField,
    delta: P::ScalarField,
    gamma: P::ScalarField,
    eta: P::ScalarField,
    num_table_segments: usize,
    num_witness_segments: usize,
    segment_size: usize,
    domain_v: &Radix2EvaluationDomain<P::ScalarField>,
    g2_tau: P::G2Affine,
    g2_one: P::G2Affine,
) -> Result<(), Error> {
    // Round 15-1: Compute b_0 = ns * a_0 / (ks)
    let table_elem_size = num_table_segments * segment_size;
    let fr_table_elem_size = P::ScalarField::from(table_elem_size as u64);
    let witness_elem_size = num_witness_segments * segment_size;
    let fr_inv_witness_elem_size = P::ScalarField::from(witness_elem_size as u64)
        .inverse()
        .ok_or(Error::FailedToInverseFieldElement)?;
    let fr_b_at_zero = proof.fr_a_at_zero * fr_table_elem_size * fr_inv_witness_elem_size;

    // Round 15-2: Compute q_{B, gamma}
    // Compute the inverse of zv_{gamma}
    let fr_zv_at_gamma = domain_v.evaluate_vanishing_polynomial(gamma);
    let fr_inv_zv_at_gamma = fr_zv_at_gamma
        .inverse()
        .ok_or(Error::FailedToInverseFieldElement)?;
    // Compute b_{gamma} = b_{0, gamma} * gamma + b_0
    let fr_b_at_gamma = proof.fr_b0_at_gamma * gamma + fr_b_at_zero;
    let mut fr_qb_at_gamma = proof.fr_f_at_gamma + beta + (delta * proof.fr_l_at_gamma);
    fr_qb_at_gamma = fr_qb_at_gamma * fr_b_at_gamma - P::ScalarField::one();
    fr_qb_at_gamma = fr_qb_at_gamma * fr_inv_zv_at_gamma;

    // Compute p_{gamma} = l_{gamma, v} + eta * l_{gamma} + eta^2 * q_{gamma, L} +
    // eta^3 * d_{gamma} + eta^4 * q_{gamma, D} + eta^5 * b_{0, gamma} + eta^6 * f_{gamma} +
    // eta^7 * q_{B, gamma}
    let mut eta_pow_x = P::ScalarField::one();
    let fr_p_at_gamma_terms: Vec<P::ScalarField> = [
        &proof.fr_l_at_gamma_div_v,
        &proof.fr_l_at_gamma,
        &proof.fr_ql_at_gamma,
        &proof.fr_d_at_gamma,
        &proof.fr_qd_at_gamma,
        &proof.fr_b0_at_gamma,
        &proof.fr_f_at_gamma,
        &fr_qb_at_gamma,
    ]
    .iter()
    .map(|fr| {
        let term = fr.mul(eta_pow_x);
        eta_pow_x *= eta;

        term
    })
    .collect();
    let mut fr_p_at_gamma = P::ScalarField::zero();
    for term in fr_p_at_gamma_terms {
        fr_p_at_gamma = fr_p_at_gamma.add(&term);
    }

    let mut eta_pow_x = P::ScalarField::one();
    let g1_p_terms: Vec<P::G1> = [
        &proof.g1_l_div_v,
        &proof.g1_l,
        &proof.g1_ql,
        &proof.g1_d,
        &proof.g1_qd,
        &proof.g1_b0,
        &statement,
        &proof.g1_qb,
    ]
    .iter()
    .map(|g1| {
        let term = g1.mul(eta_pow_x);
        eta_pow_x *= eta;

        term
    })
    .collect();
    let mut g1_proj_p = P::G1::zero();
    for term in g1_p_terms {
        g1_proj_p = g1_proj_p.add(&term);
    }
    let g1_p = g1_proj_p.into_affine();

    let left_pairing = P::pairing(proof.g1_hp, g2_tau);
    let g1_gamma_mul_hp = proof.g1_hp.mul(gamma).into_affine();
    let g1_neg_p_at_gamma = fr_to_curve_element::<P::G1>(-fr_p_at_gamma).into_affine();
    let right_pairing = P::pairing(g1_p + g1_neg_p_at_gamma + g1_gamma_mul_hp, g2_one);

    if left_pairing != right_pairing {
        return Err(Error::Pairing3Failed);
    }

    Ok(())
}

fn fourth_pairing_check<P: Pairing>(
    proof: &Proof<P>,
    g2_tau: P::G2Affine,
    g2_one: P::G2Affine,
) -> Result<(), Error> {
    let g1_neg_a0 = fr_to_curve_element::<P::G1>(-proof.fr_a_at_zero).into_affine();
    let left_pairing = P::pairing(proof.g1_a + g1_neg_a0, g2_one);
    let right_pairing = P::pairing(proof.g1_a0, g2_tau);

    if left_pairing != right_pairing {
        return Err(Error::Pairing4Failed);
    }

    Ok(())
}

fn first_point_check<P: Pairing>(
    proof: &Proof<P>,
    gamma: P::ScalarField,
    num_witness_segments: usize,
    domain_v: &Radix2EvaluationDomain<P::ScalarField>,
    domain_w: &Radix2EvaluationDomain<P::ScalarField>,
) -> Result<(), Error> {
    let fr_gamma_pow_k_sub_one = gamma.pow([num_witness_segments as u64]) - P::ScalarField::one();
    let fr_neg_gamma_pow_k_sub_one = -fr_gamma_pow_k_sub_one;
    let fr_neg_zv_at_gamma = -domain_v.evaluate_vanishing_polynomial(gamma);

    let mut g1_proj_l_at_gamma_div_v = fr_to_curve_element::<P::G1>(proof.fr_l_at_gamma_div_v);
    let mut g1_proj_l_at_gamma = fr_to_curve_element::<P::G1>(proof.fr_l_at_gamma);
    let mut g1_proj_ql_at_gamma = fr_to_curve_element::<P::G1>(proof.fr_ql_at_gamma);

    g1_proj_l_at_gamma_div_v.mul_assign(fr_neg_gamma_pow_k_sub_one * domain_w.group_gen);
    g1_proj_l_at_gamma.mul_assign(fr_gamma_pow_k_sub_one);
    g1_proj_ql_at_gamma.mul_assign(fr_neg_zv_at_gamma);
    let mut g1_proj_check1 = g1_proj_l_at_gamma_div_v.clone();
    g1_proj_check1.add_assign(g1_proj_l_at_gamma);
    g1_proj_check1.add_assign(g1_proj_ql_at_gamma);

    if g1_proj_check1 != P::G1::zero() {
        return Err(Error::PointCheck1Failed);
    }

    Ok(())
}

fn second_point_check<P: Pairing>(
    proof: &Proof<P>,
    gamma: P::ScalarField,
    domain_k: &Radix2EvaluationDomain<P::ScalarField>,
) -> Result<(), Error> {
    let mut g1_proj_l_at_gamma = fr_to_curve_element::<P::G1>(proof.fr_l_at_gamma);
    let fr_zk_at_gamma = domain_k.evaluate_vanishing_polynomial(gamma);
    let g1_d_at_gamma = fr_to_curve_element::<P::G1>(proof.fr_d_at_gamma);

    g1_proj_l_at_gamma.add_assign(g1_d_at_gamma.neg());
    let mut g1_proj_check2 = g1_proj_l_at_gamma.clone();
    let mut g1_proj_qd_at_gamma = fr_to_curve_element::<P::G1>(proof.fr_qd_at_gamma);
    g1_proj_qd_at_gamma.mul_assign(-fr_zk_at_gamma);
    g1_proj_check2.add_assign(g1_proj_qd_at_gamma);

    if g1_proj_check2 != P::G1::zero() {
        return Err(Error::PointCheck2Failed);
    }

    Ok(())
}

fn fr_to_curve_element<C: CurveGroup>(fr: C::ScalarField) -> C {
    let mut g1_proj_gen = C::generator();
    g1_proj_gen.mul_assign(fr);

    g1_proj_gen
}

#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;
    use ark_std::rand::RngCore;
    use ark_std::{test_rng, UniformRand};

    use crate::prover::prove;
    use crate::table::{rand_segments, Table};
    use crate::witness::Witness;

    use super::*;

    type Fr = <Bn254 as Pairing>::ScalarField;
    type G1Affine = <Bn254 as Pairing>::G1Affine;

    #[test]
    fn test_successful_verify() {
        let mut rng = test_rng();

        let inputs = [(4, 8, 4), (8, 4, 4), (16, 8, 4)];

        for (num_table_segments, num_witness_segments, segment_size) in inputs.into_iter() {
            let pp = PublicParameters::setup(
                &mut rng,
                num_table_segments,
                num_witness_segments,
                segment_size,
            )
            .expect("Failed to setup public parameters");
            let segments = rand_segments::generate(&pp);

            let t = Table::<Bn254>::new(&pp, segments).expect("Failed to create table");

            let queried_segment_indices: Vec<usize> = (0..pp.num_witness_segments)
                .map(|_| rng.next_u32() as usize % pp.num_table_segments)
                .collect();

            let witness = Witness::new(&pp, &t, &queried_segment_indices).unwrap();

            let statement = witness.generate_statement(&pp.g1_srs);

            let tpp = t.preprocess(&pp).unwrap();

            let rng = &mut test_rng();

            let proof = prove::<Bn254, _>(&pp, &t, &tpp, &witness, rng).expect("Failed to prove");

            assert!(verify::<Bn254, _>(&pp, &tpp, statement, &proof, rng).is_ok());
        }
    }

    #[test]
    fn test_failed_verify() {
        let mut rng = test_rng();

        let inputs = [(4, 8, 4), (8, 4, 4), (16, 8, 4)];

        for (num_table_segments, num_witness_segments, segment_size) in inputs.into_iter() {
            let pp = PublicParameters::setup(
                &mut rng,
                num_table_segments,
                num_witness_segments,
                segment_size,
            )
            .expect("Failed to setup public parameters");
            let segments = rand_segments::generate(&pp);

            let t = Table::<Bn254>::new(&pp, segments.clone()).expect("Failed to create table");

            let queried_segment_indices: Vec<usize> = (0..pp.num_witness_segments)
                .map(|_| rng.next_u32() as usize % pp.num_table_segments)
                .collect();

            let witness = Witness::new(&pp, &t, &queried_segment_indices).unwrap();

            let statement = witness.generate_statement(&pp.g1_srs);

            let tpp = t.preprocess(&pp).unwrap();

            let rng = &mut test_rng();

            // Wrong table
            let new_segments = segments
                .into_iter()
                .map(|segment| {
                    segment
                        .iter()
                        .map(|&s| s + Fr::rand(rng))
                        .collect::<Vec<Fr>>()
                })
                .collect();
            let new_t = Table::new(&pp, new_segments).expect("Failed to create table");

            let proof = prove(&pp, &new_t, &tpp, &witness, rng).expect("Failed to prove");

            assert!(!verify(&pp, &tpp, statement, &proof, rng).is_ok());

            // Wrong witness from wrong table
            let new_queried_segment_indices: Vec<usize> = (0..pp.num_witness_segments)
                .map(|_| rng.next_u32() as usize % pp.num_table_segments)
                .collect();
            let new_witness = Witness::new(&pp, &new_t, &new_queried_segment_indices).unwrap();

            let proof = prove(&pp, &t, &tpp, &new_witness, rng).expect("Failed to prove");

            assert!(!verify(&pp, &tpp, statement, &proof, rng).is_ok());

            // Wrong witness from wrong indices
            let new_queried_segment_indices: Vec<usize> = (0..pp.num_witness_segments)
                .map(|_| rng.next_u32() as usize % pp.num_table_segments)
                .collect();
            let new_witness = Witness {
                num_witness_segments: pp.num_witness_segments,
                segment_size: pp.segment_size,
                poly_f: witness.poly_f.clone(),
                poly_eval_list_f: witness.poly_eval_list_f.clone(),
                segment_indices: new_queried_segment_indices,
            };

            let proof = prove(&pp, &t, &tpp, &new_witness, rng).expect("Failed to prove");

            assert!(!verify(&pp, &tpp, statement, &proof, rng).is_ok());

            // Wrong statement
            let new_statement = G1Affine::generator().mul(Fr::rand(rng)).into_affine();
            let proof = prove(&pp, &t, &tpp, &witness, rng).expect("Failed to prove");

            assert!(!verify(&pp, &tpp, new_statement, &proof, rng).is_ok());
        }
    }
}
