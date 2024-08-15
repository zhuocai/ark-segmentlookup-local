use crate::error::Error;
use crate::multi_unity::multi_unity_verify;
use crate::prover::Proof;
use crate::public_parameters::PublicParameters;
use std::ops::{Add, Mul, Neg};

use crate::table::TablePreprocessedParameters;
use crate::transcript::{Label, Transcript};
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::Field;
use ark_poly::EvaluationDomain;
use ark_std::rand::rngs::StdRng;
use ark_std::{One, Zero};

pub fn verify<E: PairingEngine>(
    pp: &PublicParameters<E>,
    tpp: &TablePreprocessedParameters<E>,
    statement: E::G1Affine,
    proof: &Proof<E>,
    rng: &mut StdRng,
) -> Result<(), Error> {
    let mut transcript = Transcript::<E::Fr>::new();

    // Round 2: The first pairing check.
    let g1_m = proof.g1_m;
    let g1_neg_m_div_w = -proof.g1_m_div_w;
    let g2_tau_pow_ns = pp.g2_srs[pp.num_segments];
    let g2_neg_one = -pp.g2_srs[0];
    let g1_qm = proof.g1_qm;
    let g2_zw = pp.g2_zw;

    let left_pairing_lhs = g1_m + g1_neg_m_div_w;
    let left_pairing_rhs = g2_tau_pow_ns + g2_neg_one;
    let left_pairing = E::pairing(left_pairing_lhs, left_pairing_rhs);
    let right_pairing = E::pairing(g1_qm, g2_zw);

    if left_pairing != right_pairing {
        return Err(Error::Pairing1Failed);
    }

    transcript.append_elements(&[
        (Label::G1M, g1_m),
        (Label::G1MDivW, proof.g1_m_div_w),
        (Label::G1Qm, g1_qm),
    ])?;

    transcript.append_elements(&[
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

    // Round 11: The second pairing check.
    let beta = transcript.get_and_append_challenge(Label::ChallengeBeta)?;
    let delta = transcript.get_and_append_challenge(Label::ChallengeDelta)?;
    let g1_a = proof.g1_a;
    let g2_t = tpp.g2_t;
    let g2_tau = pp.g2_srs[1];
    let left_pairing = E::pairing(g1_a, g2_t + g2_tau.mul(delta).into_affine());

    let g1_qa = proof.g1_qa;
    let g1_neg_beta_mul_a = g1_a.mul(-beta).into_affine();
    let g2_one = pp.g2_srs[0];
    let right_pairing =
        E::pairing(g1_qa, g2_zw).mul(E::pairing(g1_m.add(g1_neg_beta_mul_a), g2_one));

    if left_pairing != right_pairing {
        return Err(Error::Pairing2Failed);
    }

    // Round 11: Degree pairing check.
    if pp.num_segments > pp.num_queries {
        let deg_tau = (pp.num_segments - pp.num_queries) * pp.segment_size - 1;
        let left_pairing = E::pairing(proof.g1_b0, pp.g2_srs[deg_tau]);
        let right_pairing = E::pairing(proof.g1_px, g2_one);

        if left_pairing != right_pairing {
            return Err(Error::DegreeCheckFailed);
        }
    } else if pp.num_segments < pp.num_queries {
        // TODO: current unit test does not cover this case
        let deg_tau = (pp.num_queries - pp.num_segments) * pp.segment_size - 1;
        let left_pairing = E::pairing(proof.g1_a0, pp.g2_srs[deg_tau]);
        let right_pairing = E::pairing(proof.g1_px, g2_one);

        if left_pairing != right_pairing {
            return Err(Error::DegreeCheckFailed);
        }
    }

    transcript.append_elements(&[
        (Label::G1A, g1_a),
        (Label::G1Qa, g1_qa),
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

    // Round 15-1: Compute b_0 = ns * a_0 / (ks)
    let table_elem_size = pp.num_segments * pp.segment_size;
    let fr_table_elem_size = E::Fr::from(table_elem_size as u64);
    let witness_elem_size = pp.num_queries * pp.segment_size;
    let fr_inv_witness_elem_size = E::Fr::from(witness_elem_size as u64)
        .inverse()
        .ok_or(Error::FailedToInverseFieldElement)?;
    let fr_b_at_zero = proof.fr_a_at_zero * fr_table_elem_size * fr_inv_witness_elem_size;

    // Round 15-2: Compute q_{B, gamma}
    // Compute the inverse of zv_{gamma}
    let fr_zv_at_gamma = pp.domain_v.evaluate_vanishing_polynomial(gamma);
    let fr_inv_zv_at_gamma = fr_zv_at_gamma
        .inverse()
        .ok_or(Error::FailedToInverseFieldElement)?;
    // Compute b_{gamma} = b_{0, gamma} * gamma + b_0
    let fr_b_at_gamma = proof.fr_b0_at_gamma * gamma + fr_b_at_zero;
    let mut fr_qb_at_gamma = proof.fr_f_at_gamma + beta + (delta * proof.fr_l_at_gamma);
    fr_qb_at_gamma = fr_qb_at_gamma * fr_b_at_gamma - E::Fr::one();
    fr_qb_at_gamma = fr_qb_at_gamma * fr_inv_zv_at_gamma;

    // Compute p_{gamma} = l_{gamma, v} + eta * l_{gamma} + eta^2 * q_{gamma, L} +
    // eta^3 * d_{gamma} + eta^4 * q_{gamma, D} + eta^5 * b_{0, gamma} + eta^6 * f_{gamma} +
    // eta^7 * q_{B, gamma}
    let mut eta_pow_x = E::Fr::one();
    let fr_p_at_gamma_terms: Vec<E::Fr> = [
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
    let mut fr_p_at_gamma = E::Fr::zero();
    for term in fr_p_at_gamma_terms {
        fr_p_at_gamma = fr_p_at_gamma.add(&term);
    }

    let mut eta_pow_x = E::Fr::one();
    let g1_p_terms: Vec<E::G1Projective> = [
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
    let mut g1_proj_p = E::G1Projective::zero();
    for term in g1_p_terms {
        g1_proj_p = g1_proj_p.add(&term);
    }
    let g1_p = g1_proj_p.into_affine();

    // Round 15-4: The third pairing check.
    let left_pairing = E::pairing(proof.g1_hp, g2_tau);
    let g1_gamma_mul_hp = proof.g1_hp.mul(gamma).into_affine();
    let g1_neg_p_at_gamma = fr_to_g1_proj::<E>(-fr_p_at_gamma).into_affine();
    let right_pairing = E::pairing(g1_p + g1_neg_p_at_gamma + g1_gamma_mul_hp, g2_one);

    if left_pairing != right_pairing {
        return Err(Error::Pairing3Failed);
    }

    // Round 15-4: The fourth pairing check.
    let g1_neg_a0 = fr_to_g1_proj::<E>(-proof.fr_a_at_zero).into_affine();
    let left_pairing = E::pairing(proof.g1_a + g1_neg_a0, g2_one);
    let right_pairing = E::pairing(proof.g1_a0, g2_tau);
    if left_pairing != right_pairing {
        return Err(Error::Pairing4Failed);
    }

    // Round 15-4: The first equation check.
    // TODO: Optimize point operations.
    let fr_gamma_pow_k_sub_one = gamma.pow([pp.num_queries as u64]) - E::Fr::one();
    let g1_l_at_gamma_div_v = fr_to_g1_proj::<E>(proof.fr_l_at_gamma_div_v).into_affine();
    let mut g1_equation1 = g1_l_at_gamma_div_v
        .mul(-(fr_gamma_pow_k_sub_one * pp.domain_w.group_gen))
        .into_affine();
    let g1_l_at_gamma = fr_to_g1_proj::<E>(proof.fr_l_at_gamma).into_affine();
    g1_equation1 = g1_equation1.add(g1_l_at_gamma.mul(fr_gamma_pow_k_sub_one).into_affine());
    let g1_ql_at_gamma = fr_to_g1_proj::<E>(proof.fr_ql_at_gamma).into_affine();
    g1_equation1 = g1_equation1.add(g1_ql_at_gamma.mul(-fr_zv_at_gamma).into_affine());
    if g1_equation1 != E::G1Affine::zero() {
        return Err(Error::EquationCheck1Failed);
    }

    // Round 15-4: The second equation check.
    // TODO: Optimize point operations.
    let fr_zk_at_gamma = pp.domain_k.evaluate_vanishing_polynomial(gamma);
    let g1_d_at_gamma = fr_to_g1_proj::<E>(proof.fr_d_at_gamma).into_affine();
    let mut g1_equation2 = g1_l_at_gamma.add(g1_d_at_gamma.neg());
    let g1_qd_at_gamma = fr_to_g1_proj::<E>(proof.fr_qd_at_gamma).into_affine();
    g1_equation2 = g1_equation2.add(g1_qd_at_gamma.mul(-fr_zk_at_gamma).into_affine());
    if g1_equation2 != E::G1Affine::zero() {
        return Err(Error::EquationCheck2Failed);
    }

    Ok(())
}

fn fr_to_g1_proj<E: PairingEngine>(fr: E::Fr) -> E::G1Projective {
    E::G1Affine::prime_subgroup_generator().mul(fr)
}

#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;
    use ark_std::rand::RngCore;
    use ark_std::test_rng;

    use crate::prover::prove;
    use crate::table::{rand_segments, Table};
    use crate::witness::Witness;

    use super::*;

    // TODO: add test cases with different parameters,
    // e.g., (8, 4, 4), (4, 8, 4).

    #[test]
    fn test_verify() {
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

        let statement = witness.generate_statement(&pp.g1_srs);

        let tpp = t.preprocess(&pp).unwrap();

        let rng = &mut test_rng();

        let proof: Proof<Bn254> = match prove::<Bn254>(&pp, &t, &tpp, &witness, rng) {
            Ok(proof) => proof,
            Err(err) => {
                eprintln!("{:?}", err);
                panic!("Failed to prove");
            }
        };

        let result = match verify::<Bn254>(&pp, &tpp, statement, &proof, rng) {
            Ok(_) => true,
            Err(err) => {
                eprintln!("{:?}", err);
                false
            }
        };
        assert!(result);
    }
}
