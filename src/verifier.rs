use crate::error::Error;
use crate::multi_unity::multi_unity_verify;
use crate::prover::Proof;
use crate::public_parameters::PublicParameters;
use std::ops::{Add, Mul};

use crate::table::TablePreprocessedParameters;
use crate::transcript::Transcript;
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_std::rand::rngs::StdRng;

pub fn verify<E: PairingEngine>(
    pp: &PublicParameters<E>,
    tpp: &TablePreprocessedParameters<E>,
    proof: &Proof<E>,
    rng: &mut StdRng,
) -> Result<(), Error> {
    let mut transcript = Transcript::<E::Fr>::new();

    // Round 2: Pairing check.
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

    // Round 3-8: Multi-unity check.
    if !multi_unity_verify(
        pp,
        &mut transcript,
        &proof.g1_d,
        &proof.multi_unity_proof,
        rng,
    ) {
        return Err(Error::FailedToCheckMultiUnity);
    }

    // Round 11: Pairing check.
    let beta = transcript.get_and_append_challenge(b"beta");
    let delta = transcript.get_and_append_challenge(b"delta");
    let g1_a = proof.g1_a;
    let g2_t = tpp.g2_t;
    let g2_tau = pp.g2_srs[1].clone();
    let left_pairing = E::pairing(g1_a, g2_t + g2_tau.mul(delta).into_affine());

    let g1_qa = proof.g1_qa;
    let g1_neg_beta_mul_a = g1_a.mul(-beta).into_affine();
    let g2_one = pp.g2_srs[0].clone();
    let right_pairing =
        E::pairing(g1_qa, g2_zw).mul(E::pairing(g1_m.add(g1_neg_beta_mul_a), g2_one));

    if left_pairing != right_pairing {
        return Err(Error::Pairing2Failed);
    }

    // Round 11: Degree check
    if pp.num_segments > pp.num_queries {
        let deg_tau = (pp.num_segments - pp.num_queries) * pp.segment_size - 1;
        let left_pairing = E::pairing(proof.g1_b0, pp.g2_srs[deg_tau]);
        let right_pairing = E::pairing(proof.g1_px, pp.g2_srs[0]);

        if left_pairing != right_pairing {
            return Err(Error::DegreeCheckFailed);
        }
    } else if pp.num_segments < pp.num_queries {
        // TODO: current unit test does not cover this case
        let deg_tau = (pp.num_queries - pp.num_segments) * pp.segment_size - 1;
        let left_pairing = E::pairing(proof.g1_a0, pp.g2_srs[deg_tau]);
        let right_pairing = E::pairing(proof.g1_px, pp.g2_srs[0]);

        if left_pairing != right_pairing {
            return Err(Error::DegreeCheckFailed);
        }
    }

    Ok(())
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

        let tpp = t.preprocess(&pp).unwrap();

        let rng = &mut test_rng();

        let proof: Proof<Bn254> = prove::<Bn254>(&pp, &t, &tpp, &witness, rng).unwrap();

        assert!(verify::<Bn254>(&pp, &tpp, &proof, rng).is_ok());
    }
}
