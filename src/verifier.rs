use crate::error::Error;
use crate::multi_unity::multi_unity_verify;
use crate::prover::Proof;
use crate::public_parameters::PublicParameters;

use crate::transcript::Transcript;
use ark_ec::PairingEngine;
use ark_std::rand::rngs::StdRng;

pub fn verify<E: PairingEngine>(
    pp: &PublicParameters<E>,
    transcript: &mut Transcript<E::Fr>,
    proof: &Proof<E>,
    rng: &mut StdRng,
) -> Result<(), Error> {
    // Round 2: Pairing check.
    let g1_m = proof.g1_m;
    let g1_neg_m_div_w = -proof.g1_m_div_w;
    let g2_tau_pow_ns = pp.g2_srs[pp.num_segments];
    let g2_neg_one = -pp.g2_srs[0];
    let g1_q_m = proof.g1_q_m;
    let g2_z_w = pp.g2_z_w;

    let left_pairing_lhs = g1_m + g1_neg_m_div_w;
    let left_pairing_rhs = g2_tau_pow_ns + g2_neg_one;
    let left_pairing = E::pairing(left_pairing_lhs, left_pairing_rhs);
    let right_pairing = E::pairing(g1_q_m, g2_z_w);

    if left_pairing != right_pairing {
        return Err(Error::Pairing1Failed);
    }

    // Round 3-8: Multi-unity check.
    if !multi_unity_verify(pp, transcript, &proof.g1_d, &proof.multi_unity_proof, rng) {
        return Err(Error::FailedToCheckMultiUnity);
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
            PublicParameters::setup(&mut rng, 16, 8, 4)
                .expect("Failed to setup public parameters");
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

        let proof: Proof<Bn254> = prove::<Bn254>(&pp, &mut transcript, &witness, rng).unwrap();

        let mut transcript = Transcript::<<Bn254 as PairingEngine>::Fr>::new();

        assert!(verify::<Bn254>(&pp, &mut transcript, &proof, rng).is_ok());
    }
}
