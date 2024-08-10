use ark_ec::PairingEngine;

use crate::error::Error;
use crate::prover::Proof;
use crate::public_parameters::PublicParameters;
use crate::rng::FiatShamirRng;

pub fn verify<E: PairingEngine, FS: FiatShamirRng>(
    pp: &PublicParameters<E>,
    proof: &Proof<E>,
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
        println!("Left pairing: {:?}", left_pairing);
        return Err(Error::Pairing1Failed);
    }

    Ok(())
}


#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;
    use ark_std::rand::RngCore;
    use ark_std::test_rng;
    use rand_chacha::ChaChaRng;
    use sha3::Keccak256;

    use crate::prover::prove;
    use crate::rng::SimpleHashFiatShamirRng;
    use crate::table::{rand_segments, Table};
    use crate::witness::Witness;

    use super::*;

    type FS = SimpleHashFiatShamirRng<Keccak256, ChaChaRng>;
    #[test]
    fn test_verify() {
        let mut rng = test_rng();
        let pp = PublicParameters::setup(&mut rng, 8, 4, 4)
            .expect("Failed to setup public parameters");
        let segments = rand_segments::generate(&pp);
        let segment_slices: Vec<&[<Bn254 as PairingEngine>::Fr]> = segments
            .iter().map(|segment| segment.as_slice()).collect();
        let t = Table::<Bn254>::new(&pp, &segment_slices)
            .expect("Failed to create table");

        let queried_segment_indices: Vec<usize> = (0..pp.num_queries)
            .map(|_| rng.next_u32() as usize % pp.num_segments)
            .collect();

        let witness = Witness::new(&pp, &t, &queried_segment_indices).unwrap();

        let proof: Proof<Bn254> = prove::<Bn254, >(&pp, &witness).unwrap();

        assert!(verify::<Bn254, FS>(&pp, &proof).is_ok());
    }
}