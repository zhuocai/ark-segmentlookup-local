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
    let m_com1 = proof.m_com1;
    let neg_m_inv_w_com1 = -proof.m_inv_w_com1;
    let tau_pow_ns_com2 = pp.srs_g2[pp.num_segments];
    let neg_one_com2 = -pp.srs_g2[0];
    let q_m_com1 = proof.q_m_com1;
    let z_w_com2 = pp.z_w_com2;

    let left_pairing_lhs = m_com1 + neg_m_inv_w_com1;
    let left_pairing_rhs = tau_pow_ns_com2 + neg_one_com2;
    let left_pairing = E::pairing(left_pairing_lhs, left_pairing_rhs);
    let right_pairing = E::pairing(q_m_com1, z_w_com2);

    if left_pairing != right_pairing {
        println!("Left pairing: {:?}", left_pairing);
        return Err(Error::Pairing1Failed);
    }

    Ok(())
}


#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;
    use ark_ec::PairingEngine;
    use ark_std::rand::RngCore;
    use ark_std::test_rng;
    use rand_chacha::ChaChaRng;
    use sha3::Keccak256;

    use crate::prover::Proof;
    use crate::prover::prove;
    use crate::public_parameters::PublicParameters;
    use crate::rng::SimpleHashFiatShamirRng;
    use crate::table::{rand_segments, Table};
    use crate::verifier::verify;
    use crate::witness::Witness;

    type FS = SimpleHashFiatShamirRng<Keccak256, ChaChaRng>;
    #[test]
    fn test_verifier() {
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

        let proof: Proof<Bn254> = prove::<Bn254, FS>(&pp, &witness).unwrap();

        assert!(verify::<Bn254, FS>(&pp, &proof).is_ok());
    }
}