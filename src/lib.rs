mod domain;
mod error;
mod kzg;
mod lagrange_basis;
pub mod multi_unity;
pub mod prover;
pub mod public_parameters;
pub mod table;
mod transcript;
pub mod verifier;
mod witness;

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use crate::prover::prove;
    use crate::public_parameters::PublicParameters;
    use crate::table::{rand_segments, Table, TablePreprocessedParameters};
    use crate::verifier::verify;
    use crate::witness::Witness;
    use ark_ec::PairingEngine;
    use ark_std::rand::RngCore;
    use ark_std::test_rng;

    fn prepare_common_inputs<E: PairingEngine>(
        num_table_segments: usize,
        num_witness_segments: usize,
        segment_size: usize,
    ) -> (
        PublicParameters<E>,
        Table<E>,
        Witness<E>,
        E::G1Affine,
        TablePreprocessedParameters<E>,
    ) {
        let mut rng = test_rng();
        let pp = PublicParameters::setup(
            &mut rng,
            num_table_segments,
            num_witness_segments,
            segment_size,
        )
        .unwrap();
        let segments = rand_segments::generate(&pp);
        let segment_slices: Vec<&[E::Fr]> =
            segments.iter().map(|segment| segment.as_slice()).collect();
        let t = Table::<E>::new(&pp, &segment_slices).expect("Failed to create table");

        let queried_segment_indices: Vec<usize> = (0..pp.num_witness_segments)
            .map(|_| rng.next_u32() as usize % pp.num_table_segments)
            .collect();

        let witness = Witness::new(&pp, &t, &queried_segment_indices).unwrap();

        let statement = witness.generate_statement(&pp.g1_srs);

        let tpp = t.preprocess(&pp).unwrap();

        (pp, t, witness, statement, tpp)
    }

    #[test]
    fn test_2_2_4() {
        let (pp, t, witness, statement, tpp) = prepare_common_inputs::<ark_bn254::Bn254>(2, 2, 4);

        let rng = &mut test_rng();

        let proof = prove(&pp, &t, &tpp, &witness, rng).unwrap();

        verify(&pp, &tpp, statement, &proof, rng).unwrap();
    }

    #[test]
    fn test_4_4_1() {
        let (pp, t, witness, statement, tpp) = prepare_common_inputs::<ark_bn254::Bn254>(4, 4, 1);

        let rng = &mut test_rng();

        let proof = prove(&pp, &t, &tpp, &witness, rng).unwrap();

        verify(&pp, &tpp, statement, &proof, rng).unwrap();
    }

    #[test]
    fn test_4_4_4() {
        let (pp, t, witness, statement, tpp) = prepare_common_inputs::<ark_bn254::Bn254>(4, 4, 4);

        let rng = &mut test_rng();

        let proof = prove(&pp, &t, &tpp, &witness, rng).unwrap();

        verify(&pp, &tpp, statement, &proof, rng).unwrap();
    }

    #[test]
    fn test_4_16_4() {
        let (pp, t, witness, statement, tpp) = prepare_common_inputs::<ark_bn254::Bn254>(4, 16, 4);

        let rng = &mut test_rng();

        let proof = prove(&pp, &t, &tpp, &witness, rng).unwrap();

        verify(&pp, &tpp, statement, &proof, rng).unwrap();
    }

    #[test]
    fn test_8_8_1() {
        let (pp, t, witness, statement, tpp) = prepare_common_inputs::<ark_bn254::Bn254>(8, 8, 1);

        let rng = &mut test_rng();

        let proof = prove(&pp, &t, &tpp, &witness, rng).unwrap();

        verify(&pp, &tpp, statement, &proof, rng).unwrap();
    }

    #[test]
    fn test_8_8_4() {
        let (pp, t, witness, statement, tpp) = prepare_common_inputs::<ark_bn254::Bn254>(8, 8, 4);

        let rng = &mut test_rng();

        let proof = prove(&pp, &t, &tpp, &witness, rng).unwrap();

        verify(&pp, &tpp, statement, &proof, rng).unwrap();
    }

    #[test]
    fn test_8_16_4() {
        let (pp, t, witness, statement, tpp) = prepare_common_inputs::<ark_bn254::Bn254>(8, 16, 4);

        let rng = &mut test_rng();

        let proof = prove(&pp, &t, &tpp, &witness, rng).unwrap();

        verify(&pp, &tpp, statement, &proof, rng).unwrap();
    }

    #[test]
    fn test_16_8_4() {
        let (pp, t, witness, statement, tpp) = prepare_common_inputs::<ark_bn254::Bn254>(16, 8, 4);

        let rng = &mut test_rng();

        let proof = prove(&pp, &t, &tpp, &witness, rng).unwrap();

        verify(&pp, &tpp, statement, &proof, rng).unwrap();
    }
}
