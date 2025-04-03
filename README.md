# ark-segmentlookup

ark-segmentlookup is a Rust library implementing the segment lookup protocol using the [arkworks](https://arkworks.rs/)
ecosystem.
It leverages parallelization through [rayon](https://docs.rs/rayon/latest/rayon/) to speed up the operations.

The lookup protocol is based on Section 3.5 of the
paper [SublonK: Sublinear Prover PlonK](https://eprint.iacr.org/2023/902) and includes corrections and performance
improvements.

> Note: This project is a work-in-progress. Please use it at your own risk.

## Example

Below is a simple example demonstrating how to perform a single segment lookup.
In this demo, we create one table segment containing four random field elements, construct the witness, and generate and
verify a lookup proof.

```rust
use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use ark_segmentlookup::prover::prove;
use ark_segmentlookup::public_parameters::PublicParameters;
use ark_segmentlookup::table::Table;
use ark_segmentlookup::verifier::verify;
use ark_segmentlookup::witness::Witness;
use ark_std::{test_rng, UniformRand};

fn main() {
    // For this simple demo:
    // - We have one table segment.
    // - We will query that single segment.
    // - Each segment contains 4 random field elements.
    let num_table_segments = 1;
    let num_witness_segments = 1;
    let segment_size = 4;

    let mut rng = test_rng();

    // Setup public parameters.
    let pp = PublicParameters::builder()
        .num_table_segments(num_table_segments)
        .num_witness_segments(num_witness_segments)
        .segment_size(segment_size)
        .build(&mut rng)
        .expect("Failed to setup public parameters");

    // Create a single table segment with random field elements.
    let segment: Vec<_> = (0..segment_size)
        .map(|_| <Bls12_381 as Pairing>::ScalarField::rand(&mut rng))
        .collect();
    let segments = vec![segment];

    // Build the lookup table.
    let table = Table::<Bls12_381>::new(&pp, segments).expect("Failed to create table");
    let tpp = table.preprocess(&pp).expect("Failed to preprocess table");

    // For a single segment, the only valid queried segment index is 0.
    let queried_segment_indices = vec![0];
    let witness = Witness::new(&pp, &tpp.adjusted_table_values, &queried_segment_indices)
        .expect("Failed to create witness");

    // Generate the lookup statement from the witness.
    let statement = witness.generate_statement(&pp.g1_affine_srs);

    // Generate a proof for the lookup.
    let proof = prove(&pp, &tpp, &witness, statement, &mut rng)
        .expect("Failed to generate proof");

    // Verify the generated proof.
    verify(&pp, &tpp, statement, &proof, &mut rng)
        .expect("Failed to verify proof");

    println!("Single segment lookup proof generated and verified successfully!");
}
```