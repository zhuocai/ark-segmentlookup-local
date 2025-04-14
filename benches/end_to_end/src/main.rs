mod parameters;

use ark_bls12_381::Bls12_381;
use ark_ec::pairing::Pairing;
use ark_segmentlookup::prover::prove;
use ark_segmentlookup::public_parameters::PublicParameters;
use ark_segmentlookup::table::Table;
use ark_segmentlookup::verifier::verify;
use ark_segmentlookup::witness::Witness;
use ark_std::rand::RngCore;
use ark_std::{test_rng, UniformRand};

fn rand_table<P: Pairing>(
    num_table_segments: usize,
    segment_size: usize,
) -> Vec<Vec<P::ScalarField>> {
    let mut rng = test_rng();

    let mut segments = Vec::with_capacity(num_table_segments);
    for _ in 0..num_table_segments {
        let mut segment = Vec::with_capacity(segment_size);
        for _ in 0..segment_size {
            segment.push(P::ScalarField::rand(&mut rng));
        }
        segments.push(segment);
    }

    segments
}
fn rand_indices<P: Pairing>(num_table_segments: usize, num_witness_segments: usize) -> Vec<usize> {
    let mut rng = test_rng();

    let queried_segment_indices: Vec<usize> = (0..num_witness_segments)
        .map(|_| rng.next_u32() as usize % num_table_segments)
        .collect();

    queried_segment_indices
}

fn end_to_end(n: usize, s: usize, k: usize, &dummy: &bool) {
    println!("n={}, s={}, k={}", n, s, k);
    let segments = rand_table::<Bls12_381>(n, s);
    let mut rng = &mut test_rng();
    let mut curr_time = std::time::Instant::now();
    let pp = PublicParameters::builder()
        .num_table_segments(n)
        .num_witness_segments(k)
        .segment_size(s)
        .build(&mut rng, &dummy)
        .expect("Failed to setup public parameters");
    println!(
        "Setup time for n={:?} s={:?} k={:?} is [{:?}] ms",
        n,
        s,
        k,
        curr_time.elapsed().as_millis()
    );
    let table = Table::<Bls12_381>::new(&pp, segments).expect("Failed to create table");
    curr_time = std::time::Instant::now();
    let tpp = table
        .preprocess(&pp, &dummy)
        .expect("Failed to preprocess table");
    println!(
        "Table preprocess time for n={:?} s={:?} k={:?} is [{:?}] ms",
        n,
        s,
        k,
        curr_time.elapsed().as_millis()
    );
    let queried_segment_indices = rand_indices::<Bls12_381>(n, k);

    let witness = Witness::new(&pp, &tpp.adjusted_table_values, &queried_segment_indices).unwrap();
    let statement = witness.generate_statement(&pp.g1_affine_srs);

    let curr_time = std::time::Instant::now();
    let proof = prove(&pp, &tpp, &witness, statement, rng).expect("Failed to prove");
    println!(
        "Prove time for n={:?} s={:?} k={:?} is [{:?}] ms",
        n,
        s,
        k,
        curr_time.elapsed().as_millis()
    );


    let curr_time = std::time::Instant::now();
    let res = verify(&pp, &tpp, statement, &proof, rng);
    println!(
        "Verify time for n={:?} s={:?} k={:?} is [{:?}] ms",
        n,
        s,
        k,
        curr_time.elapsed().as_millis()
    );
    // assert!(res.is_ok());
}
fn main() {
    // let seg_powers: Vec<usize> = vec![16, 17, 18, 19, 20, 21, 22, 23, 24];
    // let seg_powers: Vec<usize> = vec![20];
    
    // // let segsizes: Vec<usize> = vec![1, 2, 4, 8, 16, 32, 64, 128, 256];
    // let segsizes: Vec<usize> = vec![4, 32];

    // // let witness_sizes: Vec<usize> = vec![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024];
    // // let witness_sizes: Vec<usize> = vec![1024]; //, 4, 8, 16, 32, 64, 128, 256, 512, 1024];
    // let witness_sizes: Vec<usize> = vec![4096, 16384];

    // 2^28 run out of memory
    // let table_powers: Vec<usize> = vec![
    //     16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 
    // ];
    let row_col_batch =  vec![
        (20, vec![
            (0, vec![4,10]),
            (2, vec![0,2,4,5,6,8,10,12,14]),
            (4, vec![4,10]),
            (5, vec![0,2,4,5,6,8,10,12,14]),
            (6, vec![4,10])
        ]),
    ];
    let dummy: bool = true;

    for i in 0..row_col_batch.len() {
        let log_row = row_col_batch[i].0;
        let col_batch = &row_col_batch[i].1;
        for j in 0..col_batch.len() {
            let log_col = col_batch[j].0;
            let log_batches = &col_batch[j].1;
            for k in 0..log_batches.len() {
                let log_batch = log_batches[k];
                end_to_end(1usize<<log_row, 1usize<<log_col, 1usize<<log_batch, &dummy);
            }
        }
    }
}
