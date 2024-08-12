use ark_ec::PairingEngine;
use ark_poly::{EvaluationDomain, UVPolynomial};
use ark_poly::univariate::DensePolynomial;

use crate::error::Error;
use crate::public_parameters::PublicParameters;
use crate::table::Table;

pub struct Witness<E: PairingEngine> {
    num_queries: usize,
    segment_size: usize,
    poly_f: DensePolynomial<E::Fr>,
    pub(crate) poly_eval_list_f: Vec<E::Fr>,
    pub(crate) queried_segment_indices: Vec<usize>,
}

impl<E: PairingEngine> Witness<E> {
    pub fn new(pp: &PublicParameters<E>, table: &Table<E>, queried_segment_indices: &[usize]) -> Result<Self, Error> {
        if queried_segment_indices.len() != pp.num_queries {
            return Err(Error::InvalidNumberOfQueries(queried_segment_indices.len()));
        }

        let mut table_element_indices = Vec::with_capacity(pp.num_queries * pp.segment_size);
        for &segment_index in queried_segment_indices {
            for j in 0..pp.segment_size {
                let index = segment_index * pp.segment_size + j;
                if index >= table.values.len() {
                    return Err(Error::InvalidSegmentElementIndex(index));
                }

                table_element_indices.push(segment_index * pp.segment_size + j);
            }
        }

        let poly_eval_list_f: Vec<E::Fr> = table_element_indices
            .iter()
            .map(|&i| table.values[i])
            .collect();
        let poly_coeff_list_f = pp.domain_v.ifft(&poly_eval_list_f);
        let poly_f = DensePolynomial::from_coefficients_vec(poly_coeff_list_f);

        Ok(Self {
            num_queries: pp.num_queries,
            segment_size: pp.segment_size,
            poly_f,
            poly_eval_list_f,
            queried_segment_indices: queried_segment_indices.to_vec(),
        })
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;
    use ark_std::rand::RngCore;
    use ark_std::test_rng;

    use crate::table::rand_segments;

    use super::*;

    #[test]
    fn test_witness_new() {
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

        Witness::new(&pp, &t, &queried_segment_indices).expect("Failed to create witness");
    }
}