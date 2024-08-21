use ark_ec::{PairingEngine, ProjectiveCurve};
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, UVPolynomial};

use crate::error::Error;
use crate::kzg::Kzg;
use crate::public_parameters::PublicParameters;
use crate::table::Table;

pub struct Witness<E: PairingEngine> {
    pub(crate) num_witness_segments: usize,
    pub(crate) segment_size: usize,
    pub(crate) poly_f: DensePolynomial<E::Fr>,
    pub(crate) poly_eval_list_f: Vec<E::Fr>,
    pub(crate) queried_segment_indices: Vec<usize>,
}

impl<E: PairingEngine> Witness<E> {
    pub fn new(
        pp: &PublicParameters<E>,
        table: &Table<E>,
        queried_segment_indices: &[usize],
    ) -> Result<Self, Error> {
        if queried_segment_indices.len() != pp.num_witness_segments {
            return Err(Error::InvalidNumberOfQueries(queried_segment_indices.len()));
        }

        let mut table_element_indices =
            Vec::with_capacity(pp.num_witness_segments * pp.segment_size);
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
            num_witness_segments: pp.num_witness_segments,
            segment_size: pp.segment_size,
            poly_f,
            poly_eval_list_f,
            queried_segment_indices: queried_segment_indices.to_vec(),
        })
    }

    pub fn generate_statement(&self, g1_srs: &[E::G1Affine]) -> E::G1Affine {
        Kzg::<E>::commit_g1(g1_srs, &self.poly_f).into_affine()
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
        let pp =
            PublicParameters::setup(&mut rng, 8, 4, 4).expect("Failed to setup public parameters");
        let segments = rand_segments::generate(&pp);

        let t = Table::<Bn254>::new(&pp, segments).expect("Failed to create table");

        let queried_segment_indices: Vec<usize> = (0..pp.num_witness_segments)
            .map(|_| rng.next_u32() as usize % pp.num_table_segments)
            .collect();

        Witness::new(&pp, &t, &queried_segment_indices).expect("Failed to create witness");
    }
}
