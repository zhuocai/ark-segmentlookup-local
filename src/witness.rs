use ark_ec::pairing::Pairing;
use ark_ec::CurveGroup;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, EvaluationDomain};

use crate::error::Error;
use crate::kzg::Kzg;
use crate::public_parameters::PublicParameters;

pub struct Witness<P: Pairing> {
    pub num_segments: usize,
    pub segment_size: usize,
    pub segment_indices: Vec<usize>,
    pub poly: DensePolynomial<P::ScalarField>,
    pub evaluations: Vec<P::ScalarField>,
}

impl<P: Pairing> Witness<P> {
    pub fn new(
        pp: &PublicParameters<P>,
        table_values: &[P::ScalarField],
        queried_segment_indices: &[usize],
    ) -> Result<Self, Error> {
        if queried_segment_indices.len() != pp.num_witness_segments {
            println!(
                "queried_segment_indices.len() != pp.num_witness_segments \n===> Queried segment indices: {:?}",
                queried_segment_indices
            );
            return Err(Error::InvalidNumberOfQueries(queried_segment_indices.len()));
        }

        let mut table_element_indices =
            Vec::with_capacity(pp.num_witness_segments * pp.segment_size);
        for &segment_index in queried_segment_indices {
            for j in 0..pp.segment_size {
                let index = segment_index * pp.segment_size + j;
                if index >= table_values.len() {
                    println!(
                        "index >= table_values.len() \n===> index: {:?}, table_values.len(): {:?}",
                        index,
                        table_values.len()
                    );
                    return Err(Error::InvalidSegmentElementIndex(index));
                }

                table_element_indices.push(segment_index * pp.segment_size + j);
            }
        }

        let poly_eval_list_f: Vec<P::ScalarField> = table_element_indices
            .iter()
            .map(|&i| table_values[i])
            .collect();
        let poly_coeff_list_f = pp.domain_v.ifft(&poly_eval_list_f);
        let poly_f = DensePolynomial::from_coefficients_vec(poly_coeff_list_f);

        Ok(Self {
            num_segments: pp.num_witness_segments,
            segment_size: pp.segment_size,
            poly: poly_f,
            evaluations: poly_eval_list_f,
            segment_indices: queried_segment_indices.to_vec(),
        })
    }

    pub fn generate_statement(&self, g1_srs: &[P::G1Affine]) -> P::G1Affine {
        Kzg::<P::G1>::commit(g1_srs, &self.poly).into_affine()
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;
    use ark_std::rand::RngCore;
    use ark_std::test_rng;

    use crate::table::{rand_segments, Table};

    use super::*;

    #[test]
    fn test_witness_new() {
        let mut rng = test_rng();
        let pp = PublicParameters::builder()
            .num_table_segments(8)
            .num_witness_segments(4)
            .segment_size(4)
            .build(&mut rng)
            .expect("Failed to setup public parameters");
        let segments = rand_segments::generate(&pp);

        let t = Table::<Bn254>::new(&pp, segments).expect("Failed to create table");

        let queried_segment_indices: Vec<usize> = (0..pp.num_witness_segments)
            .map(|_| rng.next_u32() as usize % pp.num_table_segments)
            .collect();

        Witness::new(&pp, &t.values, &queried_segment_indices).expect("Failed to create witness");
    }
}
