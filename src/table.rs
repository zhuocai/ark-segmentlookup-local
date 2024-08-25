use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Field;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, EvaluationDomain, Radix2EvaluationDomain};
use std::ops::Mul;

use crate::error::Error;
use crate::kzg::Kzg;
use crate::public_parameters::PublicParameters;
use crate::toeplitz::UpperToeplitz;

pub struct Table<P: Pairing> {
    num_segments: usize,
    segment_size: usize,
    pub(crate) values: Vec<P::ScalarField>,
}

pub struct TablePreprocessedParameters<P: Pairing> {
    pub(crate) g2_t: P::G2Affine,
    pub(crate) g1_q1_list: Vec<P::G1Affine>,
}

impl<P: Pairing> Table<P> {
    pub fn new(
        pp: &PublicParameters<P>,
        segment_values: Vec<Vec<P::ScalarField>>,
    ) -> Result<Self, Error> {
        let num_segments = pp.num_table_segments;
        let segment_size = pp.segment_size;

        if segment_values.len() != num_segments {
            return Err(Error::InvalidNumberOfSegments(segment_values.len()));
        }

        let mut values = Vec::with_capacity(num_segments * segment_size);
        for segment in segment_values {
            if segment.len() != segment_size {
                return Err(Error::InvalidSegmentSize(segment.len()));
            }
            values.extend_from_slice(&segment);
        }

        Ok(Self {
            num_segments,
            segment_size,
            values,
        })
    }

    pub fn preprocess(
        &self,
        pp: &PublicParameters<P>,
    ) -> Result<TablePreprocessedParameters<P>, Error> {
        if self.num_segments != pp.num_table_segments {
            return Err(Error::InvalidNumberOfSegments(self.num_segments));
        }

        if self.segment_size != pp.segment_size {
            return Err(Error::InvalidSegmentSize(self.segment_size));
        }

        let domain = pp.domain_w;
        let srs_g1 = &pp.g1_srs;
        let srs_g2 = &pp.g2_srs;

        let table_poly = DensePolynomial::from_coefficients_slice(&domain.ifft(&self.values));
        let t_2: P::G2Affine = Kzg::<P::G2>::commit_g2(srs_g2, &table_poly).into();
        let qs1 = compute_quotients::<P>(&table_poly, &domain, srs_g1)?;

        Ok(TablePreprocessedParameters {
            g2_t: t_2,
            g1_q1_list: qs1,
        })
    }
}

fn compute_quotients<P: Pairing>(
    t: &DensePolynomial<P::ScalarField>,
    domain: &Radix2EvaluationDomain<P::ScalarField>,
    srs_g1: &[P::G1Affine],
) -> Result<Vec<P::G1Affine>, Error> {
    /*
        - N (table size) is always pow2
        - Toeplitz multiplication will happen in 2 * N, so appending zero commitments on hs is not needed
    */
    let toeplitz = UpperToeplitz::from_poly(t);

    let domain_size = domain.size();
    let srs_g1 = srs_g1.iter().take(domain_size).collect::<Vec<_>>();
    let mut srs_proj: Vec<P::G1> = srs_g1.iter().map(|t| t.into_group()).collect();
    srs_proj.reverse();

    let h_commitments: Vec<P::G1> = toeplitz.mul_by_vec(&srs_proj);
    if h_commitments.len() != 2 * domain_size {
        return Err(Error::InvalidCommitmentLength(format!(
            "Expected h_commitments length to be {}, but was {}",
            2 * domain.size(),
            h_commitments.len()
        )));
    }

    let ks: Vec<_> = domain.fft(&h_commitments[..domain.size()]);

    let fr_inv_n = domain
        .size_as_field_element()
        .inverse()
        .ok_or(Error::FailedToInverseFieldElement)?;
    let normalized_roots: Vec<P::ScalarField> =
        domain.elements().map(|g_i| g_i * fr_inv_n).collect();

    let qs: Vec<P::G1> = ks
        .iter()
        .zip(normalized_roots)
        .map(|(ki, normalizer_i)| ki.mul(normalizer_i))
        .collect();

    // Ok(P::G1::batch_normalization_into_affine(&mut qs))
    Ok(P::G1::normalize_batch(&qs))
}

#[cfg(test)]
pub mod rand_segments {
    use ark_ec::pairing::Pairing;
    use ark_std::UniformRand;

    use crate::public_parameters::PublicParameters;

    pub fn generate<P: Pairing>(pp: &PublicParameters<P>) -> Vec<Vec<P::ScalarField>> {
        let mut rng = ark_std::test_rng();
        let mut segments = Vec::with_capacity(pp.num_table_segments);
        for _ in 0..pp.num_table_segments {
            let mut segment = Vec::with_capacity(pp.segment_size);
            for _ in 0..pp.segment_size {
                segment.push(P::ScalarField::rand(&mut rng));
            }
            segments.push(segment);
        }

        segments
    }
}

#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;
    use ark_std::test_rng;

    use super::*;

    #[test]
    fn test_table_new() {
        let mut rng = test_rng();
        let pp =
            PublicParameters::setup(&mut rng, 8, 4, 4).expect("Failed to setup public parameters");
        let segments = rand_segments::generate::<Bn254>(&pp);

        Table::<Bn254>::new(&pp, segments).expect("Failed to create table");
    }

    #[test]
    fn test_table_preprocess() {
        let mut rng = test_rng();
        let pp =
            PublicParameters::setup(&mut rng, 8, 4, 4).expect("Failed to setup public parameters");
        let segments = rand_segments::generate(&pp);

        let t = Table::<Bn254>::new(&pp, segments).expect("Failed to create table");

        t.preprocess(&pp).expect("Failed to preprocess table");
    }
}
