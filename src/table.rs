use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, PrimeField};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain, UVPolynomial};
use ark_poly::univariate::DensePolynomial;
use fk::UpperToeplitz;

use crate::error::Error;
use crate::kzg::Kzg;
use crate::public_parameters::PublicParameters;

pub struct Table<E: PairingEngine> {
    num_segments: usize,
    segment_size: usize,
    pub(crate) values: Vec<E::Fr>,
}

pub struct PreprocessedParameters<E: PairingEngine> {
    t_com2: E::G2Affine,
    pub(crate) quotient_poly_com1_vec_1: Vec<E::G1Affine>,
}

impl<E: PairingEngine> Table<E> {
    pub fn new(pp: &PublicParameters<E>, segment_values: &[&[E::Fr]]) -> Result<Self, Error> {
        let num_segments = pp.num_segments;
        let segment_size = pp.segment_size;

        if segment_values.len() != num_segments {
            return Err(Error::InvalidNumerOfSegments(segment_values.len()));
        }

        let mut values = Vec::with_capacity(num_segments * segment_size);
        for segment in segment_values {
            if segment.len() != segment_size {
                return Err(Error::InvalidSegmentSize(segment.len()));
            }
            values.extend_from_slice(segment);
        }


        Ok(Self {
            num_segments,
            segment_size,
            values,
        })
    }

    pub fn preprocess(
        &self,
        pp: &PublicParameters<E>,
    ) -> Result<PreprocessedParameters<E>, Error> {
        if self.num_segments != pp.num_segments {
            return Err(Error::InvalidNumerOfSegments(self.num_segments));
        }

        if self.segment_size != pp.segment_size {
            return Err(Error::InvalidSegmentSize(self.segment_size));
        }

        let domain = pp.domain_w;
        let srs_g1 = &pp.g1_srs;
        let srs_g2 = &pp.g2_srs;

        let table_poly = DensePolynomial::from_coefficients_slice(&domain.ifft(&self.values));
        let t_2: E::G2Affine = Kzg::<E>::commit_g2(srs_g2, &table_poly).into();
        let qs1 = match compute_quotients::<E>(&table_poly, &domain, srs_g1) {
            Ok(qs) => qs,
            Err(e) => return Err(e),
        };

        Ok(PreprocessedParameters {
            t_com2: t_2,
            quotient_poly_com1_vec_1: qs1,
        })
    }
}

fn compute_quotients<E: PairingEngine>(
    t: &DensePolynomial<E::Fr>,
    domain: &Radix2EvaluationDomain<E::Fr>,
    srs_g1: &[E::G1Affine],
) -> Result<Vec<E::G1Affine>, Error> {
    /*
        - N (table size) is always pow2
        - Toeplitz multiplication will happen in 2 * N, so appending zero commitments on hs is not needed
    */
    let toeplitz = UpperToeplitz::from_poly(t);

    let mut srs_proj: Vec<E::G1Projective> = srs_g1.iter().map(|t| t.into_projective()).collect();
    srs_proj.reverse();

    let h_commitments: Vec<E::G1Projective> = toeplitz.mul_by_vec(&srs_proj);
    if h_commitments.len() != 2 * domain.size() {
        return Err(Error::InvalidCommitmentLength(format!(
            "Expected h_commitments length to be {}, but was {}",
            2 * domain.size(),
            h_commitments.len()
        )));
    }

    let ks: Vec<_> = domain.fft(&h_commitments[..domain.size()]);

    let n_inv = domain.size_as_field_element()
        .inverse()
        .ok_or(Error::FailedToInverseFieldElement)?;
    let normalized_roots: Vec<E::Fr> = domain.elements().map(|g_i| g_i * n_inv).collect();

    let mut qs: Vec<E::G1Projective> = ks
        .iter()
        .zip(normalized_roots)
        .map(|(ki, normalizer_i)| ki.mul(normalizer_i.into_repr()))
        .collect();

    E::G1Projective::batch_normalization(&mut qs);

    Ok(qs.iter().map(|qi| qi.into_affine()).collect())
}

#[cfg(test)]
pub mod rand_segments {
    use ark_bn254::Bn254;
    use ark_ec::PairingEngine;
    use ark_std::UniformRand;

    use crate::public_parameters::PublicParameters;

    pub fn generate(pp: &PublicParameters<Bn254>) -> Vec<Vec<<Bn254 as PairingEngine>::Fr>> {
        let mut rng = ark_std::test_rng();
        let mut segments = Vec::with_capacity(pp.num_segments);
        for _ in 0..pp.num_segments {
            let mut segment = Vec::with_capacity(pp.segment_size);
            for _ in 0..pp.segment_size {
                segment.push(<Bn254 as PairingEngine>::Fr::rand(&mut rng));
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
        let pp = PublicParameters::setup(&mut rng, 8, 4, 4)
            .expect("Failed to setup public parameters");
        let segments = rand_segments::generate(&pp);
        let segment_slices: Vec<&[<Bn254 as PairingEngine>::Fr]> = segments
            .iter()
            .map(|segment| segment.as_slice())
            .collect();

        Table::<Bn254>::new(&pp, &segment_slices).expect("Failed to create table");
    }

    #[test]
    fn test_table_preprocess() {
        let mut rng = test_rng();
        let pp = PublicParameters::setup(&mut rng, 8, 4, 4)
            .expect("Failed to setup public parameters");
        let segments = rand_segments::generate(&pp);
        let segment_slices: Vec<&[<Bn254 as PairingEngine>::Fr]> = segments
            .iter()
            .map(|segment| segment.as_slice())
            .collect();
        let t = Table::<Bn254>::new(&pp, &segment_slices)
            .expect("Failed to create table");

        t.preprocess(&pp).expect("Failed to preprocess table");
    }
}
