use crate::error::Error;
use crate::kzg::Kzg;
use crate::public_parameters::PublicParameters;
use crate::toeplitz::UpperToeplitz;
use crate::COMPRESS_MOD;
use ark_ec::pairing::Pairing;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::Field;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{DenseUVPolynomial, EvaluationDomain, Polynomial, Radix2EvaluationDomain};
use ark_serialize::CanonicalSerialize;
use ark_std::rand::rngs::StdRng;
use ark_std::rand::Rng;
use ark_std::{One, UniformRand, Zero};
use blake2::{Blake2b512, Digest};
use rayon::prelude::*;
use std::ops::Mul;

pub struct Table<P: Pairing> {
    pub num_segments: usize,
    pub segment_size: usize,
    pub values: Vec<P::ScalarField>,
}

pub struct TablePreprocessedParameters<P: Pairing> {
    pub(crate) g1_affine_list_q1: Vec<P::G1Affine>,
    pub g1_affine_d: P::G1Affine,
    // pub(crate) g2_affine_t: P::G2Affine,
    pub(crate) g2_affine_adjusted_t: P::G2Affine,
    pub adjusted_table_values: Vec<P::ScalarField>,

    pub(crate) hash_representation: Vec<u8>,
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
        dummy: &bool,
    ) -> Result<TablePreprocessedParameters<P>, Error> {
        if self.num_segments != pp.num_table_segments {
            return Err(Error::InvalidNumberOfSegments(self.num_segments));
        }

        if self.segment_size != pp.segment_size {
            return Err(Error::InvalidSegmentSize(self.segment_size));
        }
        if (!dummy) {
            let domain = pp.domain_w;
            let g1_affine_srs = &pp.g1_affine_srs;
            let g2_affine_srs = &pp.g2_affine_srs;

            let table_poly = DensePolynomial::from_coefficients_slice(&domain.ifft(&self.values));
            let g2_t = Kzg::<P::G2>::commit(g2_affine_srs, &table_poly);

            // TODO: Make this a feature.
            // Make-Unique process.
            // Find T_{max}.
            let max_absolute_value = self
                .values
                .par_iter()
                .map(|&value| {
                    let abs_value = if value < P::ScalarField::zero() {
                        -value
                    } else {
                        value
                    };
                    abs_value
                })
                .max()
                .unwrap_or(P::ScalarField::zero());
            // T'(X) = T(X) + E(X)
            let fr_two = P::ScalarField::from(2u128);
            let fr_max_abs_add_one = max_absolute_value + P::ScalarField::one(); // T_{max} + 1
            let num_table_segments = pp.num_table_segments;
            let segment_size = pp.segment_size;
            let adjusted_table_values = self
                .values
                .par_iter()
                .zip(0..num_table_segments * segment_size)
                .map(|(&t_i, i)| {
                    let fr_j = P::ScalarField::from((i % segment_size) as u128);
                    let e_i = fr_two * fr_j * fr_max_abs_add_one;
                    let adjusted_t_i = t_i + e_i;

                    adjusted_t_i
                })
                .collect::<Vec<_>>();
            let poly_coeff_list_adjusted_t = pp.domain_w.ifft(&adjusted_table_values);
            let poly_adjusted_t =
                DensePolynomial::from_coefficients_vec(poly_coeff_list_adjusted_t);
            let g2_adjusted_t = Kzg::<P::G2>::commit(&pp.g2_affine_srs, &poly_adjusted_t);

            let g2_affine_list = P::G2::normalize_batch(&[g2_t, g2_adjusted_t]);
            let g2_affine_t = g2_affine_list[0];
            let g2_affine_adjusted_t = g2_affine_list[1];

            let g1_affine_list_q1 =
                compute_quotients::<P>(&poly_adjusted_t, &domain, g1_affine_srs)?;

            let num_witness_segments = pp.num_witness_segments;
            let mut poly_eval_list_d = (0..num_witness_segments * segment_size)
                .into_par_iter()
                .map(|i| {
                    let fr_j = P::ScalarField::from((i % segment_size) as u128);
                    let d_i = fr_two * fr_j * fr_max_abs_add_one;

                    d_i
                })
                .collect::<Vec<_>>();
            pp.domain_v.ifft_in_place(&mut poly_eval_list_d);
            let poly_coeff_list_d = poly_eval_list_d;
            let poly_d = DensePolynomial::from_coefficients_vec(poly_coeff_list_d);
            let g1_affine_d = Kzg::<P::G1>::commit(&pp.g1_affine_srs, &poly_d).into_affine();

            let mut buffer = Vec::new();
            let mut hasher = Blake2b512::new();

            g1_affine_d
                .serialize_with_mode(&mut buffer, COMPRESS_MOD)
                .map_err(|_| Error::FailedToSerializeElement)?;
            g2_affine_t
                .serialize_with_mode(&mut buffer, COMPRESS_MOD)
                .map_err(|_| Error::FailedToSerializeElement)?;
            g2_affine_adjusted_t
                .serialize_with_mode(&mut buffer, COMPRESS_MOD)
                .map_err(|_| Error::FailedToSerializeElement)?;

            hasher.update(&buffer);
            let hash_representation = hasher.finalize().to_vec();

            Ok(TablePreprocessedParameters {
                g1_affine_list_q1,
                // g2_affine_t,
                g2_affine_adjusted_t,
                g1_affine_d,
                adjusted_table_values,
                hash_representation,
            })
        } else {
            // Dummy preprocessing
            let mut rng = ark_std::test_rng();
            let g1r = P::G1Affine::rand(&mut rng);
            let g2r = P::G2Affine::rand(&mut rng);
            let fr = P::ScalarField::rand(&mut rng);
            let g1_affine_list_q1 = vec![g1r; pp.domain_w.size()];
            let g2_affine_adjusted_t = g2r.clone();
            let g1_affine_d = g1r.clone();
            let adjusted_table_values = vec![fr; pp.num_table_segments*pp.segment_size];
            let hash_representation = "dummy".as_bytes().to_vec();


            Ok(TablePreprocessedParameters {
                g1_affine_list_q1,
                // g2_affine_t,
                g2_affine_adjusted_t,
                g1_affine_d,
                adjusted_table_values,
                hash_representation,
            })
        }
    }
}

fn compute_quotients<P: Pairing>(
    poly_t: &DensePolynomial<P::ScalarField>,
    domain: &Radix2EvaluationDomain<P::ScalarField>,
    g1_affine_srs: &[P::G1Affine],
) -> Result<Vec<P::G1Affine>, Error> {
    /*
        - N (table size) is always pow2
        - Toeplitz multiplication will happen in 2 * N, so appending zero commitments on hs is not needed
    */
    if poly_t.degree() >= domain.size() {
        return Err(Error::InvalidPolynomialDegree(poly_t.degree()));
    }

    // Resize the polynomial coefficients to the domain size
    let mut poly_t_coeffs = poly_t.coeffs().to_vec();
    poly_t_coeffs.resize(domain.size(), P::ScalarField::zero());

    let toeplitz = UpperToeplitz::from_coeff_slice(&poly_t_coeffs);

    let domain_size = domain.size();
    let g1_affine_srs = g1_affine_srs.iter().take(domain_size).collect::<Vec<_>>();
    let mut g1_srs: Vec<P::G1> = g1_affine_srs.par_iter().map(|t| t.into_group()).collect();
    g1_srs.reverse();

    let g1_list_h: Vec<P::G1> = toeplitz.mul_by_vec(&g1_srs);
    if g1_list_h.len() != 2 * domain_size {
        return Err(Error::InvalidCommitmentLength(format!(
            "Expected h_commitments length to be {}, but was {}",
            2 * domain.size(),
            g1_list_h.len()
        )));
    }

    let ks: Vec<_> = domain.fft(&g1_list_h[..domain.size()]);

    let fr_inv_n = domain
        .size_as_field_element()
        .inverse()
        .ok_or(Error::FailedToInverseFieldElement)?;
    let normalized_roots: Vec<P::ScalarField> = domain
        .elements()
        .collect::<Vec<_>>()
        .par_iter()
        .map(|&g_i| g_i * fr_inv_n)
        .collect();

    let qs: Vec<P::G1> = ks
        .par_iter()
        .zip(normalized_roots)
        .map(|(ki, normalizer_i)| ki.mul(normalizer_i))
        .collect();

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
    use ark_bls12_381::Bls12_381;
    use ark_std::test_rng;

    use super::*;

    #[test]
    fn test_table_new() {
        let mut rng = test_rng();
        let pp = PublicParameters::builder()
            .num_table_segments(8)
            .num_witness_segments(4)
            .segment_size(4)
            .build(&mut rng)
            .expect("Failed to setup public parameters");
        let segments = rand_segments::generate::<Bls12_381>(&pp);

        Table::<Bls12_381>::new(&pp, segments).expect("Failed to create table");
    }

    #[test]
    fn test_table_preprocess() {
        let mut rng = test_rng();
        let pp = PublicParameters::builder()
            .num_table_segments(8)
            .num_witness_segments(4)
            .segment_size(4)
            .build(&mut rng)
            .expect("Failed to setup public parameters");
        let segments = rand_segments::generate(&pp);

        let t = Table::<Bls12_381>::new(&pp, segments).expect("Failed to create table");

        t.preprocess(&pp).expect("Failed to preprocess table");
    }
}
