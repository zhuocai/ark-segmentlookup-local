use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, PrimeField};
use ark_poly::{EvaluationDomain, GeneralEvaluationDomain, UVPolynomial};
use ark_poly::univariate::DensePolynomial;
use fk::UpperToeplitz;

use crate::error::Error;
use crate::kzg::Kzg;
use crate::public_parameters::PublicParameters;

pub struct Table<E: PairingEngine> {
    size: usize,
    values: Vec<E::Fr>,
}

pub struct PreprocessedParameters<E: PairingEngine> {
    t_com2: E::G2Affine,
    quotient_poly_com1_vec_1: Vec<E::G1Affine>,
}

impl<E: PairingEngine> Table<E> {
    pub fn new(values: &[E::Fr]) -> Result<Self, Error> {
        assert!(values.len().is_power_of_two());

        if !values.len().is_power_of_two() {
            return Err(Error::SizeNotPowerOfTwo(values.len()));
        }

        Ok(Self {
            size: values.len(),
            values: values.to_vec(),
        })
    }

    pub fn preprocess(
        &self,
        pp: &PublicParameters<E>,
    ) -> Result<PreprocessedParameters<E>, Error> {
        assert_eq!(self.size, pp.table_size);

        let domain = pp.domain_w;
        let srs_g1 = &pp.srs_g1;
        let srs_g2 = &pp.srs_g2;

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
    domain: &GeneralEvaluationDomain<E::Fr>,
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
mod tests {
    use ark_bn254::Bn254;
    use ark_ec::PairingEngine;
    use ark_std::UniformRand;
    use crate::public_parameters::PublicParameters;
    use crate::table::Table;

    #[test]
    fn test_table_new() {
        let table_size = 8;
        let mut table_values: Vec<_> = Vec::with_capacity(table_size);
        let mut rng = ark_std::test_rng();
        for _ in 0..table_size {
            table_values.push(<Bn254 as PairingEngine>::Fr::rand(&mut rng));
        }
        Table::<Bn254>::new(&table_values).expect("Failed to create table");
    }

    #[test]
    fn test_table_preprocess() {
        let table_size = 32;
        let mut table_values: Vec<_> = Vec::with_capacity(table_size);
        let mut rng = ark_std::test_rng();
        for _ in 0..table_size {
            table_values.push(<Bn254 as PairingEngine>::Fr::rand(&mut rng));
        }
        let table = Table::<Bn254>::new(&table_values).expect("Failed to create table");
        let pp = PublicParameters::setup(&mut rng, 8, 4, 4).expect("Failed to setup public parameters");
        table.preprocess(&pp).expect("Failed to preprocess table");
    }
}
