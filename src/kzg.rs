use std::{iter, marker::PhantomData};
use std::cmp::max;

use ark_ec::{AffineCurve, msm::VariableBaseMSM, PairingEngine};
use ark_ff::{One, PrimeField};
use ark_poly::{Polynomial, univariate::DensePolynomial, UVPolynomial};
use ark_std::rand::RngCore;
use ark_std::UniformRand;

/// Minimal KZG functionalities needed for cq
/// Modified from https://github.com/geometryxyz/cq/blob/main/src/kzg.rs
pub struct Kzg<E: PairingEngine> {
    _e: PhantomData<E>,
}

impl<E: PairingEngine> Kzg<E> {
    pub fn commit_g1(srs: &[E::G1Affine], poly: &DensePolynomial<E::Fr>) -> E::G1Projective {
        if srs.len() - 1 < poly.degree() {
            panic!(
                "SRS size to small! Can't commit to polynomial of degree {} with srs of size {}",
                poly.degree(),
                srs.len()
            );
        }
        let coefficient_scalars: Vec<_> = poly.coeffs.iter().map(|c| c.into_repr()).collect();
        VariableBaseMSM::multi_scalar_mul(srs, &coefficient_scalars)
    }

    pub fn commit_g2(srs: &[E::G2Affine], poly: &DensePolynomial<E::Fr>) -> E::G2Projective {
        if srs.len() - 1 < poly.degree() {
            panic!(
                "SRS size to small! Can't commit to polynomial of degree {} with srs of size {}",
                poly.degree(),
                srs.len()
            );
        }
        let coeff_scalars: Vec<_> = poly.coeffs.iter().map(|c| c.into_repr()).collect();
        VariableBaseMSM::multi_scalar_mul(srs, &coeff_scalars)
    }

    pub fn open_g1(
        srs: &[E::G1Affine],
        poly: &DensePolynomial<E::Fr>,
        challenge: E::Fr,
    ) -> (E::Fr, E::G1Affine) {
        let q = poly / &DensePolynomial::from_coefficients_slice(&[-challenge, E::Fr::one()]);
        if srs.len() - 1 < q.degree() {
            panic!(
                "Open g1: SRS size to small! Can't commit to polynomial of degree {} with srs of size {}",
                q.degree(),
                srs.len()
            );
        }
        let proof = Self::commit_g1(srs, &q);
        (poly.evaluate(&challenge), proof.into())
    }

    pub fn batch_open_g1(
        srs: &[E::G1Affine],
        polys: &[DensePolynomial<E::Fr>],
        opening_challenge: E::Fr,
        separation_challenge: E::Fr,
    ) -> E::G1Affine {
        let powers_of_gamma = iter::successors(Some(separation_challenge), |p| {
            Some(*p * separation_challenge)
        });

        let mut batched = polys[0].clone();
        for (p_i, gamma_pow_i) in polys.iter().skip(1).zip(powers_of_gamma) {
            batched += (gamma_pow_i, p_i);
        }

        let q = &batched
            / &DensePolynomial::from_coefficients_slice(&[-opening_challenge, E::Fr::one()]);

        if srs.len() - 1 < q.degree() {
            panic!(
                "Batch open g1: SRS size to small! Can't commit to polynomial of degree {} with srs of size {}",
                q.degree(),
                srs.len()
            );
        }

        Self::commit_g1(srs, &q).into()
    }
}

/// Create srs from rng
pub fn unsafe_setup_from_rng<E: PairingEngine, R: RngCore>(
    max_power_g1: usize,
    max_power_g2: usize,
    rng: &mut R,
) -> (Vec<E::G1Affine>, Vec<E::G2Affine>) {
    let tau = E::Fr::rand(rng);

    unsafe_setup_from_tau::<E, R>(max_power_g1, max_power_g2, tau)
}

/// Create srs from specific tau
pub fn unsafe_setup_from_tau<E: PairingEngine, R: RngCore>(
    max_power_g1: usize,
    max_power_g2: usize,
    tau: E::Fr,
) -> (Vec<E::G1Affine>, Vec<E::G2Affine>) {
    let powers_of_tau_size = max(max_power_g1 + 1, max_power_g2 + 1);
    let powers_of_tau = powers_of_tau::<E>(tau, powers_of_tau_size);
    let srs_g1 = srs::<E::G1Affine>(&powers_of_tau, max_power_g1);
    let srs_g2 = srs::<E::G2Affine>(&powers_of_tau, max_power_g2);

    (srs_g1, srs_g2)
}

fn powers_of_tau<E: PairingEngine>(tau: E::Fr, size: usize) -> Vec<E::Fr> {
    iter::successors(Some(E::Fr::one()), |p| Some(*p * tau))
        .take(size)
        .collect()
}

fn srs<AC: AffineCurve>(powers_of_tau: &[AC::ScalarField], max_power: usize) -> Vec<AC> {
    let generator = AC::prime_subgroup_generator();

    powers_of_tau
        .iter()
        .take(max_power + 1)
        .map(|tp| generator.mul(tp.into_repr()).into())
        .collect()
}
