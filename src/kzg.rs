use crate::error::Error;
use ark_ec::pairing::Pairing;
use ark_ec::VariableBaseMSM;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{FftField, Field, One};
use ark_poly::{univariate::DensePolynomial, DenseUVPolynomial, Polynomial};
use ark_std::rand::Rng;
use ark_std::{UniformRand, Zero};
use rayon::prelude::*;
use std::cmp::max;
use std::marker::PhantomData;
use std::ops::Mul;

/// Minimal KZG functionalities needed for the lookup argument.
///
/// This module provides functionalities to commit to polynomials,
/// open evaluations, and verify proofs using KZG commitments.
///
/// Adapted from:
/// - [geometryxyz/cq](https://github.com/geometryxyz/cq/blob/main/src/kzg.rs)
/// - [caulk-crypto/caulk](https://github.com/caulk-crypto/caulk/blob/main/src/kzg.rs)
pub struct Kzg<C: CurveGroup> {
    _marker: PhantomData<C>,
}

impl<C: CurveGroup> Kzg<C> {
    pub fn commit(affine_srs: &[C::Affine], poly: &DensePolynomial<C::ScalarField>) -> C {
        if affine_srs.len() - 1 < poly.degree() {
            panic!(
                "SRS size to small! Can't commit to polynomial of degree {} with srs of size {}",
                poly.degree(),
                affine_srs.len()
            );
        }

        VariableBaseMSM::msm_unchecked(affine_srs, &poly.coeffs)
    }

    pub fn commit_with_offset(
        affine_srs: &[C::Affine],
        poly: &DensePolynomial<C::ScalarField>,
        offset: usize,
    ) -> C {
        let affine_srs = &affine_srs[offset..];

        if affine_srs.len() - 1 < poly.degree() {
            panic!(
                "SRS size to small! Can't commit to polynomial of degree {} with srs of size {}",
                poly.degree(),
                affine_srs.len()
            );
        }

        VariableBaseMSM::msm_unchecked(affine_srs, &poly.coeffs)
    }

    pub fn open(
        affine_srs: &[C::Affine],
        poly: &DensePolynomial<C::ScalarField>,
        challenge: C::ScalarField,
    ) -> (C::ScalarField, C::Affine) {
        let q =
            poly / &DensePolynomial::from_coefficients_slice(&[-challenge, C::ScalarField::one()]);
        if affine_srs.len() - 1 < q.degree() {
            panic!(
                "Open g1: SRS size to small! Can't commit to polynomial of degree {} with srs of size {}",
                q.degree(),
                affine_srs.len()
            );
        }
        let proof = Self::commit(affine_srs, &q);

        (poly.evaluate(&challenge), proof.into())
    }

    pub fn batch_open(
        affine_srs: &[C::Affine],
        poly_list: &[DensePolynomial<C::ScalarField>],
        fr_opening: C::ScalarField,
        fr_separation: C::ScalarField,
    ) -> C::Affine {
        let num_polys = poly_list.len();
        let powers_of_sep = powers_of_scalars::<C::ScalarField>(fr_separation, num_polys);

        let mut batched = poly_list[0].clone();
        let rest_batched: DensePolynomial<C::ScalarField> = poly_list[1..]
            .par_iter()
            .zip(powers_of_sep.par_iter().skip(1))
            .map(|(p_i, &fr_sep_pow_i)| {
                p_i * fr_sep_pow_i // Multiply each polynomial by its
                                   // corresponding power of `fr_separation`
            })
            .reduce(
                || DensePolynomial::from_coefficients_slice(&[C::ScalarField::zero()]),
                |a, b| a + b,
            );
        batched += &rest_batched;

        let q = &batched
            / &DensePolynomial::from_coefficients_slice(&[-fr_opening, C::ScalarField::one()]);

        if affine_srs.len() - 1 < q.degree() {
            panic!(
                "Batch open g1: SRS size to small! Can't commit to polynomial of degree {} with srs of size {}",
                q.degree(),
                affine_srs.len()
            );
        }

        Self::commit(affine_srs, &q).into()
    }
}

/// Create srs from rng
pub fn unsafe_setup_from_rng<P: Pairing, R: Rng + ?Sized>(
    max_power_g1: usize,
    max_power_caulk_g1: usize,
    rng: &mut R,
) -> (
    Vec<P::G1Affine>,
    Vec<P::G2Affine>,
    Vec<P::G1Affine>,
    Vec<P::G2Affine>,
) {
    let tau = P::ScalarField::rand(rng);

    unsafe_setup_from_tau::<P, R>(max_power_g1, max_power_caulk_g1, tau)
}

/// Create srs from specific tau
pub fn unsafe_setup_from_tau<P: Pairing, R: Rng + ?Sized>(
    max_power_g1: usize,
    caulk_max_power_g1: usize,
    tau: P::ScalarField,
) -> (
    Vec<P::G1Affine>,
    Vec<P::G2Affine>,
    Vec<P::G1Affine>,
    Vec<P::G2Affine>,
) {
    let max_power_g2 = max_power_g1 + 1;
    let max_power_caulk_g2 = caulk_max_power_g1 + 1;
    let powers_of_tau_size = max(max_power_g2 + 1, max_power_caulk_g2 + 1);
    let powers_of_tau = powers_of_scalars::<P::ScalarField>(tau, powers_of_tau_size);
    let g1_srs = srs::<P::G1>(&powers_of_tau, max_power_g1);
    let g2_srs = srs::<P::G2>(&powers_of_tau, max_power_g2);
    let g1_srs_caulk = srs::<P::G1>(&powers_of_tau, caulk_max_power_g1);
    let g2_srs_caulk = srs::<P::G2>(&powers_of_tau, max_power_caulk_g2);

    (g1_srs, g2_srs, g1_srs_caulk, g2_srs_caulk)
}

const CHUNK_SIZE: usize = 1024;

fn powers_of_scalars<F: FftField>(s: F, size: usize) -> Vec<F> {
    let num_chunks = (size + CHUNK_SIZE - 1) / CHUNK_SIZE;

    let mut result: Vec<F> = (0..num_chunks)
        .into_par_iter()
        .flat_map(|chunk_index| {
            let start_power = chunk_index * CHUNK_SIZE;
            let mut chunk = Vec::with_capacity(CHUNK_SIZE.min(size - start_power));
            let mut power = s.pow(&[start_power as u64]);

            for _ in 0..CHUNK_SIZE.min(size - start_power) {
                chunk.push(power);
                power *= s;
            }
            chunk
        })
        .collect();

    result.truncate(size);

    result
}

fn srs<C: CurveGroup>(powers_of_tau: &[C::ScalarField], max_power: usize) -> Vec<C::Affine> {
    let generator = C::Affine::generator();

    powers_of_tau
        .par_iter()
        .take(max_power + 1)
        .map(|tp| generator.mul(tp).into())
        .collect()
}

pub struct CaulkKzg<P: Pairing> {
    _marker: PhantomData<P>,
}

impl<P: Pairing> CaulkKzg<P> {
    pub fn open_g1(
        affine_srs: &[P::G1Affine],
        poly: &DensePolynomial<P::ScalarField>,
        max_deg: Option<&usize>,
        challenge: &P::ScalarField,
    ) -> (P::ScalarField, P::G1Affine) {
        if poly.is_zero() {
            return (P::ScalarField::zero(), P::G1Affine::zero());
        }
        let eval = poly.evaluate(challenge);

        let global_max_deg = affine_srs.len();

        let mut d: usize = 0;
        if max_deg == None {
            d += global_max_deg;
        } else {
            d += max_deg.unwrap();
        }
        let divisor =
            DensePolynomial::from_coefficients_vec(vec![-*challenge, P::ScalarField::one()]);
        let witness_polynomial = poly / &divisor;

        assert!(affine_srs[(global_max_deg - d)..].len() >= witness_polynomial.len());
        let proof = P::G1::msm_unchecked(
            &affine_srs[(global_max_deg - d)..],
            &witness_polynomial.coeffs,
        )
        .into_affine();

        (eval, proof)
    }

    pub fn bi_poly_commit_g1(
        g1_affine_srs: &[P::G1Affine],
        polynomials: &[DensePolynomial<P::ScalarField>],
        degree_offset: usize,
    ) -> Result<P::G1Affine, Error> {
        if polynomials.is_empty() {
            return Ok(P::G1Affine::zero());
        }

        let degree_offset = degree_offset.next_power_of_two();

        let final_poly_size = degree_offset * polynomials.len();
        if final_poly_size > g1_affine_srs.len() {
            return Err(Error::InvalidStructuredReferenceStrings);
        }

        let g1_poly = polynomials
            .par_iter()
            .enumerate()
            .map(|(i, poly)| {
                let offset_srs = &g1_affine_srs[i * degree_offset..(i + 1) * degree_offset];
                P::G1::msm_unchecked(offset_srs, &poly.coeffs)
            })
            .reduce(P::G1::zero, |a, b| a + b);

        Ok(g1_poly.into_affine())
    }

    pub fn batch_open_g1(
        g1_affine_srs: &[P::G1Affine],
        poly: &DensePolynomial<P::ScalarField>,
        max_deg: Option<&usize>,
        points: &[P::ScalarField],
    ) -> (Vec<P::ScalarField>, P::G1Affine) {
        if poly.is_zero() {
            return (
                vec![P::ScalarField::zero(); points.len()],
                P::G1Affine::zero(),
            );
        }

        let (evaluations, proofs): (Vec<_>, Vec<_>) = points
            .par_iter()
            .map(|p| Self::open_g1(g1_affine_srs, poly, max_deg, p))
            .unzip();

        // Parallelize the second loop (computing summations)
        let res = points
            .par_iter()
            .enumerate()
            .map(|(j, w_j)| {
                // Compute the coefficient [1/prod]
                let mut prod = P::ScalarField::one();
                for (k, p) in points.iter().enumerate() {
                    if k != j {
                        prod *= *w_j - p;
                    }
                }

                // Summation step
                let q_add = proofs[j].mul(prod.inverse().unwrap()); // [1/prod]Q_{j}
                q_add
            })
            .reduce(P::G1::zero, |acc, q_add| acc + q_add); // Reduce results into a final sum

        (evaluations, res.into_affine())
    }

    pub fn partial_open_g1(
        g1_affine_srs: &[P::G1Affine],
        polynomials: &[DensePolynomial<P::ScalarField>],
        deg_x: usize,
        point: &P::ScalarField,
    ) -> Result<(P::G1Affine, P::G1Affine, DensePolynomial<P::ScalarField>), Error> {
        if polynomials.is_empty() {
            let proof = Self::bi_poly_commit_g1(g1_affine_srs, &polynomials, deg_x)?;
            return Ok((
                P::G1Affine::zero(),
                proof,
                DensePolynomial::from_coefficients_slice(&[P::ScalarField::zero()]),
            ));
        }

        let num_polys = polynomials.len();

        let powers_of_point: Vec<P::ScalarField> =
            powers_of_scalars::<P::ScalarField>(*point, num_polys);

        let poly_partial_eval: DensePolynomial<P::ScalarField> = polynomials
            .par_iter()
            .zip(powers_of_point.par_iter())
            .map(|(coeff, alpha)| coeff * &DensePolynomial::from_coefficients_slice(&[*alpha]))
            .reduce(
                || DensePolynomial::from_coefficients_slice(&[P::ScalarField::zero()]),
                |a, b| a + b,
            );

        let eval = P::G1::msm_unchecked(g1_affine_srs, &poly_partial_eval.coeffs).into_affine();

        let mut witness_bi_poly = Vec::new();
        let poly_reverse: Vec<_> = polynomials.iter().rev().collect();
        witness_bi_poly.push(poly_reverse[0].clone());

        let alpha = DensePolynomial::from_coefficients_vec(vec![*point]);
        for i in 1..(poly_reverse.len() - 1) {
            witness_bi_poly.push(poly_reverse[i] + &(&alpha * &witness_bi_poly[i - 1]));
        }

        witness_bi_poly.reverse();

        let proof = Self::bi_poly_commit_g1(g1_affine_srs, &witness_bi_poly, deg_x)?;

        Ok((eval, proof, poly_partial_eval))
    }

    pub fn verify_defer_pairing_g1(
        // Verify that @c_com is a commitment to C(X) such that C(x)=z
        g1_affine_srs: &[P::G1Affine],  // generator of G1
        g2_affine_srs: &[P::G2Affine],  // [1]_2, [x]_2, [x^2]_2, ...
        g1_affine_com: &P::G1Affine,    // commitment
        deg_max: Option<&usize>,        // max degree
        points: &[P::ScalarField],      // x such that eval = C(x)
        evaluations: &[P::ScalarField], // evaluation
        pi: &P::G1Affine,               // proof
    ) -> Vec<(P::G1, P::G2)> {
        // Interpolation set
        // tau_i(X) = lagrange_tau[i] = polynomial equal to 0 at point[j] for j!= i and
        // 1  at points[i]

        let mut lagrange_tau = DensePolynomial::from_coefficients_slice(&[P::ScalarField::zero()]);
        let mut prod = DensePolynomial::from_coefficients_slice(&[P::ScalarField::one()]);
        let mut components = vec![];
        for &p in points.iter() {
            let poly = DensePolynomial::from_coefficients_slice(&[-p, P::ScalarField::one()]);
            prod = &prod * (&poly);
            components.push(poly);
        }

        for i in 0..points.len() {
            let mut temp = &prod / &components[i];
            let lagrange_scalar = temp.evaluate(&points[i]).inverse().unwrap() * evaluations[i];
            temp.coeffs.iter_mut().for_each(|x| *x *= lagrange_scalar);
            lagrange_tau = lagrange_tau + temp;
        }

        // commit to sum evals[i] tau_i(X)
        assert!(
            g1_affine_srs.len() >= lagrange_tau.len(),
            "KZG verifier doesn't have enough g1 powers"
        );
        let g1_tau =
            P::G1::msm_unchecked(&g1_affine_srs[..lagrange_tau.len()], &lagrange_tau.coeffs);

        // vanishing polynomial
        let z_tau = prod;

        // commit to z_tau(X) in g2
        assert!(
            g2_affine_srs.len() >= z_tau.len(),
            "KZG verifier doesn't have enough g2 powers"
        );
        let g2_z_tau = P::G2::msm_unchecked(&g2_affine_srs[..z_tau.len()], &z_tau.coeffs);

        let global_max_deg = g1_affine_srs.len();

        let mut d: usize = 0;
        if deg_max == None {
            d += global_max_deg;
        } else {
            d += deg_max.unwrap();
        }

        let res = vec![
            (
                g1_tau - g1_affine_com,
                g2_affine_srs[global_max_deg - d].into_group(),
            ),
            (pi.into_group(), g2_z_tau),
        ];

        res
    }

    pub fn partial_verify_defer_pairing_g1(
        g2_affine_srs: &[P::G2Affine],
        g1_affine_com: &P::G1Affine, // commitment
        deg_x: usize,
        point: &P::ScalarField,
        partial_eval: &P::G1Affine,
        pi: &P::G1Affine, // proof
    ) -> Vec<(P::G1, P::G2)> {
        let res = vec![
            (
                partial_eval.into_group() - g1_affine_com,
                g2_affine_srs[0].into_group(),
            ),
            (
                pi.into_group(),
                g2_affine_srs[deg_x].into_group() - g2_affine_srs[0].mul(*point),
            ),
        ];
        res
    }
}
