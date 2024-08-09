use std::{iter, marker::PhantomData};
use std::cmp::max;

use ark_ec::{AffineCurve, msm::VariableBaseMSM, PairingEngine, ProjectiveCurve};
use ark_ff::{Field, One, PrimeField};
use ark_poly::{Polynomial, univariate::DensePolynomial, UVPolynomial};
use ark_std::{end_timer, start_timer, UniformRand, Zero};
use ark_std::rand::RngCore;

/// Minimal KZG functionalities needed for the lookup argument.
/// Modified from https://github.com/geometryxyz/cq/blob/main/src/kzg.rs
/// and https://github.com/caulk-crypto/caulk/blob/main/src/kzg.rs
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
        let coefficient_scalars: Vec<_> = poly.coeffs.iter().map(|c| c.into_repr()).collect();
        VariableBaseMSM::multi_scalar_mul(srs, &coefficient_scalars)
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

pub struct CaulkKzg<E: PairingEngine> {
    _e: PhantomData<E>,
}

impl<E: PairingEngine> CaulkKzg<E> {
    pub fn open_g1(
        srs: &[E::G1Affine],
        poly: &DensePolynomial<E::Fr>,
        max_deg: Option<&usize>,
        challenge: &E::Fr,
    ) -> (E::Fr, E::G1Affine) {
        let eval = poly.evaluate(challenge);

        let global_max_deg = srs.len();

        let mut d: usize = 0;
        if max_deg == None {
            d += global_max_deg;
        } else {
            d += max_deg.unwrap();
        }
        let divisor = DensePolynomial::from_coefficients_vec(vec![-*challenge, E::Fr::one()]);
        let witness_polynomial = poly / &divisor;

        assert!(srs[(global_max_deg - d)..].len() >= witness_polynomial.len());
        let proof = VariableBaseMSM::multi_scalar_mul(
            &srs[(global_max_deg - d)..],
            convert_to_big_ints(&witness_polynomial.coeffs).as_slice(),
        )
            .into_affine();

        (eval, proof)
    }

    pub fn bi_poly_commit_g1(
        srs_g1: &[E::G1Affine],
        polynomials: &[DensePolynomial<E::Fr>],
        deg_x: usize,
    ) -> E::G1Affine {
        let mut poly_formatted = Vec::new();

        for poly in polynomials {
            let temp = convert_to_big_ints(&poly.coeffs);
            poly_formatted.extend_from_slice(&temp);
            for _ in poly.len()..deg_x {
                poly_formatted.push(E::Fr::zero().into_repr());
            }
        }

        println!("srs_g1 size: {}", srs_g1.len());
        println!("poly formatted: {}", poly_formatted.len());
        
        assert!(srs_g1.len() >= poly_formatted.len());
        let g1_poly = VariableBaseMSM::multi_scalar_mul(srs_g1, poly_formatted.as_slice())
            .into_affine();

        g1_poly
    }

    pub fn batch_open_g1(
        srs_g1: &[E::G1Affine],
        poly: &DensePolynomial<E::Fr>,
        max_deg: Option<&usize>,
        points: &[E::Fr],
    ) -> (Vec<E::Fr>, E::G1Affine) {
        let timer = start_timer!(|| "kzg batch open g1");
        let mut evals = Vec::new();
        let mut proofs = Vec::new();
        for p in points.iter() {
            let (eval, pi) = Self::open_g1(srs_g1, poly, max_deg, p);
            evals.push(eval);
            proofs.push(pi);
        }

        let mut res = E::G1Projective::zero(); // default value

        for j in 0..points.len() {
            let w_j = points[j];
            // 1. Computing coefficient [1/prod]
            let mut prod = E::Fr::one();
            for (k, p) in points.iter().enumerate() {
                if k != j {
                    prod *= w_j - p;
                }
            }
            // 2. Summation
            let q_add = proofs[j].mul(prod.inverse().unwrap()); //[1/prod]Q_{j}
            res += q_add;
        }

        end_timer!(timer);
        (evals, res.into_affine())
    }

    pub fn partial_open_g1(
        srs_g1: &[E::G1Affine],
        polys: &[DensePolynomial<E::Fr>],
        deg_x: usize,
        point: &E::Fr,
    ) -> (E::G1Affine, E::G1Affine, DensePolynomial<E::Fr>) {
        let timer = start_timer!(|| "kzg partial open g1");
        let mut poly_partial_eval = DensePolynomial::from_coefficients_vec(vec![E::Fr::zero()]);
        let mut alpha = E::Fr::one();
        for coeff in polys {
            let pow_alpha = DensePolynomial::from_coefficients_vec(vec![alpha]);
            poly_partial_eval += &(&pow_alpha * coeff);
            alpha *= point;
        }

        let eval = VariableBaseMSM::multi_scalar_mul(
            srs_g1,
            convert_to_big_ints(&poly_partial_eval.coeffs).as_slice(),
        )
            .into_affine();

        let mut witness_bipolynomial = Vec::new();
        let poly_reverse: Vec<_> = polys.iter().rev().collect();
        witness_bipolynomial.push(poly_reverse[0].clone());

        let alpha = DensePolynomial::from_coefficients_vec(vec![*point]);
        for i in 1..(poly_reverse.len() - 1) {
            witness_bipolynomial.push(poly_reverse[i] + &(&alpha * &witness_bipolynomial[i - 1]));
        }

        witness_bipolynomial.reverse();

        let proof = Self::bi_poly_commit_g1(srs_g1, &witness_bipolynomial, deg_x);

        end_timer!(timer);
        (eval, proof, poly_partial_eval)
    }

    pub fn verify_defer_pairing_g1(
        // Verify that @c_com is a commitment to C(X) such that C(x)=z
        powers_of_g1: &[E::G1Affine], // generator of G1
        powers_of_g2: &[E::G2Affine], // [1]_2, [x]_2, [x^2]_2, ...
        c_com: &E::G1Affine,          // commitment
        max_deg: Option<&usize>,      // max degree
        points: &[E::Fr],             // x such that eval = C(x)
        evals: &[E::Fr],              // evaluation
        pi: &E::G1Affine,             // proof
    ) -> Vec<(E::G1Projective, E::G2Projective)> {
        let timer = start_timer!(|| "kzg verify g1 (deferring pairing)");

        // Interpolation set
        // tau_i(X) = lagrange_tau[i] = polynomial equal to 0 at point[j] for j!= i and
        // 1  at points[i]

        let mut lagrange_tau = DensePolynomial::from_coefficients_slice(&[E::Fr::zero()]);
        let mut prod = DensePolynomial::from_coefficients_slice(&[E::Fr::one()]);
        let mut components = vec![];
        for &p in points.iter() {
            let poly = DensePolynomial::from_coefficients_slice(&[-p, E::Fr::one()]);
            prod = &prod * (&poly);
            components.push(poly);
        }

        for i in 0..points.len() {
            let mut temp = &prod / &components[i];
            let lagrange_scalar = temp.evaluate(&points[i]).inverse().unwrap() * evals[i];
            temp.coeffs.iter_mut().for_each(|x| *x *= lagrange_scalar);
            lagrange_tau = lagrange_tau + temp;
        }

        // commit to sum evals[i] tau_i(X)
        assert!(
            powers_of_g1.len() >= lagrange_tau.len(),
            "KZG verifier doesn't have enough g1 powers"
        );
        let g1_tau = VariableBaseMSM::multi_scalar_mul(
            &powers_of_g1[..lagrange_tau.len()],
            convert_to_big_ints(&lagrange_tau.coeffs).as_slice(),
        );

        // vanishing polynomial
        let z_tau = prod;

        // commit to z_tau(X) in g2
        assert!(
            powers_of_g2.len() >= z_tau.len(),
            "KZG verifier doesn't have enough g2 powers"
        );
        let g2_z_tau = VariableBaseMSM::multi_scalar_mul(
            &powers_of_g2[..z_tau.len()],
            convert_to_big_ints(&z_tau.coeffs).as_slice(),
        );

        let global_max_deg = powers_of_g1.len();

        let mut d: usize = 0;
        if max_deg == None {
            d += global_max_deg;
        } else {
            d += max_deg.unwrap();
        }

        let res = vec![
            (
                g1_tau - c_com.into_projective(),
                powers_of_g2[global_max_deg - d].into_projective(),
            ),
            (pi.into_projective(), g2_z_tau),
        ];

        end_timer!(timer);
        res
    }

    pub fn partial_verify_defer_pairing_g1(
        srs_g2: &[E::G2Affine],
        c_com: &E::G1Affine, // commitment
        deg_x: usize,
        point: &E::Fr,
        partial_eval: &E::G1Affine,
        pi: &E::G1Affine, // proof
    ) -> Vec<(E::G1Projective, E::G2Projective)> {
        let timer = start_timer!(|| "kzg partial verify g1 (deferring pairing)");
        let res = vec![
            (
                partial_eval.into_projective() - c_com.into_projective(),
                srs_g2[0].into_projective(),
            ),
            (
                pi.into_projective(),
                srs_g2[deg_x].into_projective() -  srs_g2[0].mul(*point),
            ),
        ];
        end_timer!(timer);
        res
    }
}

pub(crate) fn convert_to_big_ints<F: PrimeField>(p: &[F]) -> Vec<F::BigInt> {
    ark_std::cfg_iter!(p)
        .map(|s| s.into_repr())
        .collect::<Vec<_>>()
}