use std::iter;
use std::ops::{Mul, MulAssign};

use crate::domain::divide_by_vanishing_poly_checked;
use crate::error::Error;
use crate::kzg::CaulkKzg;
use crate::public_parameters::PublicParameters;
use crate::transcript::{Label, Transcript};
use ark_ec::pairing::Pairing;
use ark_ec::{CurveGroup, VariableBaseMSM};
use ark_ff::Field;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{
    DenseUVPolynomial, EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain,
};
use ark_std::rand::Rng;
use ark_std::{One, UniformRand, Zero};
use rayon::prelude::*;

/// Modified from https://github.com/caulk-crypto/caulk/blob/main/src/multi/unity.rs
#[derive(Copy, Clone)]
pub(crate) struct MultiUnityProof<P: Pairing> {
    pub(crate) g1_u_bar: P::G1Affine,
    pub(crate) g1_h_1: P::G1Affine,
    pub(crate) g1_h_2: P::G1Affine,
    g1_u_bar_alpha: P::G1Affine,
    g1_h_2_alpha: P::G1Affine,
    fr_v1: P::ScalarField,
    fr_v2: P::ScalarField,
    fr_v3: P::ScalarField,
    g1_pi1: P::G1Affine,
    g1_pi2: P::G1Affine,
    g1_pi3: P::G1Affine,
    g1_pi4: P::G1Affine,
    g1_pi5: P::G1Affine,
}
pub(crate) fn multi_unity_prove<P: Pairing, R: Rng + ?Sized>(
    pp: &PublicParameters<P>,
    transcript: &mut Transcript<P::ScalarField>,
    poly_eval_list_d: &[P::ScalarField],
    poly_d: &DensePolynomial<P::ScalarField>,
    g1_d: &P::G1Affine,
    rng: &mut R,
) -> Result<MultiUnityProof<P>, Error> {
    // Round 1: The prover takes the input srs and U_0(X) amd samples log(n)
    // randomnesses to compute U_l(X) for l = 1, ..., log(n), U(X, Y), U_bar(X,
    // Y), and Q_2(X, Y). And send [U_bar(\tau^{log(n)}, \tau)]_1,
    // [Q_2(\tau^{log(n)}, \tau)]_1 to the verifier.
    if !pp.num_table_segments.is_power_of_two() {
        return Err(Error::InvalidNumberOfSegments(pp.num_table_segments));
    }

    // Get the coefficients of the polynomial D(X):
    // {D{1}, D{v^s}, ..., D{v^{k-1}}}
    let mut poly_eval_list_d = poly_eval_list_d.to_vec();

    let log_num_table_segments = pp.log_num_table_segments;
    let mut poly_u_list: Vec<DensePolynomial<P::ScalarField>> =
        Vec::with_capacity(log_num_table_segments - 1);

    // Compute U_l(X) for l = 1, ..., log(n)-1
    // u_poly_list contains U_1(X), U_2(X), ..., U_{log(n)-1}(X)
    // Time complexity: (k * log(k) * log(n))
    let vanishing_poly_k: DensePolynomial<P::ScalarField> =
        pp.domain_k.vanishing_polynomial().into();
    for _ in 1..log_num_table_segments {
        // Parallel in-place squaring of the evaluations of D(X)
        poly_eval_list_d.iter_mut().for_each(|eval| {
            *eval = eval.square();
        });

        let poly_u = Evaluations::from_vec_and_domain(poly_eval_list_d.clone(), pp.domain_k)
            .interpolate()
            + blinded_vanishing_poly::<P, _>(&vanishing_poly_k, rng);

        poly_u_list.push(poly_u);
    }

    // Compute U(X, Y) = \sum^{log(n)-1}_{l=0} U_l(X) * \rho_{l+1}(Y)
    // Store each term U_l(X) * \rho_l(Y) in a vector
    // Time complexity: (k * log(n) * log(log(n)))
    let partial_y_poly_list_u_bar: Vec<DensePolynomial<P::ScalarField>> = {
        let num_coefficients = poly_u_list[0].len();

        (0..num_coefficients)
            .into_par_iter()
            .map(|coeff_index| {
                let coeff_list: Vec<P::ScalarField> = iter::once(P::ScalarField::zero())
                    .chain(poly_u_list.iter().map(|poly_u| poly_u[coeff_index]))
                    .collect();

                // Time complexity: (log(n) * log(log(n)))
                Evaluations::from_vec_and_domain(coeff_list, pp.domain_log_n).interpolate()
            })
            .collect()
    };

    // Add D(X) to the front and identity polynomial to the back.
    let identity_poly = pp.identity_poly_k.clone();
    poly_u_list = iter::once(poly_d.clone())
        .chain(poly_u_list.into_iter())
        .chain(iter::once(identity_poly.clone()))
        .collect();

    // Time complexity: (log(n) * k * log(k))
    let poly_h_s_list: Vec<DensePolynomial<P::ScalarField>> = (1..=log_num_table_segments)
        .into_par_iter() // Parallel iterator over `s`
        .map(|s| {
            divide_by_vanishing_poly_checked::<P>(
                &pp.domain_k,
                &(&(&poly_u_list[s - 1] * &poly_u_list[s - 1]) - &poly_u_list[s]),
            )
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Time complexity: (k * log(n) * log(log(n)))
    let partial_y_poly_list_h_2: Vec<DensePolynomial<P::ScalarField>> = {
        let num_coefficients_first_poly = poly_h_s_list[0].len();
        let num_coefficients = poly_h_s_list[1].len();

        (0..num_coefficients)
            .into_par_iter()
            .map(|coeff_index| {
                let coeff0 = if coeff_index < num_coefficients_first_poly {
                    poly_h_s_list[0][coeff_index]
                } else {
                    P::ScalarField::zero()
                };

                let coeff_list: Vec<P::ScalarField> = iter::once(coeff0)
                    .chain(
                        poly_h_s_list
                            .iter()
                            .skip(1)
                            .map(|poly_h_s| poly_h_s[coeff_index]),
                    )
                    .collect();

                // Time complexity: (log(n) * log(log(n)))
                Evaluations::from_vec_and_domain(coeff_list, pp.domain_log_n).interpolate()
            })
            .collect()
    };

    let g1_u_bar = CaulkKzg::<P>::bi_poly_commit_g1(
        &pp.g1_affine_srs_caulk,
        &partial_y_poly_list_u_bar,
        log_num_table_segments,
    )?;

    let g1_h_2 = CaulkKzg::<P>::bi_poly_commit_g1(
        &pp.g1_affine_srs_caulk,
        &partial_y_poly_list_h_2,
        log_num_table_segments,
    )?;

    transcript.append_elements(&[
        (Label::CaulkG1D, *g1_d),
        (Label::CaulkG1UBar, g1_u_bar),
        (Label::CaulkG1H2, g1_h_2),
    ])?;

    let alpha = transcript.squeeze_challenge(Label::ChallengeCaulkAlpha)?;

    // Compute H_1(Y)
    let bi_poly_u_at_alpha_list = poly_u_list
        .par_iter()
        .take(log_num_table_segments) // skip the identity polynomial
        .map(|poly_u| poly_u.evaluate(&alpha))
        .collect::<Vec<_>>();

    // Time complexity: (log(n) * log(log(n)))
    let poly_u_alpha =
        Evaluations::from_vec_and_domain(bi_poly_u_at_alpha_list.clone(), pp.domain_log_n)
            .interpolate();

    let bi_poly_u_sqr_at_alpha_list = bi_poly_u_at_alpha_list
        .par_iter()
        .map(|u| u.square())
        .collect::<Vec<_>>();

    // Time complexity: (log(n) * log(log(n)))
    let poly_u_sqr_alpha =
        Evaluations::from_vec_and_domain(bi_poly_u_sqr_at_alpha_list, pp.domain_log_n)
            .interpolate();

    let domain_log_n = &pp.domain_log_n;
    let poly_h_1 = divide_by_vanishing_poly_checked::<P>(
        domain_log_n,
        &(&(&poly_u_alpha * &poly_u_alpha) - &poly_u_sqr_alpha),
    )?;

    assert!(pp.g1_affine_srs_caulk.len() >= poly_h_1.len());

    let g1_h_1 = P::G1::msm_unchecked(&pp.g1_affine_srs_caulk, &poly_h_1.coeffs).into_affine();

    transcript.append_element(Label::CaulkG1H1, &g1_h_1)?;
    let beta = transcript.squeeze_challenge(Label::ChallengeCaulkBeta)?;

    let u_alpha_beta = poly_u_alpha.evaluate(&beta);
    let mut poly_p = DensePolynomial::from_coefficients_slice(&[u_alpha_beta.square()]);

    let beta_shift = beta * domain_log_n.element(1);
    let lagrange_basis_at_beta_shift = domain_log_n.evaluate_all_lagrange_coefficients(beta_shift);

    let u_bar_alpha_shift_beta = poly_u_list
        .par_iter()
        .enumerate()
        .take(log_num_table_segments)
        .skip(1)
        .map(|(s, ploy_u)| {
            let u_s_alpha = ploy_u.evaluate(&alpha);
            u_s_alpha * lagrange_basis_at_beta_shift[s]
        })
        .reduce(|| P::ScalarField::zero(), |acc, x| acc + x);

    let lagrange_basis_at_beta = domain_log_n.evaluate_all_lagrange_coefficients(beta);
    let temp = u_bar_alpha_shift_beta
        + (identity_poly.evaluate(&alpha) * lagrange_basis_at_beta[log_num_table_segments - 1]);
    let temp = DensePolynomial::from_coefficients_slice(&[temp]);
    poly_p = &poly_p - &temp;

    let vanishing_poly_at_beta = domain_log_n.evaluate_vanishing_polynomial(beta);
    let temp = &DensePolynomial::from_coefficients_slice(&[vanishing_poly_at_beta]) * &poly_h_1;
    poly_p = &poly_p - &temp;

    let poly_eval_list_h_2_alpha = poly_h_s_list
        .par_iter()
        .map(|poly_h_s| poly_h_s.evaluate(&alpha))
        .collect::<Vec<_>>();
    let poly_h_2_alpha =
        Evaluations::from_vec_and_domain(poly_eval_list_h_2_alpha, pp.domain_log_n).interpolate();

    let temp = &DensePolynomial::from_coefficients_slice(&[vanishing_poly_k.evaluate(&alpha)])
        * &poly_h_2_alpha;
    poly_p = &poly_p - &temp;

    assert!(poly_p.evaluate(&beta) == P::ScalarField::zero());

    let (eval_list1, g1_pi1) =
        CaulkKzg::<P>::batch_open_g1(&pp.g1_affine_srs_caulk, &poly_u_list[0], None, &[alpha]);

    let (g1_u_bar_alpha, g1_pi2, poly_u_bar_alpha) = CaulkKzg::<P>::partial_open_g1(
        &pp.g1_affine_srs_caulk,
        &partial_y_poly_list_u_bar,
        domain_log_n.size(),
        &alpha,
    )?;

    let (g1_h_2_alpha, g1_pi3, _) = CaulkKzg::<P>::partial_open_g1(
        &pp.g1_affine_srs_caulk,
        &partial_y_poly_list_h_2,
        domain_log_n.size(),
        &alpha,
    )?;

    let (eval_list2, g1_pi4) = CaulkKzg::<P>::batch_open_g1(
        &pp.g1_affine_srs_caulk,
        &poly_u_bar_alpha,
        Some(&(domain_log_n.size() - 1)),
        &[P::ScalarField::one(), beta, beta * domain_log_n.element(1)],
    );
    assert!(eval_list2[0] == P::ScalarField::zero());

    let (eval_list3, g1_pi5) = CaulkKzg::<P>::batch_open_g1(
        &pp.g1_affine_srs_caulk,
        &poly_p,
        Some(&(domain_log_n.size() - 1)),
        &[beta],
    );
    assert!(eval_list3[0] == P::ScalarField::zero());

    Ok(MultiUnityProof {
        g1_u_bar,
        g1_h_1,
        g1_h_2,
        g1_u_bar_alpha,
        g1_h_2_alpha,
        fr_v1: eval_list1[0],
        fr_v2: eval_list2[1],
        fr_v3: eval_list2[2],
        g1_pi1,
        g1_pi2,
        g1_pi3,
        g1_pi4,
        g1_pi5,
    })
}

fn blinded_vanishing_poly<P: Pairing, R: Rng + ?Sized>(
    vanishing_poly: &DensePolynomial<P::ScalarField>,
    rng: &mut R,
) -> DensePolynomial<P::ScalarField> {
    let fr_rand = P::ScalarField::rand(rng);
    let vanishing_poly_coefficients: Vec<P::ScalarField> = vanishing_poly.coeffs.clone();
    let rand_poly_coefficients = vanishing_poly_coefficients
        .par_iter()
        .map(|&s| s * fr_rand)
        .collect();

    DensePolynomial::from_coefficients_vec(rand_poly_coefficients)
}

pub(crate) fn multi_unity_verify<P: Pairing, R: Rng + ?Sized>(
    pp: &PublicParameters<P>,
    alpha: P::ScalarField,
    beta: P::ScalarField,
    g1_d: &P::G1Affine,
    proof: &MultiUnityProof<P>,
    rng: &mut R,
) -> Result<(), Error> {
    let mut pairing_inputs = multi_unity_verify_defer_pairing(
        alpha,
        beta,
        &pp.g1_affine_srs_caulk,
        &pp.g2_affine_srs_caulk,
        pp.identity_poly_k.clone(),
        &pp.domain_k,
        &pp.domain_log_n,
        pp.log_num_table_segments,
        g1_d,
        proof,
    )?;

    // Scale the pairing inputs by powers of zeta
    let mut zeta = P::ScalarField::rand(rng);
    for (i, (g1, _)) in pairing_inputs.iter_mut().enumerate().skip(2) {
        g1.mul_assign(zeta);
        if i % 2 != 0 {
            zeta.square_in_place();
        }
    }

    // Extract G1 and G2 elements for the pairing
    let (pairing_inputs_g1, pairing_inputs_g2): (Vec<_>, Vec<_>) =
        pairing_inputs.into_iter().unzip();

    // Perform the multi-pairing operation and check the result
    let res = P::multi_pairing(pairing_inputs_g1, pairing_inputs_g2)
        .0
        .is_one();

    if !res {
        return Err(Error::MultiUnityPairingFailed);
    }

    Ok(())
}

fn multi_unity_verify_defer_pairing<P: Pairing>(
    alpha: P::ScalarField,
    beta: P::ScalarField,
    g1_srs: &[P::G1Affine],
    g2_srs: &[P::G2Affine],
    identity_poly_k: DensePolynomial<P::ScalarField>,
    domain_k: &Radix2EvaluationDomain<P::ScalarField>,
    domain_log_n: &Radix2EvaluationDomain<P::ScalarField>,
    log_num_segments: usize,
    g1_d: &P::G1Affine,
    proof: &MultiUnityProof<P>,
) -> Result<Vec<(P::G1, P::G2)>, Error> {
    let lagrange_basis_at_beta = domain_log_n.evaluate_all_lagrange_coefficients(beta);
    let u_alpha_beta = proof.fr_v1 * lagrange_basis_at_beta[0] + proof.fr_v2;

    // g1_P = [ U^2 - (v3 + id(alpha)* pn(beta) )]_1
    let mut g1_p = g1_srs[0].mul(
        u_alpha_beta * u_alpha_beta
            - (proof.fr_v3
                + (identity_poly_k.evaluate(&alpha)
                    * lagrange_basis_at_beta[log_num_segments - 1])),
    );

    // g1_P = g1_P  - h1 zVn(beta)
    let vanishing_poly_log_n = domain_log_n.vanishing_polynomial();
    g1_p -= proof.g1_h_1.mul(vanishing_poly_log_n.evaluate(&beta));

    // g1_P = g1_P  - h2_alpha zVm(alpha)
    let vanishing_poly_k = domain_k.vanishing_polynomial();
    g1_p -= proof.g1_h_2_alpha.mul(vanishing_poly_k.evaluate(&alpha));

    let check1 = CaulkKzg::<P>::verify_defer_pairing_g1(
        g1_srs,
        g2_srs,
        g1_d,
        None,
        &[alpha],
        &[proof.fr_v1],
        &proof.g1_pi1,
    );

    let check2 = CaulkKzg::<P>::partial_verify_defer_pairing_g1(
        g2_srs,
        &proof.g1_u_bar,
        domain_log_n.size(),
        &alpha,
        &proof.g1_u_bar_alpha,
        &proof.g1_pi2,
    );

    let check3 = CaulkKzg::<P>::partial_verify_defer_pairing_g1(
        g2_srs,
        &proof.g1_h_2,
        domain_log_n.size(),
        &alpha,
        &proof.g1_h_2_alpha,
        &proof.g1_pi3,
    );

    let check4 = CaulkKzg::<P>::verify_defer_pairing_g1(
        g1_srs,
        g2_srs,
        &proof.g1_u_bar_alpha,
        Some(&(domain_log_n.size() - 1)),
        &[P::ScalarField::one(), beta, beta * domain_log_n.element(1)],
        &[P::ScalarField::zero(), proof.fr_v2, proof.fr_v3],
        &proof.g1_pi4,
    );

    let check5 = CaulkKzg::<P>::verify_defer_pairing_g1(
        g1_srs,
        g2_srs,
        &g1_p.into_affine(),
        Some(&(domain_log_n.size() - 1)),
        &[beta],
        &[P::ScalarField::zero()],
        &proof.g1_pi5,
    );

    let res = [
        check1.as_slice(),
        check2.as_slice(),
        check3.as_slice(),
        check4.as_slice(),
        check5.as_slice(),
    ]
    .concat();

    Ok(res)
}

#[cfg(test)]
mod tests {
    use crate::domain::roots_of_unity;
    use crate::kzg::Kzg;
    use ark_bn254::Bn254;
    use ark_std::rand::RngCore;
    use ark_std::test_rng;

    use super::*;

    #[test]
    fn test_trailing_zero() {
        let num: usize = 8;
        assert_eq!(num.trailing_zeros() as usize, 3);
    }

    #[test]
    fn test_multi_unity_prove() {
        let mut rng = test_rng();
        let pp = PublicParameters::<Bn254>::builder()
            .num_table_segments(8)
            .num_witness_segments(4)
            .segment_size(4)
            .build(&mut rng)
            .expect("Failed to setup public parameters");

        let queried_segment_indices: Vec<usize> = (0..pp.num_witness_segments)
            .map(|_| rng.next_u32() as usize % pp.num_table_segments)
            .collect();

        let roots_of_unity_w: Vec<<Bn254 as Pairing>::ScalarField> =
            roots_of_unity::<Bn254>(&pp.domain_w);
        let mut poly_eval_list_d: Vec<<Bn254 as Pairing>::ScalarField> =
            Vec::with_capacity(pp.num_witness_segments);
        for &seg_index in queried_segment_indices.iter() {
            let root_of_unity_w = roots_of_unity_w[seg_index * pp.segment_size];
            poly_eval_list_d.push(root_of_unity_w);
        }

        let poly_coeff_list_d = pp.domain_k.ifft(&poly_eval_list_d);
        let poly_d = DensePolynomial::from_coefficients_vec(poly_coeff_list_d);
        let g1_d =
            Kzg::<<Bn254 as Pairing>::G1>::commit(&pp.g1_affine_srs_caulk, &poly_d).into_affine();

        let mut transcript = Transcript::new();

        multi_unity_prove(
            &pp,
            &mut transcript,
            &poly_eval_list_d,
            &poly_d,
            &g1_d,
            &mut rng,
        )
        .unwrap();
    }

    #[test]
    fn test_multi_unity_verify() {
        let mut rng = test_rng();
        let pp = PublicParameters::<Bn254>::builder()
            .num_table_segments(8)
            .num_witness_segments(4)
            .segment_size(4)
            .build(&mut rng)
            .expect("Failed to setup public parameters");
        let queried_segment_indices: Vec<usize> = (0..pp.num_witness_segments)
            .map(|_| rng.next_u32() as usize % pp.num_table_segments)
            .collect();
        let roots_of_unity_w: Vec<<Bn254 as Pairing>::ScalarField> =
            roots_of_unity::<Bn254>(&pp.domain_w);
        let mut poly_eval_list_d: Vec<<Bn254 as Pairing>::ScalarField> =
            Vec::with_capacity(pp.num_witness_segments);
        for &seg_index in queried_segment_indices.iter() {
            let root_of_unity_w = roots_of_unity_w[seg_index * pp.segment_size];
            poly_eval_list_d.push(root_of_unity_w);
        }
        let poly_coeff_list_d = pp.domain_k.ifft(&poly_eval_list_d);
        let poly_d = DensePolynomial::from_coefficients_vec(poly_coeff_list_d);
        let g1_affine_d =
            Kzg::<<Bn254 as Pairing>::G1>::commit(&pp.g1_affine_srs_caulk, &poly_d).into_affine();

        let mut transcript = Transcript::new();
        let multi_unity_proof = multi_unity_prove(
            &pp,
            &mut transcript,
            &poly_eval_list_d,
            &poly_d,
            &g1_affine_d,
            &mut rng,
        )
        .unwrap();

        let mut transcript = Transcript::new();
        transcript
            .append_elements(&[
                (Label::CaulkG1D, g1_affine_d),
                (Label::CaulkG1UBar, multi_unity_proof.g1_u_bar),
                (Label::CaulkG1H2, multi_unity_proof.g1_h_2),
            ])
            .unwrap();
        let alpha = transcript
            .squeeze_challenge(Label::ChallengeCaulkAlpha)
            .unwrap();
        transcript
            .append_element(Label::CaulkG1H1, &multi_unity_proof.g1_h_1)
            .unwrap();
        let beta = transcript
            .squeeze_challenge(Label::ChallengeCaulkBeta)
            .unwrap();
        assert!(
            multi_unity_verify(&pp, alpha, beta, &g1_affine_d, &multi_unity_proof, &mut rng)
                .is_ok()
        );

        let mut incorrect_poly_eval_list_d = poly_eval_list_d.clone();
        incorrect_poly_eval_list_d[0] = <Bn254 as Pairing>::ScalarField::from(456);
        let incorrect_poly_coeff_list_d = pp.domain_k.ifft(&incorrect_poly_eval_list_d);
        let incorrect_poly_d = DensePolynomial::from_coefficients_vec(incorrect_poly_coeff_list_d);
        let incorrect_g1_d =
            Kzg::<<Bn254 as Pairing>::G1>::commit(&pp.g1_affine_srs_caulk, &incorrect_poly_d)
                .into_affine();

        let mut transcript = Transcript::new();
        let multi_unity_proof = multi_unity_prove(
            &pp,
            &mut transcript,
            &poly_eval_list_d,
            &poly_d,
            &g1_affine_d,
            &mut rng,
        )
        .unwrap();

        let mut transcript = Transcript::new();
        transcript
            .append_elements(&[
                (Label::CaulkG1D, g1_affine_d),
                (Label::CaulkG1UBar, multi_unity_proof.g1_u_bar),
                (Label::CaulkG1H2, multi_unity_proof.g1_h_2),
            ])
            .unwrap();
        let alpha = transcript
            .squeeze_challenge(Label::ChallengeCaulkAlpha)
            .unwrap();
        transcript
            .append_element(Label::CaulkG1H1, &multi_unity_proof.g1_h_1)
            .unwrap();
        let beta = transcript
            .squeeze_challenge(Label::ChallengeCaulkBeta)
            .unwrap();
        assert!(!multi_unity_verify(
            &pp,
            alpha,
            beta,
            &incorrect_g1_d,
            &multi_unity_proof,
            &mut rng
        )
        .is_ok());

        let mut transcript = Transcript::new();
        assert!(!multi_unity_prove(
            &pp,
            &mut transcript,
            &incorrect_poly_eval_list_d,
            &incorrect_poly_d,
            &g1_affine_d,
            &mut rng,
        )
        .is_ok());
    }
}
