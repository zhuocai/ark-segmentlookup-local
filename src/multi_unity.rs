use std::iter;
use std::ops::MulAssign;

use crate::domain::divide_by_vanishing_poly_checked;
use crate::error::Error;
use crate::kzg::{convert_to_big_ints, CaulkKzg};
use crate::public_parameters::PublicParameters;
use crate::transcript::{Label, Transcript};
use ark_ec::msm::VariableBaseMSM;
use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ff::Field;
use ark_poly::univariate::DensePolynomial;
use ark_poly::{EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain, UVPolynomial};
use ark_std::rand::prelude::StdRng;
use ark_std::{One, UniformRand, Zero};

/// Modified from https://github.com/caulk-crypto/caulk/blob/main/src/multi/unity.rs
#[derive(Copy, Clone)]
pub(crate) struct MultiUnityProof<E: PairingEngine> {
    g1_u_bar: E::G1Affine,
    g1_h_1: E::G1Affine,
    g1_h_2: E::G1Affine,
    g1_u_bar_alpha: E::G1Affine,
    g1_h_2_alpha: E::G1Affine,
    fr_v1: E::Fr,
    fr_v2: E::Fr,
    fr_v3: E::Fr,
    g1_pi1: E::G1Affine,
    g1_pi2: E::G1Affine,
    g1_pi3: E::G1Affine,
    g1_pi4: E::G1Affine,
    g1_pi5: E::G1Affine,
}
pub(crate) fn multi_unity_prove<E: PairingEngine>(
    pp: &PublicParameters<E>,
    transcript: &mut Transcript<E::Fr>,
    poly_d: &DensePolynomial<E::Fr>,
    g1_d: &E::G1Affine,
    rng: &mut StdRng,
) -> Result<MultiUnityProof<E>, Error> {
    // Round 1: The prover takes the input srs and U_0(X) amd samples log(n) randomnesses
    // to compute U_l(X) for l = 1, ..., log(n), U(X, Y), U_bar(X, Y), and Q_2(X, Y).
    // And send [U_bar(\tau^{log(n)}, \tau)]_1, [Q_2(\tau^{log(n)}, \tau)]_1 to the verifier.
    if !pp.num_table_segments.is_power_of_two() {
        return Err(Error::InvalidNumberOfSegments(pp.num_table_segments));
    }

    // Get the coefficients of the polynomial D(X):
    // {D{1}, D{v^s}, ..., D{v^{k-1}}}
    let poly_coeff_list_d = poly_d.coeffs.clone();
    let mut poly_eval_list_d = pp.domain_k.fft(&poly_coeff_list_d);

    let log_num_table_segments = pp.log_num_table_segments;
    let mut poly_u_list: Vec<DensePolynomial<E::Fr>> =
        Vec::with_capacity(log_num_table_segments - 1);

    // Compute U_l(X) for l = 1, ..., log(n)-1
    // u_poly_list contains U_1(X), U_2(X), ..., U_{log(n)-1}(X)
    let vanishing_poly_k: DensePolynomial<E::Fr> = pp.domain_k.vanishing_polynomial().into();
    for _ in 1..log_num_table_segments {
        // In-place squaring of the evaluations of D(X)
        for eval in &mut poly_eval_list_d {
            *eval = eval.square();
        }
        let poly_u = Evaluations::from_vec_and_domain(poly_eval_list_d.clone(), pp.domain_k)
            .interpolate()
            + blinded_vanishing_poly::<E>(&vanishing_poly_k, rng);

        poly_u_list.push(poly_u);
    }

    // Compute U(X, Y) = \sum^{log(n)-1}_{l=0} U_l(X) * \rho_{l+1}(Y)
    // Store each term U_l(X) * \rho_l(Y) in a vector
    let lagrange_basis = &pp.lagrange_basis_log_n;

    let partial_y_poly_list_u_bar: Vec<DensePolynomial<E::Fr>> = {
        let num_coefficients = poly_u_list[0].len();
        let mut partial_y_poly_list_u_bar = Vec::with_capacity(num_coefficients);
        for coeff_index in 0..num_coefficients {
            let mut partial_y_poly = DensePolynomial::zero();
            for (base_index, poly_u) in poly_u_list.iter().enumerate() {
                let coeff_u = poly_u[coeff_index];
                let scaled_coeffs: Vec<E::Fr> = lagrange_basis[base_index + 1]
                    .coeffs
                    .iter()
                    .map(|&basis_coeff| basis_coeff * &coeff_u)
                    .collect();
                let scaled_poly = DensePolynomial::from_coefficients_vec(scaled_coeffs);
                partial_y_poly += &scaled_poly;
            }

            partial_y_poly_list_u_bar.push(partial_y_poly);
        }

        partial_y_poly_list_u_bar
    };

    // Add D(X) to the front and identity polynomial to the back.
    let identity_poly = pp.identity_poly_k.clone();
    poly_u_list = iter::once(poly_d.clone())
        .chain(poly_u_list.into_iter())
        .chain(iter::once(identity_poly.clone()))
        .collect();

    let mut poly_h_s_list: Vec<DensePolynomial<E::Fr>> = Vec::new();
    for s in 1..=log_num_table_segments {
        let poly_h_s = divide_by_vanishing_poly_checked::<E>(
            &pp.domain_k,
            &(&(&poly_u_list[s - 1] * &poly_u_list[s - 1]) - &poly_u_list[s]),
        )?;
        poly_h_s_list.push(poly_h_s);
    }

    // TODO: Optimize the code segment.
    let partial_y_poly_list_h_2 = {
        let num_coefficients = poly_h_s_list[1].len();
        let mut partial_y_poly_list_h_2: Vec<DensePolynomial<E::Fr>> =
            Vec::with_capacity(num_coefficients);

        // Add H_1(X) * \rho_1(Y) and pad with zero polynomials if needed.
        for j in 0..num_coefficients {
            let h_0_j = if j < poly_h_s_list[0].len() {
                DensePolynomial::from_coefficients_slice(&[poly_h_s_list[0][j]])
            } else {
                DensePolynomial::from_coefficients_slice(&[E::Fr::zero()])
            };
            partial_y_poly_list_h_2.push(&h_0_j * &lagrange_basis[0]);
        }

        // Update h_2_partial_y_polys with the sum of H_{s,j} * \rho_s(Y)
        for (j, coeff) in partial_y_poly_list_h_2
            .iter_mut()
            .enumerate()
            .take(num_coefficients)
        {
            for (s, h_s_poly) in poly_h_s_list
                .iter()
                .enumerate()
                .take(log_num_table_segments)
                .skip(1)
            {
                let h_s_j = DensePolynomial::from_coefficients_slice(&[h_s_poly[j]]);
                *coeff += &(&h_s_j * &lagrange_basis[s]);
            }
        }

        partial_y_poly_list_h_2
    };

    let g1_u_bar = CaulkKzg::<E>::bi_poly_commit_g1(
        &pp.g1_srs_caulk,
        &partial_y_poly_list_u_bar,
        log_num_table_segments,
    );

    let g1_h_2 = CaulkKzg::<E>::bi_poly_commit_g1(
        &pp.g1_srs_caulk,
        &partial_y_poly_list_h_2,
        log_num_table_segments,
    );

    transcript.append_elements(&[
        (Label::CaulkG1D, *g1_d),
        (Label::CaulkG1UBar, g1_u_bar),
        (Label::CaulkG1H2, g1_h_2),
    ])?;

    let alpha = transcript.get_and_append_challenge(Label::ChallengeCaulkAlpha)?;

    // Compute H_1(Y)
    let mut poly_u_alpha = DensePolynomial::zero();

    let mut u_sqr_alpha_list = DensePolynomial::zero();

    for (s, poly_u) in poly_u_list.iter().enumerate().take(log_num_table_segments) {
        let u_s_alpha = poly_u.evaluate(&alpha);
        let mut temp = DensePolynomial::from_coefficients_slice(&[u_s_alpha]);
        poly_u_alpha += &(&temp * &lagrange_basis[s]);

        temp = DensePolynomial::from_coefficients_slice(&[u_s_alpha.square()]);
        u_sqr_alpha_list += &(&temp * &lagrange_basis[s]);
    }
    let domain_log_n = &pp.domain_log_n;
    let poly_h_1 = divide_by_vanishing_poly_checked::<E>(
        domain_log_n,
        &(&(&poly_u_alpha * &poly_u_alpha) - &u_sqr_alpha_list),
    )?;

    assert!(pp.g1_srs_caulk.len() >= poly_h_1.len());

    let g1_h_1 = VariableBaseMSM::multi_scalar_mul(
        &pp.g1_srs_caulk,
        convert_to_big_ints(&poly_h_1.coeffs).as_slice(),
    )
    .into_affine();

    transcript.append_element(Label::CaulkG1H1, &g1_h_1)?;
    let beta = transcript.get_and_append_challenge(Label::ChallengeCaulkBeta)?;

    let u_alpha_beta = poly_u_alpha.evaluate(&beta);
    let mut poly_p = DensePolynomial::from_coefficients_slice(&[u_alpha_beta.square()]);

    let mut u_bar_alpha_shift_beta = E::Fr::zero();
    let beta_shift = beta * domain_log_n.element(1);
    for (s, ploy_u) in poly_u_list
        .iter()
        .enumerate()
        .take(log_num_table_segments)
        .skip(1)
    {
        let u_s_alpha = ploy_u.evaluate(&alpha);
        u_bar_alpha_shift_beta += u_s_alpha * lagrange_basis[s].evaluate(&beta_shift);
    }

    let temp = u_bar_alpha_shift_beta
        + (identity_poly.evaluate(&alpha)
            * lagrange_basis[log_num_table_segments - 1].evaluate(&beta));
    let temp = DensePolynomial::from_coefficients_slice(&[temp]);

    poly_p = &poly_p - &temp;

    let vanishing_poly_log_n: DensePolynomial<E::Fr> = domain_log_n.vanishing_polynomial().into();
    let temp = &DensePolynomial::from_coefficients_slice(&[vanishing_poly_log_n.evaluate(&beta)])
        * &poly_h_1;
    poly_p = &poly_p - &temp;

    let mut poly_h_2_alpha = DensePolynomial::from_coefficients_slice(&[E::Fr::zero()]);
    for (s, poly_h_s) in poly_h_s_list.iter().enumerate() {
        let h_s_j = DensePolynomial::from_coefficients_slice(&[poly_h_s.evaluate(&alpha)]);
        poly_h_2_alpha = &poly_h_2_alpha + &(&h_s_j * &lagrange_basis[s]);
    }

    let temp = &DensePolynomial::from_coefficients_slice(&[vanishing_poly_k.evaluate(&alpha)])
        * &poly_h_2_alpha;
    poly_p = &poly_p - &temp;

    assert!(poly_p.evaluate(&beta) == E::Fr::zero());

    let (eval_list1, g1_pi1) =
        CaulkKzg::<E>::batch_open_g1(&pp.g1_srs_caulk, &poly_u_list[0], None, &[alpha]);
    let (g1_u_bar_alpha, g1_pi2, poly_u_bar_alpha) = CaulkKzg::<E>::partial_open_g1(
        &pp.g1_srs_caulk,
        &partial_y_poly_list_u_bar,
        domain_log_n.size(),
        &alpha,
    );

    let (g1_h_2_alpha, g1_pi3, _) = CaulkKzg::<E>::partial_open_g1(
        &pp.g1_srs_caulk,
        &partial_y_poly_list_h_2,
        domain_log_n.size(),
        &alpha,
    );

    let (eval_list2, g1_pi4) = CaulkKzg::<E>::batch_open_g1(
        &pp.g1_srs_caulk,
        &poly_u_bar_alpha,
        Some(&(domain_log_n.size() - 1)),
        &[E::Fr::one(), beta, beta * domain_log_n.element(1)],
    );
    assert!(eval_list2[0] == E::Fr::zero());

    let (eval_list3, g1_pi5) = CaulkKzg::<E>::batch_open_g1(
        &pp.g1_srs_caulk,
        &poly_p,
        Some(&(domain_log_n.size() - 1)),
        &[beta],
    );
    assert!(eval_list3[0] == E::Fr::zero());

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

fn blinded_vanishing_poly<E: PairingEngine>(
    vanishing_poly: &DensePolynomial<E::Fr>,
    rng: &mut StdRng,
) -> DensePolynomial<E::Fr> {
    let fr_rand = E::Fr::rand(rng);
    let vanishing_poly_coefficients: Vec<E::Fr> = vanishing_poly.coeffs.clone();
    let rand_poly_coefficients = vanishing_poly_coefficients
        .iter()
        .map(|&s| s * fr_rand)
        .collect();

    DensePolynomial::from_coefficients_vec(rand_poly_coefficients)
}

pub(crate) fn multi_unity_verify<E: PairingEngine>(
    pp: &PublicParameters<E>,
    transcript: &mut Transcript<E::Fr>,
    g1_d: &E::G1Affine,
    proof: &MultiUnityProof<E>,
    rng: &mut StdRng,
) -> Result<bool, Error> {
    let mut pairing_inputs = multi_unity_verify_defer_pairing(
        transcript,
        &pp.g1_srs_caulk,
        &pp.g2_srs_caulk,
        pp.identity_poly_k.clone(),
        &pp.domain_k,
        &pp.domain_log_n,
        pp.log_num_table_segments,
        &pp.lagrange_basis_log_n,
        g1_d,
        proof,
    )?;

    // TODO: Optimize the code segment.
    assert_eq!(pairing_inputs.len(), 10);

    let mut zeta = E::Fr::rand(rng);
    pairing_inputs[2].0.mul_assign(zeta);
    pairing_inputs[3].0.mul_assign(zeta);
    zeta.square_in_place();
    pairing_inputs[4].0.mul_assign(zeta);
    pairing_inputs[5].0.mul_assign(zeta);
    zeta.square_in_place();
    pairing_inputs[6].0.mul_assign(zeta);
    pairing_inputs[7].0.mul_assign(zeta);
    zeta.square_in_place();
    pairing_inputs[8].0.mul_assign(zeta);
    pairing_inputs[9].0.mul_assign(zeta);

    let prepared_pairing_inputs: Vec<(E::G1Prepared, E::G2Prepared)> = pairing_inputs
        .iter()
        .map(|(g1, g2)| {
            (
                E::G1Prepared::from(g1.into_affine()),
                E::G2Prepared::from(g2.into_affine()),
            )
        })
        .collect();
    let res = E::product_of_pairings(prepared_pairing_inputs.iter()).is_one();

    Ok(res)
}

fn multi_unity_verify_defer_pairing<E: PairingEngine>(
    transcript: &mut Transcript<E::Fr>,
    g1_srs: &[E::G1Affine],
    g2_srs: &[E::G2Affine],
    identity_poly_k: DensePolynomial<E::Fr>,
    domain_k: &Radix2EvaluationDomain<E::Fr>,
    domain_log_n: &Radix2EvaluationDomain<E::Fr>,
    log_num_segments: usize,
    lagrange_basis_log_n: &[DensePolynomial<E::Fr>],
    g1_d: &E::G1Affine,
    proof: &MultiUnityProof<E>,
) -> Result<Vec<(E::G1Projective, E::G2Projective)>, Error> {
    transcript.append_elements(&[
        (Label::CaulkG1D, *g1_d),
        (Label::CaulkG1UBar, proof.g1_u_bar),
        (Label::CaulkG1H2, proof.g1_h_2),
    ])?;
    let alpha = transcript.get_and_append_challenge(Label::ChallengeCaulkAlpha)?;

    transcript.append_element(Label::CaulkG1H1, &proof.g1_h_1)?;
    let beta = transcript.get_and_append_challenge(Label::ChallengeCaulkBeta)?;

    let u_alpha_beta = proof.fr_v1 * lagrange_basis_log_n[0].evaluate(&beta) + proof.fr_v2;

    // g1_P = [ U^2 - (v3 + id(alpha)* pn(beta) )]_1
    let mut g1_p = g1_srs[0].mul(
        u_alpha_beta * u_alpha_beta
            - (proof.fr_v3
                + (identity_poly_k.evaluate(&alpha)
                    * lagrange_basis_log_n[log_num_segments - 1].evaluate(&beta))),
    );

    // g1_P = g1_P  - h1 zVn(beta)
    let vanishing_poly_log_n = domain_log_n.vanishing_polynomial();
    g1_p -= proof.g1_h_1.mul(vanishing_poly_log_n.evaluate(&beta));

    // g1_P = g1_P  - h2_alpha zVm(alpha)
    let vanishing_poly_k = domain_k.vanishing_polynomial();
    g1_p -= proof.g1_h_2_alpha.mul(vanishing_poly_k.evaluate(&alpha));

    let check1 = CaulkKzg::<E>::verify_defer_pairing_g1(
        g1_srs,
        g2_srs,
        g1_d,
        None,
        &[alpha],
        &[proof.fr_v1],
        &proof.g1_pi1,
    );

    let check2 = CaulkKzg::<E>::partial_verify_defer_pairing_g1(
        g2_srs,
        &proof.g1_u_bar,
        domain_log_n.size(),
        &alpha,
        &proof.g1_u_bar_alpha,
        &proof.g1_pi2,
    );

    let check3 = CaulkKzg::<E>::partial_verify_defer_pairing_g1(
        g2_srs,
        &proof.g1_h_2,
        domain_log_n.size(),
        &alpha,
        &proof.g1_h_2_alpha,
        &proof.g1_pi3,
    );

    let check4 = CaulkKzg::<E>::verify_defer_pairing_g1(
        g1_srs,
        g2_srs,
        &proof.g1_u_bar_alpha,
        Some(&(domain_log_n.size() - 1)),
        &[E::Fr::one(), beta, beta * domain_log_n.element(1)],
        &[E::Fr::zero(), proof.fr_v2, proof.fr_v3],
        &proof.g1_pi4,
    );

    let check5 = CaulkKzg::<E>::verify_defer_pairing_g1(
        g1_srs,
        g2_srs,
        &g1_p.into_affine(),
        Some(&(domain_log_n.size() - 1)),
        &[beta],
        &[E::Fr::zero()],
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
    use super::*;
    use crate::domain::roots_of_unity;
    use crate::kzg::Kzg;
    use ark_bn254::Bn254;
    use ark_std::rand::RngCore;
    use ark_std::test_rng;

    #[test]
    fn test_trailing_zero() {
        let num: usize = 8;
        assert_eq!(num.trailing_zeros() as usize, 3);
    }

    #[test]
    fn test_multi_unity_prove() {
        let mut rng = test_rng();
        let pp =
            PublicParameters::setup(&mut rng, 8, 4, 4).expect("Failed to setup public parameters");

        let queried_segment_indices: Vec<usize> = (0..pp.num_witness_segments)
            .map(|_| rng.next_u32() as usize % pp.num_table_segments)
            .collect();

        let roots_of_unity_w: Vec<<Bn254 as PairingEngine>::Fr> =
            roots_of_unity::<Bn254>(&pp.domain_w);
        let mut poly_eval_list_d: Vec<<Bn254 as PairingEngine>::Fr> =
            Vec::with_capacity(pp.num_witness_segments);
        for &seg_index in queried_segment_indices.iter() {
            let root_of_unity_w = roots_of_unity_w[seg_index * pp.segment_size];
            poly_eval_list_d.push(root_of_unity_w);
        }

        let poly_coeff_list_d = pp.domain_k.ifft(&poly_eval_list_d);
        let poly_d = DensePolynomial::from_coefficients_vec(poly_coeff_list_d);
        let g1_d = Kzg::<Bn254>::commit_g1(&pp.g1_srs_caulk, &poly_d).into_affine();

        let mut transcript = Transcript::new();

        multi_unity_prove::<Bn254>(&pp, &mut transcript, &poly_d, &g1_d, &mut rng).unwrap();
    }

    #[test]
    fn test_multi_unity_verify() {
        let mut rng = test_rng();
        let pp =
            PublicParameters::setup(&mut rng, 8, 4, 4).expect("Failed to setup public parameters");
        let queried_segment_indices: Vec<usize> = (0..pp.num_witness_segments)
            .map(|_| rng.next_u32() as usize % pp.num_table_segments)
            .collect();
        let roots_of_unity_w: Vec<<Bn254 as PairingEngine>::Fr> =
            roots_of_unity::<Bn254>(&pp.domain_w);
        let mut poly_eval_list_d: Vec<<Bn254 as PairingEngine>::Fr> =
            Vec::with_capacity(pp.num_witness_segments);
        for &seg_index in queried_segment_indices.iter() {
            let root_of_unity_w = roots_of_unity_w[seg_index * pp.segment_size];
            poly_eval_list_d.push(root_of_unity_w);
        }
        let poly_coeff_list_d = pp.domain_k.ifft(&poly_eval_list_d);
        let poly_d = DensePolynomial::from_coefficients_vec(poly_coeff_list_d);
        let g1_d = Kzg::<Bn254>::commit_g1(&pp.g1_srs_caulk, &poly_d).into_affine();

        let mut transcript = Transcript::new();
        let multi_unity_proof =
            multi_unity_prove::<Bn254>(&pp, &mut transcript, &poly_d, &g1_d, &mut rng).unwrap();

        let mut transcript = Transcript::new();
        assert!(
            multi_unity_verify(&pp, &mut transcript, &g1_d, &multi_unity_proof, &mut rng).unwrap()
        );

        let mut incorrect_poly_eval_list_d = poly_eval_list_d.clone();
        incorrect_poly_eval_list_d[0] = <Bn254 as PairingEngine>::Fr::from(456);
        let incorrect_poly_coeff_list_d = pp.domain_k.ifft(&incorrect_poly_eval_list_d);
        let incorrect_poly_d = DensePolynomial::from_coefficients_vec(incorrect_poly_coeff_list_d);
        let incorrect_g1_d =
            Kzg::<Bn254>::commit_g1(&pp.g1_srs_caulk, &incorrect_poly_d).into_affine();

        let mut transcript = Transcript::new();

        let multi_unity_proof =
            multi_unity_prove::<Bn254>(&pp, &mut transcript, &poly_d, &g1_d, &mut rng).unwrap();

        let mut transcript = Transcript::new();
        assert!(!multi_unity_verify(
            &pp,
            &mut transcript,
            &incorrect_g1_d,
            &multi_unity_proof,
            &mut rng
        )
        .unwrap());

        let mut transcript = Transcript::new();
        assert!(!multi_unity_prove::<Bn254>(
            &pp,
            &mut transcript,
            &incorrect_poly_d,
            &g1_d,
            &mut rng,
        )
        .is_ok());
    }
}
