use std::ops::MulAssign;

use ark_ec::{AffineCurve, PairingEngine, ProjectiveCurve};
use ark_ec::msm::VariableBaseMSM;
use ark_ff::Field;
use ark_poly::{EvaluationDomain, Evaluations, Polynomial, Radix2EvaluationDomain, UVPolynomial};
use ark_poly::univariate::DensePolynomial;
use ark_std::{end_timer, One, start_timer, UniformRand, Zero};
use ark_std::rand::prelude::StdRng;
use ark_std::rand::RngCore;

use crate::error::Error;
use crate::kzg::{CaulkKzg, convert_to_big_ints, Kzg};
use crate::public_parameters::PublicParameters;

/// Modified from https://github.com/caulk-crypto/caulk/blob/main/src/multi/unity.rs
pub struct MultiUnityProof<E: PairingEngine> {
    pub g1_u_bar: E::G1Affine,
    pub g1_h_1: E::G1Affine,
    pub g1_h_2: E::G1Affine,
    pub g1_u_bar_alpha: E::G1Affine,
    pub g1_h_2_alpha: E::G1Affine,
    pub v1: E::Fr,
    pub v2: E::Fr,
    pub v3: E::Fr,
    pub pi_1: E::G1Affine,
    pub pi_2: E::G1Affine,
    pub pi_3: E::G1Affine,
    pub pi_4: E::G1Affine,
    pub pi_5: E::G1Affine,
}
pub fn multi_unity_prove<
    E: PairingEngine,
    R: RngCore
>(
    pp: &PublicParameters<E>,
    d_poly: &DensePolynomial<E::Fr>,
    // queried_segment_indices: &[usize],
    mut rng: StdRng,
    alpha: E::Fr, // TODO: to be removed.
    beta: E::Fr, // TODO: to be removed.
) -> Result<MultiUnityProof<E>, Error> {
    // Round 1: The prover takes the input srs and U_0(X) amd samples log(n) randoms
    // to compute U_l(X) for l = 1, ..., log(n), U(X, Y), U_bar(X, Y), and Q_2(X, Y).
    // And send [U_bar(\tau^{log(n)}, \tau)]_1, [Q_2(\tau^{log(n)}, \tau)]_1 to the verifier.
    assert!(pp.num_segments.is_power_of_two());


    // {\mu^0, \mu^1, ..., \mu^{n-1}}
    // let roots_of_unity_n = roots_of_unity::<E>(&domain_n);
    // let queried_roots_of_unity_n: Vec<E::Fr> = queried_segment_indices
    //     .iter()
    //     .map(|&i| roots_of_unity_n[i])
    //     .collect();
    // let vanishing_poly_k = pp.domain_k.vanishing_polynomial().into();
    let d_coefficients = d_poly.coeffs.clone();
    let mut d_evaluations = pp.domain_k.fft(&d_coefficients);
    let log_num_segments = pp.log_num_segments;
    let mut u_poly_list: Vec<DensePolynomial<E::Fr>> = Vec::with_capacity(log_num_segments + 1);
    u_poly_list.push(d_poly.clone());
    let vanishing_poly_k: DensePolynomial<E::Fr> = pp.domain_k.vanishing_polynomial().into();
    let vanishing_poly_k_coefficients = vanishing_poly_k.coeffs.clone();
    for _ in 1..log_num_segments {
        for x in &mut d_evaluations {
            *x = x.square();
        }
        let rand_scalar = E::Fr::rand(&mut rng);
        let rand_poly_coefficients = vanishing_poly_k_coefficients
            .iter()
            .map(|&s| {s * rand_scalar}).collect();
        let rand_poly = DensePolynomial::from_coefficients_vec(rand_poly_coefficients);
        let u_poly = Evaluations::from_vec_and_domain(
            d_evaluations.clone(),
            pp.domain_k,
        ).interpolate() + rand_poly;
        println!("u poly degree: {:?}", u_poly.len());
        u_poly_list.push(u_poly);
    }

    // let domain_n: Radix2EvaluationDomain<E::Fr> = create_sub_domain::<E>(
    //     &pp.domain_w,
    //     pp.num_segments,
    //     pp.segment_size,
    // )?;


    let lagrange_basis_log_n = &pp.lagrange_basis_log_n;
    let mut bi_poly_u_bar = Vec::new();
    for j in 0..u_poly_list[1].len() {
        let mut temp = DensePolynomial::zero();
        for (s, u_poly) in u_poly_list
            .iter()
            .enumerate()
            .take(log_num_segments)
            .skip(1) {
            let u_s_j = DensePolynomial::from_coefficients_slice(&[u_poly[j]]);
            temp += &(&u_s_j * &lagrange_basis_log_n[s]);
        }

        bi_poly_u_bar.push(temp);
    }



    let mut h_s_poly_list: Vec<DensePolynomial<E::Fr>> = Vec::new();
    for s in 1..log_num_segments {
        let (h_s_poly, remainder) = (
            &(&u_poly_list[s - 1] * &u_poly_list[s - 1])
                - &u_poly_list[s]
        ).divide_by_vanishing_poly(pp.domain_k).ok_or(Error::FailedToDivideByVanishingPolynomial)?;

        assert!(remainder.is_zero());

        h_s_poly_list.push(h_s_poly);
    }

    let id_poly = pp.id_poly.clone();

    let (h_s_poly, remainder) = (
        &(&u_poly_list[log_num_segments - 1] * &u_poly_list[log_num_segments - 1])
            - &id_poly
    ).divide_by_vanishing_poly(pp.domain_k).ok_or(Error::FailedToDivideByVanishingPolynomial)?;

    assert!(remainder.is_zero());

    h_s_poly_list.push(h_s_poly);

    let mut bi_h_2_poly = Vec::new();

    for j in 0..h_s_poly_list[0].len() {
        let h_0_j = DensePolynomial::from_coefficients_slice(&[h_s_poly_list[0][j]]);
        bi_h_2_poly.push(&h_0_j * &lagrange_basis_log_n[0]);
    }

    for _ in h_s_poly_list[0].len()..h_s_poly_list[1].len() {
        let h_0_j = DensePolynomial::from_coefficients_slice(&[E::Fr::zero()]);
        bi_h_2_poly.push(h_0_j);
    }
    println!("{}", bi_h_2_poly.len());

    for (j, coeff) in bi_h_2_poly
        .iter_mut()
        .enumerate()
        .take(h_s_poly_list[1].len())
    {
        // h_2[j] = sum_s H_{s,j} * rho_s(Y)
        for (s, h_s_poly) in h_s_poly_list
            .iter()
            .enumerate()
            .take(log_num_segments)
            .skip(1) {
            let h_s_j = DensePolynomial::from_coefficients_slice(&[h_s_poly[j]]);

            // h_2[j] += H_{s,j} * rho_s(Y)
            *coeff += &(&h_s_j * &lagrange_basis_log_n[s]);
        }
    }

    let domain_log_n = &pp.domain_log_n;

    let u_bar_com1 = CaulkKzg::<E>::bi_poly_commit(&pp.srs_g1, &bi_poly_u_bar, domain_log_n.size());
    let h_2_com1 = CaulkKzg::<E>::bi_poly_commit(&pp.srs_g1, &bi_h_2_poly, domain_log_n.size());

    // Compute H_1(Y)
    let mut u_alpha_poly = DensePolynomial::zero();

    let mut u_sqr_alpha_list =  DensePolynomial::zero();

    for (s, u_poly) in u_poly_list
        .iter()
        .enumerate()
        .take(log_num_segments) {
        let u_s_alpha = u_poly.evaluate(&alpha);
        let mut temp = DensePolynomial::from_coefficients_slice(&[u_s_alpha]);
        u_alpha_poly += &(&temp * &lagrange_basis_log_n[s]);

        temp = DensePolynomial::from_coefficients_slice(&[u_s_alpha.square()]);
        u_sqr_alpha_list += &(&temp * &lagrange_basis_log_n[s]);
    }
    let (h_1_poly, remainder) = (&(&u_alpha_poly * &u_alpha_poly) - &u_sqr_alpha_list)
        .divide_by_vanishing_poly(domain_log_n.clone())
        .unwrap();
    assert!(remainder.is_zero(), "poly_h_1 does not divide");

    assert!(pp.srs_g1.len() >= h_1_poly.len());
    let h_1_com1 = VariableBaseMSM::multi_scalar_mul(
        &pp.srs_g1,
        convert_to_big_ints(&h_1_poly.coeffs).as_slice(),
    ).into_affine();

    let u_alpha_beta = u_alpha_poly.evaluate(&beta);
    let mut p_poly = DensePolynomial::from_coefficients_slice(&[u_alpha_beta.square()]);

    let mut u_bar_alpha_shift_beta = E::Fr::zero();
    let beta_shift = beta * domain_log_n.element(1);
    for (s, u_ploy) in u_poly_list.iter().enumerate().take(log_num_segments).skip(1) {
        let u_s_alpha = u_ploy.evaluate(&alpha);
        u_bar_alpha_shift_beta += u_s_alpha * lagrange_basis_log_n[s].evaluate(&beta_shift);
    }

    let temp = u_bar_alpha_shift_beta
        + (id_poly.evaluate(&alpha) * lagrange_basis_log_n[log_num_segments - 1].evaluate(&beta));
    let temp = DensePolynomial::from_coefficients_slice(&[temp]);

    p_poly = &p_poly - &temp;

    let vanishing_poly_log_n: DensePolynomial<E::Fr> = domain_log_n.vanishing_polynomial().into();
    let temp = &DensePolynomial::from_coefficients_slice(&[vanishing_poly_log_n.evaluate(&beta)]) * &h_1_poly;
    p_poly = &p_poly - &temp;

    let mut poly_h_2_alpha = DensePolynomial::from_coefficients_slice(&[E::Fr::zero()]);
    for (s, H_s_poly) in h_s_poly_list.iter().enumerate() {
        let h_s_j = DensePolynomial::from_coefficients_slice(&[H_s_poly.evaluate(&alpha)]);
        poly_h_2_alpha = &poly_h_2_alpha + &(&h_s_j * &lagrange_basis_log_n[s]);
    }

    let temp =
        &DensePolynomial::from_coefficients_slice(&[vanishing_poly_k.evaluate(&alpha)]) * &poly_h_2_alpha;
    p_poly = &p_poly - &temp;

    assert!(p_poly.evaluate(&beta) == E::Fr::zero());


    let (evals_1, pi_1) = CaulkKzg::<E>::open_g1_batch(&pp.srs_g1, &u_poly_list[0], None, &[alpha]);
    let (g1_u_bar_alpha, pi_2, poly_u_bar_alpha) =
        CaulkKzg::<E>::partial_open_g1(&pp.srs_g1, &bi_poly_u_bar, domain_log_n.size(), &alpha);
    let (g1_h_2_alpha, pi_3, _) =
        CaulkKzg::<E>::partial_open_g1(&pp.srs_g1, &bi_h_2_poly, domain_log_n.size(), &alpha);
    let (evals_2, pi_4) = CaulkKzg::<E>::open_g1_batch(
        &pp.srs_g1,
        &poly_u_bar_alpha,
        Some(&(domain_log_n.size() - 1)),
        &[E::Fr::one(), beta, beta * domain_log_n.element(1)],
    );
    assert!(evals_2[0] == E::Fr::zero());
    let (evals_3, pi_5) = CaulkKzg::<E>::open_g1_batch(
        &pp.srs_g1,
        &p_poly,
        Some(&(domain_log_n.size() - 1)),
        &[beta],
    );
    assert!(evals_3[0] == E::Fr::zero());

    Ok(MultiUnityProof {
        g1_u_bar: u_bar_com1,
        g1_h_1: h_1_com1,
        g1_h_2: h_2_com1,
        g1_u_bar_alpha,
        g1_h_2_alpha,
        v1: evals_1[0],
        v2: evals_2[1],
        v3: evals_2[2],
        pi_1,
        pi_2,
        pi_3,
        pi_4,
        pi_5,
    })
}

pub fn multi_unity_verify<E: PairingEngine, R: RngCore>(
    pp: &PublicParameters<E>,
    g1_u: &E::G1Affine,
    pi_unity: &MultiUnityProof<E>,
    rng: &mut R,
    alpha: E::Fr,
    beta: E::Fr,
) -> bool {
    let timer = start_timer!(|| "verify multiunity");
    let mut pairing_inputs = verify_multi_unity_defer_pairing(
        &pp.srs_g1,
        &pp.srs_g2,
        pp.id_poly.clone(),
        &pp.domain_k,
        &pp.domain_log_n,
        pp.log_num_segments,
        &pp.lagrange_basis_log_n,
        g1_u,
        pi_unity,
        alpha,
        beta,
    );
    assert_eq!(pairing_inputs.len(), 10);

    let pairing_timer = start_timer!(|| "pairing product");
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

    end_timer!(pairing_timer);
    end_timer!(timer);

    res
}

fn verify_multi_unity_defer_pairing<E: PairingEngine>(
    // pp: &PublicParameters<E>,
    // transcript: &mut CaulkTranscript<E::Fr>,
    srs_g1: &[E::G1Affine],
    srs_g2: &[E::G2Affine],
    id_poly: DensePolynomial<E::Fr>,
    domain_k: &Radix2EvaluationDomain<E::Fr>,
    domain_log_n: &Radix2EvaluationDomain<E::Fr>,
    log_num_segments: usize,
    lagrange_basis_log_n: &[DensePolynomial<E::Fr>],
    g1_u: &E::G1Affine,
    pi_unity: &MultiUnityProof<E>,
    alpha: E::Fr, // TODO: to be removed.
    beta: E::Fr, // TODO: to be removed.
) -> Vec<(E::G1Projective, E::G2Projective)> {
    let timer = start_timer!(|| "verify multi-unity (deferring pairing)");
    ////////////////////////////
    // alpha = Hash(g1_u, g1_u_bar, g1_h_2)
    ////////////////////////////
    // transcript.append_element(b"u", g1_u);
    // transcript.append_element(b"u_bar", &pi_unity.g1_u_bar);
    // transcript.append_element(b"h2", &pi_unity.g1_h_2);
    // let alpha = transcript.get_and_append_challenge(b"alpha");

    ////////////////////////////
    // beta = Hash( g1_h_1 )
    ////////////////////////////
    // transcript.append_element(b"h1", &pi_unity.g1_h_1);
    // let beta = transcript.get_and_append_challenge(b"beta");

    /////////////////////////////
    // Compute [P]_1
    ////////////////////////////

    let u_alpha_beta = pi_unity.v1 * lagrange_basis_log_n[0].evaluate(&beta) + pi_unity.v2;

    // g1_P = [ U^2 - (v3 + id(alpha)* pn(beta) )]_1
    let mut g1_P = srs_g1[0].mul(
        u_alpha_beta * u_alpha_beta
            - (pi_unity.v3
            + (id_poly.evaluate(&alpha)
            * lagrange_basis_log_n[log_num_segments - 1].evaluate(&beta))),
    );

    // g1_P = g1_P  - h1 zVn(beta)
    let vanishing_poly_log_n = domain_log_n.vanishing_polynomial();
    g1_P -= pi_unity.g1_h_1.mul(vanishing_poly_log_n.evaluate(&beta));

    // g1_P = g1_P  - h2_alpha zVm(alpha)
    let vanishing_poly_k = domain_k.vanishing_polynomial();
    g1_P -= pi_unity.g1_h_2_alpha.mul(vanishing_poly_k.evaluate(&alpha));

    /////////////////////////////
    // Check the KZG openings
    ////////////////////////////

    let check1 = CaulkKzg::<E>::verify_g1_defer_pairing(
        srs_g1,
        srs_g2,
        g1_u,
        None,
        &[alpha],
        &[pi_unity.v1],
        &pi_unity.pi_1,
    );
    let check2 = CaulkKzg::<E>::partial_verify_g1_defer_pairing(
        srs_g2,
        &pi_unity.g1_u_bar,
        domain_log_n.size(),
        &alpha,
        &pi_unity.g1_u_bar_alpha,
        &pi_unity.pi_2,
    );
    let check3 = CaulkKzg::<E>::partial_verify_g1_defer_pairing(
        srs_g2,
        &pi_unity.g1_h_2,
        domain_log_n.size(),
        &alpha,
        &pi_unity.g1_h_2_alpha,
        &pi_unity.pi_3,
    );
    let check4 = CaulkKzg::<E>::verify_g1_defer_pairing(
        srs_g1,
        srs_g2,
        &pi_unity.g1_u_bar_alpha,
        Some(&(domain_log_n.size() - 1)),
        &[E::Fr::one(), beta, beta * domain_log_n.element(1)],
        &[E::Fr::zero(), pi_unity.v2, pi_unity.v3],
        &pi_unity.pi_4,
    );
    let check5 = CaulkKzg::<E>::verify_g1_defer_pairing(
        srs_g1,
        srs_g2,
        &g1_P.into_affine(),
        Some(&(domain_log_n.size() - 1)),
        &[beta],
        &[E::Fr::zero()],
        &pi_unity.pi_5,
    );

    let res = [
        check1.as_slice(),
        check2.as_slice(),
        check3.as_slice(),
        check4.as_slice(),
        check5.as_slice(),
    ]
        .concat();
    end_timer!(timer);
    res
}

#[cfg(test)]
mod tests {
    use ark_bn254::Bn254;
    use ark_std::test_rng;
    use rand_chacha::ChaChaRng;
    use sha3::Keccak256;

    use crate::rng::SimpleHashFiatShamirRng;

    use super::*;

    #[test]
    fn test_trailing_zero() {
        let num: usize = 8;
        assert_eq!(num.trailing_zeros() as usize, 3);
    }

    type FS = SimpleHashFiatShamirRng<Keccak256, ChaChaRng>;

    #[test]
    fn test_multi_unity_prove() {
        let mut rng = test_rng();
        let pp = PublicParameters::setup(&mut rng, 8, 4, 4)
            .expect("Failed to setup public parameters");

        let queried_segment_indices: Vec<usize> = (0..pp.num_queries)
            .map(|_| rng.next_u32() as usize % pp.num_segments)
            .collect();

        let roots_of_unity_w: Vec<<Bn254 as PairingEngine>::Fr> = pp.domain_w.elements().collect();
        let mut d_poly_evaluations: Vec<<Bn254 as PairingEngine>::Fr> = Vec::with_capacity(pp.num_queries);
        for &seg_index in queried_segment_indices.iter() {
            let root_of_unity_w = roots_of_unity_w[seg_index * pp.segment_size];
            d_poly_evaluations.push(root_of_unity_w);
        }

        let d_poly_coefficients = pp.domain_k.ifft(&d_poly_evaluations);
        let d_poly = DensePolynomial::from_coefficients_vec(d_poly_coefficients);

        let alpha = <Bn254 as PairingEngine>::Fr::rand(&mut rng);
        let beta = <Bn254 as PairingEngine>::Fr::rand(&mut rng);

        multi_unity_prove::<Bn254, FS>(
            &pp,
            &d_poly,
            rng,
            alpha,
            beta,
        ).unwrap();
    }

    #[test]
    fn test_multi_unity_verify() {
        let mut rng = test_rng();
        let pp = PublicParameters::setup(&mut rng, 8, 4, 4)
            .expect("Failed to setup public parameters");

        let queried_segment_indices: Vec<usize> = (0..pp.num_queries)
            .map(|_| rng.next_u32() as usize % pp.num_segments)
            .collect();

        let roots_of_unity_w: Vec<<Bn254 as PairingEngine>::Fr> = pp.domain_w.elements().collect();
        let mut d_poly_evaluations: Vec<<Bn254 as PairingEngine>::Fr> = Vec::with_capacity(pp.num_queries);
        for &seg_index in queried_segment_indices.iter() {
            let root_of_unity_w = roots_of_unity_w[seg_index * pp.segment_size];
            d_poly_evaluations.push(root_of_unity_w);
        }

        let d_poly_coefficients = pp.domain_k.ifft(&d_poly_evaluations);
        let d_poly = DensePolynomial::from_coefficients_vec(d_poly_coefficients);
        let d_com1 = Kzg::<Bn254>::commit_g1(&pp.srs_g1, &d_poly)
            .into_affine();

        let alpha = <Bn254 as PairingEngine>::Fr::rand(&mut rng);
        let beta = <Bn254 as PairingEngine>::Fr::rand(&mut rng);

        let multi_unity_proof = multi_unity_prove::<Bn254, FS>(
            &pp,
            &d_poly,
            rng.clone(),
            alpha,
            beta,
        ).unwrap();

        assert!(multi_unity_verify(&pp, &d_com1, &multi_unity_proof, &mut rng, alpha, beta));
    }
}