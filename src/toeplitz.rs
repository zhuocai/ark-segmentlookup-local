use ark_ff::{FftField, Zero};
use ark_poly::{domain::DomainCoeff, EvaluationDomain, GeneralEvaluationDomain};
use rayon::prelude::*;
use std::fmt::Debug;
use std::marker::PhantomData;

/// Modified from: https://github.com/geometryxyz/fk/blob/main/src/toeplitz.rs

/*
    fm f(m-1) ... f1
    0   fm    ... f2
    .   ...   ... f3
    .   ... fm f(m-1)
    0   ...   ... fm
*/
/// Succinct representation of Toeplitz matrix that is instantiated from
/// polynomial on which mul by vector can be run efficiently
pub(crate) struct UpperToeplitz<F: FftField> {
    pub(crate) repr: Vec<F>,
}

impl<F: FftField> UpperToeplitz<F> {
    // pub(crate) fn from_poly(poly: &DensePolynomial<F>) -> Self {
    //     let mut repr = poly.coeffs()[1..].to_vec();
    //     let next_pow2_degree = poly.degree().next_power_of_two();
    //     repr.resize(next_pow2_degree, F::zero());
    //
    //     assert!(repr.len().is_power_of_two());
    //
    //     Self { repr }
    // }

    pub(crate) fn from_coeff_slice(coeffs: &[F]) -> Self {
        let next_pow2_degree = coeffs.len().next_power_of_two();
        let mut repr = coeffs[1..].to_vec();
        repr.resize(next_pow2_degree, F::zero());

        assert!(repr.len().is_power_of_two());

        Self { repr }
    }

    pub(crate) fn mul_by_vec<T: DomainCoeff<F> + std::ops::MulAssign<F> + Zero>(
        &self,
        x: &[T],
    ) -> Vec<T> {
        let circulant_repr = self.to_circulant_repr();
        let zeroes = vec![T::zero(); x.len()];

        Circulant::mul_by_vec(&circulant_repr, &[x, zeroes.as_slice()].concat())
    }

    fn to_circulant_repr(&self) -> Vec<F> {
        let fm = *self.repr.last().unwrap();
        let mut circulant_repr = vec![F::zero(); self.repr.len() + 1];

        circulant_repr[0] = fm;
        circulant_repr[self.repr.len()] = fm;

        circulant_repr.extend_from_slice(&self.repr[..self.repr.len() - 1]);

        circulant_repr
    }
}

struct Circulant<F: FftField, D: DomainCoeff<F> + Debug> {
    _f: PhantomData<F>,
    _d: PhantomData<D>,
}

impl<F: FftField, D: DomainCoeff<F> + Debug> Circulant<F, D> {
    fn mul_by_vec<T: DomainCoeff<F> + std::ops::MulAssign<D>>(repr: &[D], x: &[T]) -> Vec<T> {
        assert!(repr.len().is_power_of_two());

        let domain = GeneralEvaluationDomain::new(repr.len()).unwrap();
        let v = domain.fft(repr);

        let mut res = domain.fft(x);
        res.par_iter_mut()
            .zip(v.par_iter())
            .for_each(|(res_i, v_i)| *res_i *= *v_i);

        domain.ifft(&res)
    }
}
