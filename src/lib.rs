mod domain;
mod error;
mod kzg;
mod lagrange_basis;
pub mod multi_unity;
pub mod prover;
pub mod public_parameters;
mod rng;
pub mod table;
mod transcript;
pub mod verifier;
mod witness;

pub fn add(left: usize, right: usize) -> usize {
    left + right
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
