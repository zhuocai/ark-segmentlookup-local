mod public_parameters;
mod kzg;
mod lagrange_basis;
mod error;
mod table;
mod prover;
mod rng;
mod transcript;
mod witness;
mod verifier;

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
