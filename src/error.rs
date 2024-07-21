#[derive(Debug)]
pub enum Error {
    FailedToCreateGeneralEvaluationDomain,
    FailedToInverseFieldElement,
    InvalidCommitmentLength(String),
    InvalidLagrangeBasisCommitments(String),
    InvalidStructuredReferenceStrings,
    SizeNotPowerOfTwo(usize),
}