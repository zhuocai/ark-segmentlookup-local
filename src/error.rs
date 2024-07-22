#[derive(Debug)]
pub enum Error {
    FailedToCreateGeneralEvaluationDomain,
    FailedToInverseFieldElement,
    InvalidCommitmentLength(String),
    InvalidLagrangeBasisCommitments(String),
    InvalidStructuredReferenceStrings,
    InvalidNumerOfSegments(usize),
    InvalidNumberOfQueries(usize),
    InvalidSegmentSize(usize),
    SizeNotPowerOfTwo(usize),
}