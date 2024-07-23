#[derive(Debug)]
pub enum Error {
    FailedToCreateEvaluationDomain,
    FailedToInverseFieldElement,

    InvalidCommitmentLength(String),
    InvalidLagrangeBasisCommitments(String),
    InvalidStructuredReferenceStrings,
    InvalidNumerOfSegments(usize),
    InvalidNumberOfQueries(usize),
    InvalidSegmentIndex(usize),
    InvalidSegmentElementIndex(usize),
    InvalidSegmentSize(usize),
    InvalidEvaluationDomainSize(usize),

    SizeNotPowerOfTwo(usize),
}