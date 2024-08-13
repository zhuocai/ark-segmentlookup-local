#[derive(Debug)]
pub enum Error {
    FailedToCreateEvaluationDomain,
    FailedToInverseFieldElement,

    InvalidCommitmentLength(String),
    InvalidLagrangeBasisCommitments(String),
    InvalidQuotientPolynomialCommitments(String),
    InvalidStructuredReferenceStrings,
    InvalidNumberOfSegments(usize),
    InvalidNumberOfQueries(usize),
    InvalidSegmentIndex(usize),
    InvalidSegmentElementIndex(usize),
    InvalidSegmentSize(usize),
    InvalidEvaluationDomainSize(usize),

    SizeNotPowerOfTwo(usize),

    Pairing1Failed,
    Pairing2Failed,
    Pairing3Failed,
    Pairing4Failed,
    DegreeCheckFailed,

    // Caulk Sub-protocol
    FailedToDivideByVanishingPolynomial,
    RemainderAfterDivisionIsNonZero,
    FailedToCheckMultiUnity,
}
