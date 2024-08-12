#[derive(Debug)]
pub enum Error {
    FailedToCreateEvaluationDomain,
    FailedToInverseFieldElement,
    

    InvalidCommitmentLength(String),
    InvalidLagrangeBasisCommitments(String),
    InvalidQuotientPolynomialCommitments(String),
    InvalidStructuredReferenceStrings,
    InvalidNumerOfSegments(usize),
    InvalidNumberOfQueries(usize),
    InvalidSegmentIndex(usize),
    InvalidSegmentElementIndex(usize),
    InvalidSegmentSize(usize),
    InvalidEvaluationDomainSize(usize),

    SizeNotPowerOfTwo(usize),
    
    Pairing1Failed,
    Pairing2Failed,
    
    // Caulk Sub-protocol
    FailedToDivideByVanishingPolynomial,
    RemainderAfterDivisionIsNonZero,
    FailedToCheckMultiUnity,
}