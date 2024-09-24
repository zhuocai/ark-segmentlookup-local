use crate::error::Error;
use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use merlin::Transcript as MerlinTranscript;
use std::marker::PhantomData;

/// Modified from https://github.com/caulk-crypto/caulk/blob/main/src/transcript.rs

#[derive(Copy, Clone)]
pub(crate) enum Label {
    ChallengeBeta,
    ChallengeDelta,
    ChallengeGamma,
    ChallengeEta,
    ChallengeCaulkAlpha,
    ChallengeCaulkBeta,

    PublicParameters,
    TablePreprocessedParameters,

    G1M,
    G1MDivW,
    G1Qm,
    G1L,
    G1LDivV,
    G1Ql,
    G1D,
    G1Qd,
    G1A,
    G1Qa,
    G1Qb,
    G1A0,
    G1B0,
    G1Px,

    FrB0AtGamma,
    FrFAtGamma,
    FrLAtGamma,
    FrAAtZero,
    FrLAtGammaDivV,
    FrQlAtGamma,
    FrDAtGamma,
    FrQdAtGamma,

    CaulkG1D,
    CaulkG1UBar,
    CaulkG1H2,
    CaulkG1H1,
}

impl Label {
    pub fn as_bytes(&self) -> &'static [u8] {
        match self {
            Label::ChallengeBeta => b"beta",
            Label::ChallengeDelta => b"delta",
            Label::ChallengeGamma => b"gamma",
            Label::ChallengeEta => b"eta",
            Label::ChallengeCaulkAlpha => b"caulk_alpha",
            Label::ChallengeCaulkBeta => b"caulk_beta",
            Label::PublicParameters => b"common_inputs",
            Label::TablePreprocessedParameters => b"table_preprocessed_parameters",
            Label::G1M => b"g1_m",
            Label::G1MDivW => b"g1_m_div_w",
            Label::G1Qm => b"g1_qm",
            Label::G1L => b"g1_l",
            Label::G1LDivV => b"g1_l_div_v",
            Label::G1Ql => b"g1_ql",
            Label::G1D => b"g1_d",
            Label::G1Qd => b"g1_qd",
            Label::G1A => b"g1_a",
            Label::G1Qa => b"g1_qa",
            Label::G1Qb => b"g1_qb",
            Label::G1A0 => b"g1_a0",
            Label::G1B0 => b"g1_b0",
            Label::G1Px => b"g1_px",
            Label::FrB0AtGamma => b"fr_b0_at_gamma",
            Label::FrFAtGamma => b"fr_f_at_gamma",
            Label::FrLAtGamma => b"fr_l at_gamma",
            Label::FrAAtZero => b"fr_a_at_zero",
            Label::FrLAtGammaDivV => b"fr_l_at_gamma_div_v",
            Label::FrQlAtGamma => b"fr_ql_at_gamma",
            Label::FrDAtGamma => b"fr_d_at_gamma",
            Label::FrQdAtGamma => b"fr_qd_at_gamma",
            Label::CaulkG1D => b"caulk_g1_d",
            Label::CaulkG1UBar => b"caulk_g1_u_bar",
            Label::CaulkG1H2 => b"caulk_g1_h2",
            Label::CaulkG1H1 => b"caulk_g1_h1",
        }
    }
}

pub(crate) struct Transcript<F: PrimeField> {
    transcript: MerlinTranscript,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Default for Transcript<F> {
    fn default() -> Self {
        Self::new()
    }
}

impl<F: PrimeField> Transcript<F> {
    pub(crate) fn new() -> Self {
        Self {
            transcript: MerlinTranscript::new(b"Init SegLookup Transcript"),
            _marker: PhantomData::default(),
        }
    }

    /// Get a uniform random field element for field size < 384
    pub(crate) fn get_and_append_challenge(&mut self, label: Label) -> Result<F, Error> {
        let mut bytes = [0u8; 64];
        self.transcript
            .challenge_bytes(label.as_bytes(), &mut bytes);
        let challenge = F::from_le_bytes_mod_order(bytes.as_ref());
        self.append_element(label, &challenge)?;

        Ok(challenge)
    }

    /// Append a field/group element to the transcript
    pub(crate) fn append_element<T: CanonicalSerialize>(
        &mut self,
        label: Label,
        element: &T,
    ) -> Result<(), Error> {
        let mut buf = vec![];
        element
            .serialize_uncompressed(&mut buf)
            .map_err(|_| Error::FailedToSerializeElement)?;
        self.transcript
            .append_message(label.as_bytes(), buf.as_ref());

        Ok(())
    }

    pub(crate) fn append_elements<T: CanonicalSerialize>(
        &mut self,
        labels_and_elements: &[(Label, T)],
    ) -> Result<(), Error> {
        for (label, element) in labels_and_elements {
            self.append_element(*label, element)?;
        }

        Ok(())
    }
}
