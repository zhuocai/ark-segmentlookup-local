use crate::error::Error;
use crate::public_parameters::PublicParameters;
use crate::table::TablePreprocessedParameters;
use ark_ec::pairing::Pairing;
use ark_ff::PrimeField;
use ark_serialize::{CanonicalSerialize, Compress};
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

    pub(crate) fn append_public_parameters<P: Pairing>(
        &mut self,
        pp: &PublicParameters<P>,
        tpp: &TablePreprocessedParameters<P>,
        statement: P::G1Affine,
    ) -> Result<(), Error> {
        // fn serialize_usize<W: Write>(value: usize, writer: &mut W) -> Result<(),
        // Error> {     let value_u64 = value as u64;
        //     value_u64
        //         .serialize_with_mode(writer, Compress::Yes)
        //         .map_err(|_| Error::FailedToSerializeElement)
        // }

        // fn serialize_and_hash<T: CanonicalSerialize>(
        //     group: &Vec<T>,
        //     compress: Compress,
        // ) -> Result<Vec<u8>, Error> {
        //     let mut buffer = Vec::new();
        //     group
        //         .serialize_with_mode(&mut buffer, compress)
        //         .map_err(|_| Error::FailedToSerializeElement)?;
        //     let mut hasher = Blake2b512::new();
        //     hasher.update(&buffer);
        //     let hash = hasher.finalize();
        //     Ok(hash.to_vec()) // 64 bytes for Blake2b512
        // }

        const COMPRESS_MOD: Compress = Compress::No;

        let mut buf = vec![];

        // PP: Serialize fixed-size usize fields.
        // serialize_usize(pp.num_table_segments, &mut buf)?;
        // serialize_usize(pp.num_witness_segments, &mut buf)?;
        // serialize_usize(pp.segment_size, &mut buf)?;
        // serialize_usize(pp.table_element_size, &mut buf)?;
        // serialize_usize(pp.witness_element_size, &mut buf)?;
        // serialize_usize(pp.log_num_table_segments, &mut buf)?;

        // PP: Serialize Evaluation Domains.
        // pp.domain_w
        //     .serialize_with_mode(&mut buf, COMPRESS_MOD)
        //     .map_err(|_| Error::FailedToSerializeElement)?;
        // pp.domain_v
        //     .serialize_with_mode(&mut buf, COMPRESS_MOD)
        //     .map_err(|_| Error::FailedToSerializeElement)?;
        // pp.domain_k
        //     .serialize_with_mode(&mut buf, COMPRESS_MOD)
        //     .map_err(|_| Error::FailedToSerializeElement)?;
        // pp.domain_log_n
        //     .serialize_with_mode(&mut buf, COMPRESS_MOD)
        //     .map_err(|_| Error::FailedToSerializeElement)?;

        // PP: Serialize points.
        pp.g2_affine_zw
            .serialize_with_mode(&mut buf, COMPRESS_MOD)
            .map_err(|_| Error::FailedToSerializeElement)?;
        pp.g2_affine_zv
            .serialize_with_mode(&mut buf, COMPRESS_MOD)
            .map_err(|_| Error::FailedToSerializeElement)?;
        pp.g2_affine_zk
            .serialize_with_mode(&mut buf, COMPRESS_MOD)
            .map_err(|_| Error::FailedToSerializeElement)?;

        // PP: Serialize Identity Polynomial.
        // let mut serialized_id_poly_k = vec![];
        // pp.identity_poly_k
        //     .serialize_with_mode(&mut serialized_id_poly_k, COMPRESS_MOD)
        //     .map_err(|_| Error::FailedToSerializeElement)?;
        // let mut hasher = Blake2b512::new();
        // hasher.update(&serialized_id_poly_k);
        // let hash = hasher.finalize();
        // buf.write_all(&hash)
        //     .map_err(|_| Error::FailedToSerializeElement)?;

        // TPP: Serialize points.
        tpp.g1_affine_d
            .serialize_with_mode(&mut buf, COMPRESS_MOD)
            .map_err(|_| Error::FailedToSerializeElement)?;
        tpp.g2_affine_t
            .serialize_with_mode(&mut buf, COMPRESS_MOD)
            .map_err(|_| Error::FailedToSerializeElement)?;
        tpp.g2_affine_adjusted_t
            .serialize_with_mode(&mut buf, COMPRESS_MOD)
            .map_err(|_| Error::FailedToSerializeElement)?;

        // Statement: Serialize the point.
        statement
            .serialize_with_mode(&mut buf, COMPRESS_MOD)
            .map_err(|_| Error::FailedToSerializeElement)?;

        // Lists will be serialized in parallel.
        // let g1_affine_lists = vec![
        //     &pp.g1_affine_srs,
        //     &pp.g1_affine_list_q2,
        //     &pp.g1_affine_list_q3,
        //     &pp.g1_affine_list_lw,
        //     &pp.g1_affine_lw_opening_proofs_at_zero,
        //     &pp.g1_affine_list_lv,
        //     &pp.g1_affine_srs_caulk,
        //     &tpp.g1_affine_list_q1,
        // ];

        // let g2_affine_lists = vec![&pp.g2_affine_srs, &pp.g2_affine_srs_caulk];

        // let g1_affine_list_hashes: Result<Vec<Vec<u8>>, Error> = g1_affine_lists
        //     .par_iter()
        //     .map(|group| serialize_and_hash(*group, COMPRESS_MOD))
        //     .collect();

        // let g1_affine_list_hashes = g1_affine_list_hashes?;

        // let g2_affine_list_hashes: Result<Vec<Vec<u8>>, Error> = g2_affine_lists
        //     .par_iter()
        //     .map(|group| serialize_and_hash(*group, COMPRESS_MOD))
        //     .collect();

        // let g2_affine_list_hashes = g2_affine_list_hashes?;

        // for hash in g1_affine_list_hashes
        //     .into_iter()
        //     .chain(g2_affine_list_hashes)
        // {
        //     buf.write_all(&hash)
        //         .map_err(|_| Error::FailedToSerializeElement)?;
        // }

        self.transcript
            .append_message(Label::PublicParameters.as_bytes(), buf.as_ref());

        Ok(())
    }
}
