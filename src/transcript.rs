use ark_ff::PrimeField;
use ark_serialize::CanonicalSerialize;
use merlin::Transcript as MerlinTranscript;
use std::marker::PhantomData;

/// Modified from https://github.com/caulk-crypto/caulk/blob/main/src/transcript.rs
pub struct Transcript<F: PrimeField> {
    transcript: MerlinTranscript,
    _marker: PhantomData<F>,
}

impl<F: PrimeField> Default for Transcript<F> {
    fn default() -> Self {
        Self::new()
    }
}

impl<F: PrimeField> Transcript<F> {
    pub fn new() -> Self {
        Self {
            transcript: MerlinTranscript::new(b"Init SegLookup Transcript"),
            _marker: PhantomData::default(),
        }
    }

    /// Get a uniform random field element for field size < 384
    pub fn get_and_append_challenge(&mut self, label: &'static [u8]) -> F {
        let mut bytes = [0u8; 64];
        self.transcript.challenge_bytes(label, &mut bytes);
        let challenge = F::from_le_bytes_mod_order(bytes.as_ref());
        self.append_element(b"append challenge", &challenge);
        challenge
    }

    /// Append a field/group element to the transcript
    pub fn append_element<T: CanonicalSerialize>(&mut self, label: &'static [u8], r: &T) {
        let mut buf = vec![];
        r.serialize(&mut buf).unwrap();
        self.transcript.append_message(label, buf.as_ref());
    }
}
