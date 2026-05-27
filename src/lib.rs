use std::{
    error::Error,
    fmt::Display,
    iter::{once, repeat_n},
};

use subtle::{Choice, ConditionallySelectable, ConstantTimeEq};

use mgf1_sha256::mgf1_sha256;

#[derive(Debug)]
pub struct OAEPErr;

impl Display for OAEPErr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "encode error")
    }
}

impl Error for OAEPErr {}

pub const HASH_LEN: usize = 32;

pub fn encode(
    len: usize,
    seed: &[u8; HASH_LEN],
    label: &[u8],
    message: &[u8],
) -> Result<Vec<u8>, OAEPErr> {
    let msg_cap = len - HASH_LEN * 2 - 2;
    let message_len = message.len();
    if message_len > msg_cap {
        return Err(OAEPErr);
    }
    let db_len = len - HASH_LEN - 1;
    let zero_pad_len = db_len - HASH_LEN - 1 - message_len;
    let db: Vec<u8> = sha256::sha256(label)
        .into_iter()
        .chain(repeat_n(0, zero_pad_len))
        .chain(once(1))
        .chain(message.iter().copied())
        .collect();

    let db_mask = mgf1_sha256(&seed[..], db_len);
    let masked_db = mask(&db, &db_mask)?;

    let seed_mask = mgf1_sha256(&masked_db, HASH_LEN);
    let masked_seed = mask(&seed[..], &seed_mask)?;

    Ok(once(0).chain(masked_seed).chain(masked_db).collect())
}

pub fn decode(len: usize, label: &[u8], encrypted_message: &[u8]) -> Result<Vec<u8>, OAEPErr> {
    if encrypted_message.len() != len {
        return Err(OAEPErr);
    }
    let db_len = len - HASH_LEN - 1;
    let first_byte_ok = encrypted_message[0].ct_eq(&0x00);

    let masked_seed = &encrypted_message[1..1 + HASH_LEN];
    let masked_db = &encrypted_message[1 + HASH_LEN..];

    let seed_mask = mgf1_sha256(masked_db, HASH_LEN);
    let seed_vec = mask(masked_seed, &seed_mask)?;
    let seed: [u8; HASH_LEN] = seed_vec.try_into().unwrap();

    let db_mask = mgf1_sha256(&seed, db_len);
    let db = mask(masked_db, &db_mask)?;

    let l_hash: [u8; HASH_LEN] = db[..HASH_LEN].try_into().map_err(|_| OAEPErr)?;
    let label_hash = sha256::sha256(label);
    let label_ok = l_hash.ct_eq(&label_hash);

    let mut msg_start = db_len as u64;
    let mut found = Choice::from(0u8);
    for (j, b) in db.iter().enumerate().take(db_len).skip(HASH_LEN) {
        let is_one = b.ct_eq(&0x01);
        let pick = is_one & !found;
        msg_start = u64::conditional_select(&msg_start, &(j as u64), pick);
        found |= is_one;
    }

    let ok = first_byte_ok & label_ok & found;
    if ok.unwrap_u8() == 0 {
        return Err(OAEPErr);
    }
    let message = db[msg_start as usize + 1..].to_vec();
    Ok(message)
}

fn mask(a: &[u8], b: &[u8]) -> Result<Vec<u8>, OAEPErr> {
    if a.len() != b.len() {
        return Err(OAEPErr);
    }
    Ok(a.iter().zip(b.iter()).map(|(x, y)| x ^ y).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::Rng;

    fn random_seed() -> [u8; HASH_LEN] {
        let mut rng = rand::rng();
        let mut seed = [0u8; HASH_LEN];
        rng.fill_bytes(&mut seed);
        seed
    }

    #[test]
    fn roundtrip_typical_message() {
        let seed = random_seed();
        let label = b"The Label";
        let message = b"The Plaintext";
        let em = encode(512, &seed, label, message).unwrap();
        let recovered_msg = decode(512, label, &em).unwrap();
        assert_eq!(
            message.as_ref(),
            recovered_msg.as_slice(),
            "message mismatch"
        );
    }

    #[test]
    fn roundtrip_empty_message() {
        let seed = random_seed();
        let em = encode(512, &seed, b"", b"").unwrap();
        let msg = decode(512, b"", &em).unwrap();
        assert!(msg.is_empty());
    }

    #[test]
    fn roundtrip_empty_label() {
        let seed = random_seed();
        let message = b"hello world";
        let em = encode(512, &seed, b"", message).unwrap();
        let recovered = decode(512, b"", &em).unwrap();
        assert_eq!(message.as_ref(), recovered.as_slice());
    }

    #[test]
    fn roundtrip_max_length_message() {
        let seed = random_seed();
        let len = 512;
        let msg_cap = len - HASH_LEN * 2 - 2;
        let message = vec![0xABu8; msg_cap];
        let em = encode(len, &seed, b"label", &message).unwrap();
        let recovered = decode(len, b"label", &em).unwrap();
        assert_eq!(message, recovered);
    }

    #[test]
    fn encode_rejects_oversized_message() {
        let seed = random_seed();
        let len = 512;
        let msg_cap = len - HASH_LEN * 2 - 2;
        let message = vec![0u8; msg_cap + 1];
        assert!(encode(len, &seed, b"", &message).is_err());
    }

    // ── decode error cases ────────────────────────────────────────────────

    #[test]
    fn decode_rejects_wrong_label() {
        let seed = random_seed();
        let em = encode(512, &seed, b"correct-label", b"secret").unwrap();
        assert!(decode(512, b"wrong-label", &em).is_err());
    }

    #[test]
    fn decode_rejects_wrong_length() {
        assert!(decode(512, b"", &[0u8; 511]).is_err());
        assert!(decode(512, b"", &[0u8; 513]).is_err());
        assert!(decode(512, b"", &[]).is_err());
    }

    #[test]
    fn decode_rejects_bit_flip_in_masked_db() {
        let seed = random_seed();
        let mut em = encode(512, &seed, b"label", b"msg").unwrap();
        em[HASH_LEN + 5] ^= 0xFF; // flip bits in maskedDB region
        assert!(decode(512, b"label", &em).is_err());
    }

    #[test]
    fn decode_rejects_bit_flip_in_masked_seed() {
        let seed = random_seed();
        let mut em = encode(512, &seed, b"label", b"msg").unwrap();
        em[3] ^= 0xFF; // flip bits in maskedSeed region
        assert!(decode(512, b"label", &em).is_err());
    }

    #[test]
    fn em_first_byte_is_zero() {
        let seed = random_seed();
        let em = encode(512, &seed, b"", b"test").unwrap();
        assert_eq!(em[0], 0x00, "EM[0] must always be 0x00");
    }

    #[test]
    fn different_seeds_give_different_ciphertexts() {
        let seed1 = random_seed();
        let mut seed2 = random_seed();
        // Ensure seeds differ (astronomically unlikely they collide, but be safe)
        seed2[0] ^= 0xFF;
        let em1 = encode(512, &seed1, b"", b"same message").unwrap();
        let em2 = encode(512, &seed2, b"", b"same message").unwrap();
        assert_ne!(
            em1.to_vec(),
            em2.to_vec(),
            "different seeds must produce different EM"
        );
    }
}
