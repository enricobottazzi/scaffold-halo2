use halo2_proofs::halo2curves::bn256::Fr as Fp;
use num_bigint::BigUint;

/// Converts a Field element to a BigUint
fn fp_to_big_uint(f: Fp) -> BigUint {
    BigUint::from_bytes_le(f.to_bytes().as_slice())
}

// Converts Fp to n chunks of 8 bits. If the number of chunks is less than n, then the chunks are padded with 0s. If the number of chunks is greater than n, then the chunks are truncated by removing the least significant bits.
pub fn big_uint_to_8bit_chunks(value: Fp, n: usize) -> Vec<u8> {
    let value_biguint = fp_to_big_uint(value);

    let mut chunks = value_biguint.to_bytes_be();

    while chunks.len() < n {
        chunks.insert(0, 0);
    }

    // Truncate excess bytes from the end if chunks length is more than n.
    if chunks.len() > n {
        chunks.truncate(n);
    }

    chunks
}

// Converts a vector of 8 bit chunks to a vector of running sums of the chunks.
pub fn running_sums_of_chunks(chunks: Vec<u8>) -> Vec<BigUint> {
    let mut running_sum = BigUint::from(0_u8);
    let mut sums = Vec::with_capacity(chunks.len());

    for &chunk in &chunks {
        running_sum = (running_sum << 8) + chunk as u64;
        sums.push(running_sum.clone());
    }

    sums
}

#[cfg(test)]
mod testing {

    use super::*;

    #[test]
    fn test_fp_to_big_uint() {
        let f = Fp::from(5);
        let big_uint = fp_to_big_uint(f);
        assert_eq!(big_uint, BigUint::from(5u8));
    }

    // convert a 32 bit number in 4 chunks. Should correctly convert to 4 chunks of 8 bits
    #[test]
    fn test_big_uint_to_8bit_chunks_no_padding() {
        let f = Fp::from(0x1f2f3f4f);
        let chunks = big_uint_to_8bit_chunks(f, 4);
        assert_eq!(chunks, vec![0x1f, 0x2f, 0x3f, 0x4f]);
    }

    // convert a 32 bit number in 6 chunks. Should correctly convert to 6 chunks of 8 bits in which the first 2 chunks are 0 padded.
    #[test]
    fn test_big_uint_to_8bit_chunks_padding() {
        let f = Fp::from(0x1f2f3f4f);
        let chunks = big_uint_to_8bit_chunks(f, 6);
        assert_eq!(chunks, vec![0x00, 0x00, 0x1f, 0x2f, 0x3f, 0x4f]);
    }

    // convert a 32 bit number in 2 chunks. Should convert to 2 chunks of 8 bits containing the most significant bits (and truncating the least significant bits)
    #[test]
    fn test_big_uint_to_8bit_chunks_overflow() {
        let f = Fp::from(0x1f2f3f4f);
        let chunks = big_uint_to_8bit_chunks(f, 2);
        assert_eq!(chunks, vec![0x1f, 0x2f]);
    }

    // Return the running sum from a vector of chunks
    #[test]
    fn test_running_sums_of_chunks() {
        let chunks = vec![0x1f, 0x2f, 0x3f, 0x4f];
        let sums = running_sums_of_chunks(chunks);
        assert_eq!(
            sums,
            vec![
                BigUint::from(0x1f_u64),
                BigUint::from(0x1f2f_u64),
                BigUint::from(0x1f2f3f_u64),
                BigUint::from(0x1f2f3f4f_u64)
            ]
        );
    }

    // Return the running sum from a vector of chunks with overflow
    #[test]
    fn test_running_sums_of_chunks_overflow() {
        let f = Fp::from(0x1f2f3f4f5f);
        let chunks = big_uint_to_8bit_chunks(f, 4);
        let sums = running_sums_of_chunks(chunks);
        assert_eq!(
            sums,
            vec![
                BigUint::from(0x1f_u64),
                BigUint::from(0x1f2f_u64),
                BigUint::from(0x1f2f3f_u64),
                BigUint::from(0x1f2f3f4f_u64)
            ]
        );
    }
}
