//! ULEB128/SLEB128 decoding specialized for WASM MVP integer widths.

use super::{cursor::Cursor, BinaryReadError, Result};

/// Decode an unsigned LEB128 as u32 (max 5 bytes).
pub fn read_uleb_u32(cur: &mut Cursor) -> Result<u32> {
    read_uleb_generic(cur, 32).map(|v| v as u32)
}

/// Decode an unsigned LEB128 as u64 (max 10 bytes).
pub fn read_uleb_u64(cur: &mut Cursor) -> Result<u64> {
    read_uleb_generic(cur, 64)
}

/// Decode a signed LEB128 as i32 (max 5 bytes).
pub fn read_sleb_i32(cur: &mut Cursor) -> Result<i32> {
    read_sleb_generic(cur, 32).map(|v| v as i32)
}

/// Decode a signed LEB128 as i64 (max 10 bytes).
pub fn read_sleb_i64(cur: &mut Cursor) -> Result<i64> {
    read_sleb_generic(cur, 64).map(|v| v as i64)
}

fn read_uleb_generic(cur: &mut Cursor, bits: u8) -> Result<u64> {
    let mut result: u64 = 0;
    let mut shift: u32 = 0;
    let max_bytes = ((bits + 6) / 7) as u8; // ceiling(bits/7)

    for i in 0..max_bytes {
        let byte = cur.read_u8()?;
        let low = (byte & 0x7F) as u64;
        if shift >= 64 || (low << shift) >> shift != low {
            return Err(BinaryReadError::Leb128Overflow {
                target_bits: bits,
                offset: cur.offset(),
            });
        }
        result |= low << shift;

        if (byte & 0x80) == 0 {
            // Final byte. Check that higher bits beyond target width are zero.
            if bits < 64 && (result >> bits) != 0 {
                return Err(BinaryReadError::Leb128Overflow {
                    target_bits: bits,
                    offset: cur.offset(),
                });
            }
            return Ok(result);
        }
        shift += 7;
        if shift as u8 >= bits + 7 && i + 1 == max_bytes {
            // We consumed max bytes but still have continuation bit set.
            return Err(BinaryReadError::Leb128TooManyBytes {
                limit: max_bytes,
                offset: cur.offset(),
            });
        }
    }

    Err(BinaryReadError::Leb128TooManyBytes {
        limit: max_bytes,
        offset: cur.offset(),
    })
}

fn read_sleb_generic(cur: &mut Cursor, bits: u8) -> Result<i64> {
    let mut result: i64 = 0;
    let mut shift: u32 = 0;
    let mut byte: u8;
    let size = bits;
    let max_bytes = ((bits + 6) / 7) as u8;

    for i in 0..max_bytes {
        byte = cur.read_u8()?;
        let low = (byte & 0x7F) as i64;
        result |= low << shift;

        shift += 7;
        let cont = (byte & 0x80) != 0;
        if !cont {
            // Sign extend if sign bit set and we haven't filled the full width.
            if (byte & 0x40) != 0 && shift < size as u32 {
                result |= (!0i64) << shift;
            }
            // Check range fits exactly within size bits.
            let min = -(1i64 << (size - 1));
            let max = (1i64 << (size - 1)) - 1;
            if result < min || result > max {
                return Err(BinaryReadError::Leb128Overflow {
                    target_bits: bits,
                    offset: cur.offset(),
                });
            }
            return Ok(result);
        }

        if i + 1 == max_bytes {
            return Err(BinaryReadError::Leb128TooManyBytes {
                limit: max_bytes,
                offset: cur.offset(),
            });
        }
    }

    Err(BinaryReadError::Leb128TooManyBytes {
        limit: max_bytes,
        offset: cur.offset(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary::cursor::Cursor;

    #[test]
    fn uleb32_basic() {
        let mut c = Cursor::new(&[0xE5, 0x8E, 0x26]); // 624485
        let v = read_uleb_u32(&mut c).unwrap();
        assert_eq!(v, 624485);
    }

    #[test]
    fn sleb32_basic() {
        // -624485 encoded as SLEB128: 9b f1 59
        let mut c = Cursor::new(&[0x9b, 0xf1, 0x59]);
        let v = read_sleb_i32(&mut c).unwrap();
        assert_eq!(v, -624485);
    }

    #[test]
    fn uleb32_overflow() {
        // Too many continuation bytes for u32
        let bytes = [0xFFu8; 6];
        let mut c = Cursor::new(&bytes);
        let err = read_uleb_u32(&mut c).unwrap_err();
        match err {
            BinaryReadError::Leb128TooManyBytes { .. } | BinaryReadError::Leb128Overflow { .. } => {}
            e => panic!("unexpected error: {e:?}"),
        }
    }
}
