//! Higher-level binary helpers: length-prefixed vectors, names, and convenience reads.

use super::{cursor::Cursor, leb128, BinaryReadError, Result};

/// Read a length-prefixed vector of raw bytes (u32 length via ULEB128).
pub fn read_len_prefixed_bytes(cur: &mut Cursor) -> Result<Vec<u8>> {
    let len = leb128::read_uleb_u32(cur)? as usize;
    let bytes = cur.read_bytes(len)?.to_vec();
    Ok(bytes)
}

/// Read a UTF-8 name (length-prefixed bytes).
pub fn read_name(cur: &mut Cursor) -> Result<String> {
    let bytes = read_len_prefixed_bytes(cur)?;
    match String::from_utf8(bytes) {
        Ok(s) => Ok(s),
        Err(_) => Err(BinaryReadError::InvalidUtf8 {
            offset: cur.offset(),
        }),
    }
}

/// Read a vector of T using the provided element reader closure.
/// Length is encoded as ULEB128 u32.
pub fn read_vec<T, F>(cur: &mut Cursor, mut elem: F) -> Result<Vec<T>>
where
    F: FnMut(&mut Cursor) -> Result<T>,
{
    let len = leb128::read_uleb_u32(cur)? as usize;
    let mut out = Vec::with_capacity(len);
    for _ in 0..len {
        out.push(elem(cur)?);
    }
    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn read_name_ok() {
        let data = [0x03, b'f', b'o', b'o']; // len=3, "foo"
        let mut c = Cursor::new(&data);
        let s = read_name(&mut c).unwrap();
        assert_eq!(s, "foo");
    }

    #[test]
    fn read_vec_of_bytes() {
        // vec length=2, then each elem is a single u8 byte read via closure
        let data = [0x02, 0xAA, 0xBB];
        let mut c = Cursor::new(&data);
        let v = read_vec(&mut c, |c| c.read_u8()) .unwrap();
        assert_eq!(v, vec![0xAA, 0xBB]);
    }
}
