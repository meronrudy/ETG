//! Byte cursor with offset tracking and little-endian primitives.

use super::BinaryReadError;

/// Cursor over a byte slice with absolute offset tracking.
#[derive(Clone, Copy)]
pub struct Cursor<'a> {
    data: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    /// Create a new cursor over the given bytes.
    pub fn new(data: &'a [u8]) -> Self {
        Self { data, pos: 0 }
    }

    /// Current absolute byte offset within the underlying slice.
    pub fn offset(&self) -> usize {
        self.pos
    }

    /// Remaining unread length.
    pub fn remaining(&self) -> usize {
        self.data.len().saturating_sub(self.pos)
    }

    /// True if at end of input.
    pub fn is_eof(&self) -> bool {
        self.pos >= self.data.len()
    }

    /// Peek next byte without advancing.
    pub fn peek_u8(&self) -> super::Result<u8> {
        self.data
            .get(self.pos)
            .copied()
            .ok_or(BinaryReadError::UnexpectedEof { offset: self.pos })
    }

    /// Read a single byte.
    pub fn read_u8(&mut self) -> super::Result<u8> {
        let b = self
            .data
            .get(self.pos)
            .copied()
            .ok_or(BinaryReadError::UnexpectedEof { offset: self.pos })?;
        self.pos += 1;
        Ok(b)
    }

    /// Read exactly n bytes and return a slice view into the underlying data.
    pub fn read_bytes(&mut self, n: usize) -> super::Result<&'a [u8]> {
        let end = self.pos.checked_add(n).ok_or(BinaryReadError::Malformed {
            offset: self.pos,
            msg: "position overflow",
        })?;
        if end > self.data.len() {
            return Err(BinaryReadError::UnexpectedEof { offset: self.pos });
        }
        let slice = &self.data[self.pos..end];
        self.pos = end;
        Ok(slice)
    }

    /// Skip exactly n bytes.
    pub fn skip(&mut self, n: usize) -> super::Result<()> {
        let _ = self.read_bytes(n)?;
        Ok(())
    }

    /// Read little-endian u32.
    pub fn read_u32_le(&mut self) -> super::Result<u32> {
        let b = self.read_bytes(4)?;
        Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
    }

    /// Read little-endian u64.
    pub fn read_u64_le(&mut self) -> super::Result<u64> {
        let b = self.read_bytes(8)?;
        Ok(u64::from_le_bytes([
            b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7],
        ]))
    }

    /// Return a subslice starting at current position with given length (no advance).
    pub fn slice(&self, n: usize) -> super::Result<&'a [u8]> {
        let end = self.pos.checked_add(n).ok_or(BinaryReadError::Malformed {
            offset: self.pos,
            msg: "position overflow",
        })?;
        self.data
            .get(self.pos..end)
            .ok_or(BinaryReadError::UnexpectedEof { offset: self.pos })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn basic_cursor_ops() {
        let bytes = [1u8, 2, 3, 4, 5, 6, 7, 8];
        let mut c = Cursor::new(&bytes);
        assert_eq!(c.offset(), 0);
        assert_eq!(c.peek_u8().unwrap(), 1);
        assert_eq!(c.read_u8().unwrap(), 1);
        assert_eq!(c.offset(), 1);
        let s = c.read_bytes(3).unwrap();
        assert_eq!(s, &[2, 3, 4]);
        assert_eq!(c.read_u32_le().unwrap(), 0x08070605);
        assert!(c.is_eof());
    }
}
