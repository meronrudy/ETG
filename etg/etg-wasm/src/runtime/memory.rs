//! Linear memory instance (MVP, 32-bit index space).
//! Provides page-based growth, size helpers, and bounds-checked little-endian loads/stores.

use crate::model::MemoryType;

/// WASM page size in bytes (64 KiB).
pub const PAGE_SIZE: usize = 64 * 1024;

#[derive(Debug, Clone)]
pub struct MemoryInstance {
    buf: Vec<u8>,
    // Limits in pages
    min: u32,
    max: Option<u32>,
}

impl MemoryInstance {
    /// Create a memory from its declared type (limits in pages).
    pub fn new(ty: &MemoryType) -> Self {
        let min = ty.limits.min;
        let max = ty.limits.max;
        let mut buf = Vec::with_capacity((min as usize) * PAGE_SIZE);
        buf.resize((min as usize) * PAGE_SIZE, 0);
        Self { buf, min, max }
    }

    /// Current size in pages.
    pub fn size_pages(&self) -> u32 {
        (self.buf.len() / PAGE_SIZE) as u32
    }

    /// Grow by delta pages. Returns previous size on success, or None on failure.
    pub fn grow(&mut self, delta_pages: u32) -> Option<u32> {
        let prev = self.size_pages();
        let new = prev.saturating_add(delta_pages);
        if let Some(max) = self.max {
            if new > max {
                return None;
            }
        }
        let new_len = (new as usize) * PAGE_SIZE;
        self.buf.resize(new_len, 0);
        Some(prev)
    }

    /// Immutable view of the underlying buffer.
    pub fn data(&self) -> &[u8] {
        &self.buf
    }

    /// Mutable view of the underlying buffer.
    pub fn data_mut(&mut self) -> &mut [u8] {
        &mut self.buf
    }

    /* ===== Bounds-checked loads/stores (little-endian) ===== */

    #[inline]
    fn check_bounds(&self, addr: u32, len: usize) -> Result<usize, ()> {
        let start = addr as usize;
        let end = start.checked_add(len).ok_or(())?;
        if end <= self.buf.len() {
            Ok(start)
        } else {
            Err(())
        }
    }

    // Byte loads/stores
    pub fn load_u8(&self, addr: u32) -> Result<u8, ()> {
        let i = self.check_bounds(addr, 1)?;
        Ok(self.buf[i])
    }
    pub fn load_i8(&self, addr: u32) -> Result<i8, ()> {
        self.load_u8(addr).map(|v| v as i8)
    }
    pub fn store_u8(&mut self, addr: u32, v: u8) -> Result<(), ()> {
        let i = self.check_bounds(addr, 1)?;
        self.buf[i] = v;
        Ok(())
    }

    // 16-bit loads/stores
    pub fn load_u16(&self, addr: u32) -> Result<u16, ()> {
        let i = self.check_bounds(addr, 2)?;
        Ok(u16::from_le_bytes([self.buf[i], self.buf[i + 1]]))
    }
    pub fn load_i16(&self, addr: u32) -> Result<i16, ()> {
        self.load_u16(addr).map(|v| v as i16)
    }
    pub fn store_u16(&mut self, addr: u32, v: u16) -> Result<(), ()> {
        let i = self.check_bounds(addr, 2)?;
        let b = v.to_le_bytes();
        self.buf[i] = b[0];
        self.buf[i + 1] = b[1];
        Ok(())
    }

    // 32-bit loads/stores
    pub fn load_u32(&self, addr: u32) -> Result<u32, ()> {
        let i = self.check_bounds(addr, 4)?;
        Ok(u32::from_le_bytes([
            self.buf[i],
            self.buf[i + 1],
            self.buf[i + 2],
            self.buf[i + 3],
        ]))
    }
    pub fn load_i32(&self, addr: u32) -> Result<i32, ()> {
        self.load_u32(addr).map(|v| v as i32)
    }
    pub fn store_u32(&mut self, addr: u32, v: u32) -> Result<(), ()> {
        let i = self.check_bounds(addr, 4)?;
        let b = v.to_le_bytes();
        self.buf[i] = b[0];
        self.buf[i + 1] = b[1];
        self.buf[i + 2] = b[2];
        self.buf[i + 3] = b[3];
        Ok(())
    }

    // 64-bit loads/stores
    pub fn load_u64(&self, addr: u32) -> Result<u64, ()> {
        let i = self.check_bounds(addr, 8)?;
        Ok(u64::from_le_bytes([
            self.buf[i],
            self.buf[i + 1],
            self.buf[i + 2],
            self.buf[i + 3],
            self.buf[i + 4],
            self.buf[i + 5],
            self.buf[i + 6],
            self.buf[i + 7],
        ]))
    }
    pub fn load_i64(&self, addr: u32) -> Result<i64, ()> {
        self.load_u64(addr).map(|v| v as i64)
    }
    pub fn store_u64(&mut self, addr: u32, v: u64) -> Result<(), ()> {
        let i = self.check_bounds(addr, 8)?;
        let b = v.to_le_bytes();
        self.buf[i] = b[0];
        self.buf[i + 1] = b[1];
        self.buf[i + 2] = b[2];
        self.buf[i + 3] = b[3];
        self.buf[i + 4] = b[4];
        self.buf[i + 5] = b[5];
        self.buf[i + 6] = b[6];
        self.buf[i + 7] = b[7];
        Ok(())
    }

    // Floating-point bit-pattern loads/stores (preserving NaN payloads).
    pub fn load_f32_bits(&self, addr: u32) -> Result<u32, ()> {
        self.load_u32(addr)
    }
    pub fn store_f32_bits(&mut self, addr: u32, bits: u32) -> Result<(), ()> {
        self.store_u32(addr, bits)
    }
    pub fn load_f64_bits(&self, addr: u32) -> Result<u64, ()> {
        self.load_u64(addr)
    }
    pub fn store_f64_bits(&mut self, addr: u32, bits: u64) -> Result<(), ()> {
        self.store_u64(addr, bits)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn grow_and_bounds() {
        let mt = MemoryType { limits: crate::model::Limits { min: 1, max: Some(2) } };
        let mut mem = MemoryInstance::new(&mt);
        assert_eq!(mem.size_pages(), 1);
        assert!(mem.load_u8((PAGE_SIZE - 1) as u32).is_ok());
        assert!(mem.load_u8(PAGE_SIZE as u32).is_err());
        assert_eq!(mem.grow(1), Some(1));
        assert_eq!(mem.size_pages(), 2);
        assert!(mem.load_u8((2 * PAGE_SIZE - 1) as u32).is_ok());
        assert!(mem.grow(1).is_none()); // exceeds max
    }

    #[test]
    fn le_load_store() {
        let mt = MemoryType { limits: crate::model::Limits { min: 1, max: None } };
        let mut mem = MemoryInstance::new(&mt);

        mem.store_u32(0, 0x11223344).unwrap();
        assert_eq!(mem.load_u8(0).unwrap(), 0x44);
        assert_eq!(mem.load_u16(0).unwrap(), 0x3344);
        assert_eq!(mem.load_u32(0).unwrap(), 0x11223344);

        mem.store_u64(16, 0x1122334455667788).unwrap();
        assert_eq!(mem.load_u64(16).unwrap(), 0x1122334455667788);

        mem.store_f32_bits(32, 0x7FC00001).unwrap();
        assert_eq!(mem.load_f32_bits(32).unwrap(), 0x7FC00001);

        mem.store_f64_bits(40, 0x7FF8000000000001).unwrap();
        assert_eq!(mem.load_f64_bits(40).unwrap(), 0x7FF8000000000001);
    }
}
