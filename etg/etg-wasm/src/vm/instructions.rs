#![allow(dead_code)]
//! Opcode constants and immediate decoding helpers for the interpreter.

pub mod op {
    pub const UNREACHABLE: u8 = 0x00;
    pub const NOP: u8 = 0x01;
    pub const BLOCK: u8 = 0x02;
    pub const LOOP: u8 = 0x03;
    pub const IF: u8 = 0x04;
    pub const ELSE: u8 = 0x05;
    pub const END: u8 = 0x0B;
    pub const BR: u8 = 0x0C;
    pub const BR_IF: u8 = 0x0D;
    pub const BR_TABLE: u8 = 0x0E;
    pub const RETURN: u8 = 0x0F;

    pub const CALL: u8 = 0x10;
    pub const CALL_INDIRECT: u8 = 0x11;

    // Locals / Globals
    pub const GET_LOCAL: u8 = 0x20;
    pub const SET_LOCAL: u8 = 0x21;
    pub const TEE_LOCAL: u8 = 0x22;
    pub const GET_GLOBAL: u8 = 0x23;
    pub const SET_GLOBAL: u8 = 0x24;

    pub const DROP: u8 = 0x1A;
    pub const SELECT: u8 = 0x1B;

    // Memory loads
    pub const I32_LOAD: u8 = 0x28;
    pub const I64_LOAD: u8 = 0x29;
    pub const F32_LOAD: u8 = 0x2A;
    pub const F64_LOAD: u8 = 0x2B;
    pub const I32_LOAD8_S: u8 = 0x2C;
    pub const I32_LOAD8_U: u8 = 0x2D;
    pub const I32_LOAD16_S: u8 = 0x2E;
    pub const I32_LOAD16_U: u8 = 0x2F;
    pub const I64_LOAD8_S: u8 = 0x30;
    pub const I64_LOAD8_U: u8 = 0x31;
    pub const I64_LOAD16_S: u8 = 0x32;
    pub const I64_LOAD16_U: u8 = 0x33;
    pub const I64_LOAD32_S: u8 = 0x34;
    pub const I64_LOAD32_U: u8 = 0x35;

    // Memory stores
    pub const I32_STORE: u8 = 0x36;
    pub const I64_STORE: u8 = 0x37;
    pub const F32_STORE: u8 = 0x38;
    pub const F64_STORE: u8 = 0x39;
    pub const I32_STORE8: u8 = 0x3A;
    pub const I32_STORE16: u8 = 0x3B;
    pub const I64_STORE8: u8 = 0x3C;
    pub const I64_STORE16: u8 = 0x3D;
    pub const I64_STORE32: u8 = 0x3E;

    // Memory queries
    pub const MEMORY_SIZE: u8 = 0x3F;
    pub const MEMORY_GROW: u8 = 0x40;

    pub const I32_CONST: u8 = 0x41;
    pub const I64_CONST: u8 = 0x42;
    pub const F32_CONST: u8 = 0x43;
    pub const F64_CONST: u8 = 0x44;

    // i32 comparisons
    pub const I32_EQ: u8 = 0x46;
    pub const I32_LT_S: u8 = 0x48;
    pub const I32_LT_U: u8 = 0x49;

    // i64 comparisons
    pub const I64_EQ: u8 = 0x51;
    pub const I64_LT_S: u8 = 0x53;
    pub const I64_LT_U: u8 = 0x54;

    // f32 comparisons
    pub const F32_EQ: u8 = 0x5B;
    pub const F32_LT: u8 = 0x5D;

    // f64 comparisons
    pub const F64_EQ: u8 = 0x61;
    pub const F64_LT: u8 = 0x63;

    // i32 arithmetic
    pub const I32_ADD: u8 = 0x6A;
    pub const I32_SUB: u8 = 0x6B;
    pub const I32_MUL: u8 = 0x6C;
    pub const I32_DIV_S: u8 = 0x6D;
    pub const I32_DIV_U: u8 = 0x6E;

    // i64 arithmetic
    pub const I64_ADD: u8 = 0x7C;
    pub const I64_SUB: u8 = 0x7D;
    pub const I64_MUL: u8 = 0x7E;
    pub const I64_DIV_S: u8 = 0x7F;
    pub const I64_DIV_U: u8 = 0x80;

    // f32 arithmetic
    pub const F32_ADD: u8 = 0x92;
    pub const F32_SUB: u8 = 0x93;
    pub const F32_MUL: u8 = 0x94;
    pub const F32_DIV: u8 = 0x95;

    // f64 arithmetic
    pub const F64_ADD: u8 = 0xA0;
    pub const F64_SUB: u8 = 0xA1;
    pub const F64_MUL: u8 = 0xA2;
    pub const F64_DIV: u8 = 0xA3;
}

use crate::binary::{cursor::Cursor, leb128};
use crate::error::Trap;

#[inline]
pub fn read_i32_const(cur: &mut Cursor) -> Result<i32, Trap> {
    leb128::read_sleb_i32(cur).map_err(|_| Trap::Unimplemented("bad i32.const immediate"))
}

#[inline]
pub fn read_i64_const(cur: &mut Cursor) -> Result<i64, Trap> {
    leb128::read_sleb_i64(cur).map_err(|_| Trap::Unimplemented("bad i64.const immediate"))
}

#[inline]
pub fn read_f32_bits(cur: &mut Cursor) -> Result<u32, Trap> {
    let b = cur.read_bytes(4).map_err(|_| Trap::Unimplemented("bad f32.const immediate"))?;
    Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
}

#[inline]
pub fn read_f64_bits(cur: &mut Cursor) -> Result<u64, Trap> {
    let b = cur.read_bytes(8).map_err(|_| Trap::Unimplemented("bad f64.const immediate"))?;
    Ok(u64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]))
}
