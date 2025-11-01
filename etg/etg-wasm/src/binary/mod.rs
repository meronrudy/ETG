//! Binary parsing utilities for WASM MVP: cursor, LEB128, helpers, and section headers.
//! These utilities intentionally use a local error type (BinaryReadError).
//! Higher layers can wrap/translate to crate::error::ParseError later.

pub mod cursor;
pub mod leb128;
pub mod reader;
pub mod sections;

use thiserror::Error;

/// Result alias for binary reading operations.
pub type Result<T> = core::result::Result<T, BinaryReadError>;

/// Errors that can occur while reading a WASM binary stream.
#[derive(Debug, Error)]
pub enum BinaryReadError {
    #[error("unexpected EOF at offset {offset}")]
    UnexpectedEof { offset: usize },

    #[error("ULEB128 overflow (target bits={target_bits}) at offset {offset}")]
    Leb128Overflow { target_bits: u8, offset: usize },

    #[error("too many bytes in LEB128 (limit={limit}) at offset {offset}")]
    Leb128TooManyBytes { limit: u8, offset: usize },

    #[error("invalid UTF-8 string at offset {offset}")]
    InvalidUtf8 { offset: usize },

    #[error("integer out of range at offset {offset}")]
    IntegerOutOfRange { offset: usize },

    #[error("malformed binary at offset {offset}: {msg}")]
    Malformed { offset: usize, msg: &'static str },
}
