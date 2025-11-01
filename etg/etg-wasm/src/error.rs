//! Crate-level error types for etg-wasm.

use thiserror::Error;

#[derive(Debug, Error)]
pub enum ParseError {
    #[error(transparent)]
    Binary(#[from] crate::binary::BinaryReadError),

    #[error("unimplemented parse error: {0}")]
    Unimplemented(&'static str),
}

#[derive(Debug, Error)]
pub enum ValidationError {
    #[error("unimplemented validation error: {0}")]
    Unimplemented(&'static str),
}

#[derive(Debug, Error)]
pub enum LinkError {
    #[error("unresolved import: {module}.{name}")]
    UnresolvedImport { module: String, name: String },

    #[error("type mismatch ({context}): expected {expected}, found {found}")]
    TypeMismatch {
        context: &'static str,
        expected: String,
        found: String,
    },

    #[error("limits exceeded ({context})")]
    LimitsExceeded { context: &'static str },

    #[error("element segment initialization out of bounds")]
    ElemOutOfBounds,

    #[error("data segment initialization out of bounds")]
    DataOutOfBounds,

    #[error("trap while running start function")]
    StartTrap(#[source] Trap),

    #[error("unimplemented link error: {0}")]
    Unimplemented(&'static str),
}

#[derive(Debug, Error)]
pub enum Trap {
    #[error("unimplemented trap: {0}")]
    Unimplemented(&'static str),
}
