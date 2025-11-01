//! Public model/IR surface.

pub mod types;
pub mod module;

pub use types::{
    Export, ExportDesc, FuncIdx, FuncType, GlobalIdx, GlobalType, Import, ImportDesc, Limits,
    MemIdx, MemoryType, RefType, TableIdx, TableType, TypeIdx, ValType, Value,
};
pub use module::{
    CodeBody, DataSegment, ElementSegment, Expr, Global, LocalDecl, Module,
};
