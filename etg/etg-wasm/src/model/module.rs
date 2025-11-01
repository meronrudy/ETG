//! Module-level IR for WASM MVP: module structure, expressions, function bodies, segments.

use super::types::{
    Export, FuncIdx, FuncType, GlobalIdx, GlobalType, Import, MemIdx, MemoryType, RefType, TableIdx,
    TableType, TypeIdx, ValType,
};

/// Local declarations inside a function body (count repetitions of a valtype).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LocalDecl {
    pub count: u32,
    pub val_type: ValType,
}

/// Raw expression (sequence of bytes ending with `end`) used in initializers (globals, offsets).
/// Decoding/validation is performed later.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Expr {
    pub body: Vec<u8>,
}

/// Code body for a defined function: locals and raw instruction bytes (terminated by `end`).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CodeBody {
    pub locals: Vec<LocalDecl>,
    pub body: Vec<u8>,
}

/// Global with type and initializer expression.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Global {
    pub ty: GlobalType,
    pub init: Expr,
}

/// Active element segment (MVP): initializes table elements with function indices at offset expr.
/// MVP assumes table index 0 in typical modules; still stored explicitly.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct ElementSegment {
    pub table: TableIdx,
    pub offset: Expr,
    pub init: Vec<FuncIdx>,
}

/// Active data segment (MVP): initializes memory with bytes at offset expr.
/// MVP assumes memory index 0; still stored explicitly.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct DataSegment {
    pub memory: MemIdx,
    pub offset: Expr,
    pub init: Vec<u8>,
}

/// The parse-time module IR (pre-validation, pre-instantiation).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Module {
    // Types and declarations
    pub types: Vec<FuncType>,
    pub imports: Vec<Import>,
    /// Type indices for each defined (non-imported) function, in module order.
    pub func_type_indices: Vec<TypeIdx>,
    pub tables: Vec<TableType>,
    pub memories: Vec<MemoryType>,
    pub globals: Vec<Global>,

    // Exports and start
    pub exports: Vec<Export>,
    pub start: Option<FuncIdx>,

    // Segments and code
    pub elements: Vec<ElementSegment>,
    /// Code bodies for defined functions (length must equal func_type_indices.len()).
    pub codes: Vec<CodeBody>,
    pub data: Vec<DataSegment>,

    // Precomputed import counts for index space arithmetic.
    pub imported_funcs: u32,
    pub imported_tables: u32,
    pub imported_memories: u32,
    pub imported_globals: u32,
}

impl Module {
    /// Returns total counts including imports for each index space.
    pub fn total_funcs(&self) -> u32 {
        self.imported_funcs + (self.func_type_indices.len() as u32)
    }
    pub fn total_tables(&self) -> u32 {
        self.imported_tables + (self.tables.len() as u32)
    }
    pub fn total_memories(&self) -> u32 {
        self.imported_memories + (self.memories.len() as u32)
    }
    pub fn total_globals(&self) -> u32 {
        self.imported_globals + (self.globals.len() as u32)
    }
}
