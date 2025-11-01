//! Core WASM MVP type definitions: value types, function types, limits, table/memory/global types,
//! import/export descriptors, and index aliases.

#[allow(dead_code)]
pub type TypeIdx = u32;
#[allow(dead_code)]
pub type FuncIdx = u32;
#[allow(dead_code)]
pub type TableIdx = u32;
#[allow(dead_code)]
pub type MemIdx = u32;
#[allow(dead_code)]
pub type GlobalIdx = u32;

/// Value type (MVP).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ValType {
    I32,
    I64,
    F32,
    F64,
}

impl Default for ValType {
    fn default() -> Self {
        ValType::I32
    }
}

/// Stack value representation. For floats, store the raw IEEE-754 bits (preserve NaN payloads).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Value {
    I32(i32),
    I64(i64),
    F32(u32),
    F64(u64),
}

/// Function type: params and results (MVP result arity: 0 or 1; enforced at validation time).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct FuncType {
    pub params: Vec<ValType>,
    pub results: Vec<ValType>,
}

/// Min/max limits for tables/memories (units: elements for tables, pages (64KiB) for memories).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Limits {
    pub min: u32,
    pub max: Option<u32>,
}
impl Limits {
    pub const fn new(min: u32, max: Option<u32>) -> Self {
        Self { min, max }
    }
}
impl Default for Limits {
    fn default() -> Self {
        Self { min: 0, max: None }
    }
}

/// Reference type. MVP supports only funcref.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RefType {
    FuncRef,
}

impl Default for RefType {
    fn default() -> Self {
        RefType::FuncRef
    }
}

/// Table type (MVP: funcref only).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct TableType {
    pub elem: RefType,
    pub limits: Limits,
}

/// Memory type (MVP: 32-bit index space; one memory per module max).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct MemoryType {
    pub limits: Limits,
}

/// Global type with content value type and mutability.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GlobalType {
    pub val_type: ValType,
    pub mutable: bool,
}
impl GlobalType {
    pub const fn new(val_type: ValType, mutable: bool) -> Self {
        Self { val_type, mutable }
    }
}

/// Import descriptor kinds (MVP).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportDesc {
    Func(TypeIdx),
    Table(TableType),
    Memory(MemoryType),
    Global(GlobalType),
}

impl Default for ImportDesc {
    fn default() -> Self {
        ImportDesc::Func(0)
    }
}

/// Import: module/name and descriptor.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Import {
    pub module: String,
    pub name: String,
    pub desc: ImportDesc,
}

/// Export descriptor kinds (MVP).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ExportDesc {
    Func(FuncIdx),
    Table(TableIdx),
    Memory(MemIdx),
    Global(GlobalIdx),
}

impl Default for ExportDesc {
    fn default() -> Self {
        ExportDesc::Func(0)
    }
}

/// Export: name and descriptor.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct Export {
    pub name: String,
    pub desc: ExportDesc,
}
