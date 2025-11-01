#![allow(clippy::module_inception)]
//! Instance records for functions and modules. Minimal structures to be used by the Store.

use std::collections::HashMap;
use std::sync::Arc;

use crate::host::func::HostFunc;
use crate::model::{FuncType, TypeIdx, Value};

/// A function instance: either WASM-defined (points to a function body by index) or Host-provided.
#[derive(Clone)]
pub enum FuncInstance {
    /// WASM-defined function: references the function's type and the index into the module's code bodies.
    Wasm {
        type_idx: TypeIdx,
        /// Index into Module.codes (definition index, not including imports).
        def_index: usize,
        /// Owning module instance index in Store.modules.
        module: usize,
    },
    /// Host function: external callable with a known signature.
    Host {
        ty: FuncType,
        f: Arc<HostFunc>,
    },
}

impl std::fmt::Debug for FuncInstance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FuncInstance::Wasm { type_idx, def_index, module } => f
                .debug_struct("Wasm")
                .field("type_idx", type_idx)
                .field("def_index", def_index)
                .field("module", module)
                .finish(),
            FuncInstance::Host { ty, .. } => f.debug_struct("Host").field("ty", ty).finish(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RuntimeExportDesc {
    Func(usize),
    Table(usize),
    Memory(usize),
    Global(usize),
}

/// A module instance records the addresses (indices into the Store) of its imported and defined items,
/// and export bindings.
#[derive(Debug, Clone, Default)]
pub struct ModuleInstance {
    /// Absolute indices (into Store.funcs) for all functions in the module (imports first, then defs).
    pub funcs: Vec<usize>,
    /// Absolute indices into Store.tables
    pub tables: Vec<usize>,
    /// Absolute indices into Store.mems
    pub memories: Vec<usize>,
    /// Absolute indices into Store.globals
    pub globals: Vec<usize>,

    /// Exports by name (runtime addresses).
    pub exports: HashMap<String, RuntimeExportDesc>,

    /// Parse-time IR of the module to access code bodies, types, etc. at runtime.
    pub module_ir: Arc<crate::model::Module>,
}

impl ModuleInstance {
    /// Resolve an export name to runtime export descriptor.
    pub fn resolve_export(&self, name: &str) -> Option<RuntimeExportDesc> {
        self.exports.get(name).cloned()
    }

    /// Convenience: fetch code body by definition index (index into Module.codes).
    pub fn code_body(&self, def_index: usize) -> Option<&crate::model::CodeBody> {
        self.module_ir.codes.get(def_index)
    }

    /// Convenience: fetch function type by TypeIdx.
    pub fn func_type_by_typeidx(&self, type_idx: crate::model::TypeIdx) -> Option<&crate::model::FuncType> {
        self.module_ir.types.get(type_idx as usize)
    }
}
