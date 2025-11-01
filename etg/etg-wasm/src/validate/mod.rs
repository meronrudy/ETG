#![allow(clippy::match_like_matches_macro)]

//! Module validator for WASM MVP.
//! Checks structural and index-space invariants. Full instruction typing to be added later.

use std::collections::HashSet;

use crate::error::ValidationError;
use crate::model::{
    ExportDesc, FuncIdx, FuncType, ImportDesc, MemIdx, Module, RefType, TableIdx, TypeIdx,
};

type VResult<T> = Result<T, ValidationError>;

struct TypeEnv<'a> {
    m: &'a Module,
    // Ordered list of function type indices for imported functions (in import appearance order)
    func_import_types: Vec<TypeIdx>,
}

impl<'a> TypeEnv<'a> {
    fn new(m: &'a Module) -> VResult<Self> {
        let mut func_import_types = Vec::with_capacity(m.imported_funcs as usize);
        for imp in &m.imports {
            if let ImportDesc::Func(tidx) = imp.desc {
                func_import_types.push(tidx);
            }
        }
        if func_import_types.len() as u32 != m.imported_funcs {
            return Err(ValidationError::Unimplemented(
                "imported function count mismatch",
            ));
        }
        Ok(Self {
            m,
            func_import_types,
        })
    }

    #[inline]
    fn total_funcs(&self) -> u32 {
        self.m.total_funcs()
    }
    #[inline]
    fn total_tables(&self) -> u32 {
        self.m.total_tables()
    }
    #[inline]
    fn total_mems(&self) -> u32 {
        self.m.total_memories()
    }
    #[inline]
    fn total_globals(&self) -> u32 {
        self.m.total_globals()
    }

    /// Resolve an absolute function index to its declared function type index.
    fn func_type_idx(&self, fidx: FuncIdx) -> VResult<TypeIdx> {
        if fidx < self.m.imported_funcs {
            let i = fidx as usize;
            self.func_import_types
                .get(i)
                .copied()
                .ok_or(ValidationError::Unimplemented(
                    "function import index out of range",
                ))
        } else {
            let def_i = (fidx - self.m.imported_funcs) as usize;
            self.m
                .func_type_indices
                .get(def_i)
                .copied()
                .ok_or(ValidationError::Unimplemented(
                    "defined function index out of range",
                ))
        }
    }

    /// Resolve an absolute function index to its FuncType.
    fn func_type(&self, fidx: FuncIdx) -> VResult<&'a FuncType> {
        let tidx = self.func_type_idx(fidx)?;
        self.m
            .types
            .get(tidx as usize)
            .ok_or(ValidationError::Unimplemented(
                "function type index out of range",
            ))
    }
}

pub fn validate_module(m: &Module) -> VResult<()> {
    let env = TypeEnv::new(m)?;

    /* Types and function declarations */
    for &tidx in &m.func_type_indices {
        if (tidx as usize) >= m.types.len() {
            return Err(ValidationError::Unimplemented(
                "function type index out of range",
            ));
        }
    }

    /* Tables */
    for tt in &m.tables {
        if !matches!(tt.elem, RefType::FuncRef) {
            return Err(ValidationError::Unimplemented(
                "non-funcref table not allowed in MVP",
            ));
        }
        if let Some(max) = tt.limits.max {
            if max < tt.limits.min {
                return Err(ValidationError::Unimplemented(
                    "table limits max < min",
                ));
            }
        }
    }

    /* Memories */
    if m.memories.len() > 1 {
        return Err(ValidationError::Unimplemented(
            "multiple memories not allowed in MVP",
        ));
    }
    for mt in &m.memories {
        if let Some(max) = mt.limits.max {
            if max < mt.limits.min {
                return Err(ValidationError::Unimplemented(
                    "memory limits max < min",
                ));
            }
        }
    }

    /* Exports */
    let mut export_names = HashSet::new();
    for ex in &m.exports {
        if !export_names.insert(&ex.name) {
            return Err(ValidationError::Unimplemented(
                "duplicate export name",
            ));
        }
        match ex.desc {
            ExportDesc::Func(f) => {
                if f >= env.total_funcs() {
                    return Err(ValidationError::Unimplemented(
                        "exported function index out of range",
                    ));
                }
            }
            ExportDesc::Table(t) => {
                if t >= env.total_tables() {
                    return Err(ValidationError::Unimplemented(
                        "exported table index out of range",
                    ));
                }
            }
            ExportDesc::Memory(mem) => {
                if mem >= env.total_mems() {
                    return Err(ValidationError::Unimplemented(
                        "exported memory index out of range",
                    ));
                }
            }
            ExportDesc::Global(g) => {
                if g >= env.total_globals() {
                    return Err(ValidationError::Unimplemented(
                        "exported global index out of range",
                    ));
                }
            }
        }
    }

    /* Start function */
    if let Some(start_idx) = m.start {
        if start_idx >= env.total_funcs() {
            return Err(ValidationError::Unimplemented(
                "start function index out of range",
            ));
        }
        let fty = env.func_type(start_idx)?;
        if !fty.params.is_empty() || !fty.results.is_empty() {
            return Err(ValidationError::Unimplemented(
                "start function must have type [] -> []",
            ));
        }
    }

    /* Elements (active segments) */
    for seg in &m.elements {
        let table: TableIdx = seg.table;
        if table >= env.total_tables() {
            return Err(ValidationError::Unimplemented(
                "element segment table index out of range",
            ));
        }
        for &func_idx in &seg.init {
            if func_idx >= env.total_funcs() {
                return Err(ValidationError::Unimplemented(
                    "element segment function index out of range",
                ));
            }
        }
    }

    /* Code bodies */
    if m.func_type_indices.len() != m.codes.len() {
        return Err(ValidationError::Unimplemented(
            "function/code count mismatch",
        ));
    }
    for code in &m.codes {
        // Ensure function body ends with 'end' (0x0B).
        match code.body.last() {
            Some(0x0B) => {}
            _ => {
                return Err(ValidationError::Unimplemented(
                    "function body missing terminating 'end'",
                ))
            }
        }
    }

    /* Data segments */
    for seg in &m.data {
        let mem: MemIdx = seg.memory;
        if mem >= env.total_mems() {
            return Err(ValidationError::Unimplemented(
                "data segment memory index out of range",
            ));
        }
    }

    Ok(())
}
