 //! etg-wasm: WASM MVP runtime/interpreter (scaffolding with parser wiring)

pub mod error;
pub mod binary;
pub mod model;
pub mod validate;
pub mod runtime;
pub mod vm;
pub mod host;

pub use model::{Module, Value, ValType};

/// Parse a WASM binary into a Module IR (public API).
/// This delegates to the internal binary parser and translates low-level binary errors
/// into crate-level ParseError via the From impl.
pub fn parse(bytes: &[u8]) -> Result<Module, error::ParseError> {
    let module = crate::binary::sections::parse_module_from_bytes(bytes)?;
    Ok(module)
}

/// Validate a parsed Module using the MVP validator.
pub fn validate(m: &Module) -> Result<(), error::ValidationError> {
    crate::validate::validate_module(m)
}

/// Instantiate a validated Module.
pub fn instantiate(
    store: &mut runtime::Store,
    module_ir: std::sync::Arc<Module>,
    resolver: &impl host::ImportResolver,
) -> Result<runtime::InstanceHandle, error::LinkError> {
    use crate::error::LinkError;
    use crate::model::{ExportDesc, ImportDesc};
    use crate::runtime::instances::{FuncInstance, RuntimeExportDesc};
    use crate::runtime::{GlobalInstance, MemoryInstance, TableInstance};
    use std::collections::HashMap;

    // Allocate empty runtime instance with IR attached
    let handle = store.alloc_module_ir(module_ir.clone());
    let module_index = handle.0;
    let module = module_ir;

    // Build index spaces locally to avoid borrowing Store and ModuleInstance simultaneously.
    let mut funcs: Vec<usize> = Vec::with_capacity(module.total_funcs() as usize);
    let mut tables: Vec<usize> = Vec::with_capacity(module.total_tables() as usize);
    let mut memories: Vec<usize> = Vec::with_capacity(module.total_memories() as usize);
    let mut globals: Vec<usize> = Vec::with_capacity(module.total_globals() as usize);

    // 1) Resolve imports
    for imp in &module.imports {
        match &imp.desc {
            ImportDesc::Func(type_idx) => {
                let fty = module
                    .types
                    .get(*type_idx as usize)
                    .ok_or(LinkError::Unimplemented("invalid typeidx in import"))?
                    .clone();
                let host_f = resolver
                    .resolve_func(&imp.module, &imp.name, &fty)
                    .ok_or(LinkError::UnresolvedImport {
                        module: imp.module.clone(),
                        name: imp.name.clone(),
                    })?;
                let addr = store.alloc_func(FuncInstance::Host { ty: fty, f: host_f });
                funcs.push(addr);
            }
            ImportDesc::Table(tt) => {
                let addr = resolver
                    .resolve_table(&imp.module, &imp.name, tt)
                    .ok_or(LinkError::UnresolvedImport {
                        module: imp.module.clone(),
                        name: imp.name.clone(),
                    })?;
                // basic compatibility: imported table has at least min elements
                let t = store
                    .get_table(addr)
                    .ok_or(LinkError::TypeMismatch {
                        context: "table import addr",
                        expected: format!("existing Table({:?})", tt.limits),
                        found: "invalid address".to_string(),
                    })?;
                if t.size() < tt.limits.min {
                    return Err(LinkError::TypeMismatch {
                        context: "table import limits",
                        expected: format!("min >= {}", tt.limits.min),
                        found: format!("size {}", t.size()),
                    });
                }
                tables.push(addr);
            }
            ImportDesc::Memory(mt) => {
                let addr = resolver
                    .resolve_memory(&imp.module, &imp.name, mt)
                    .ok_or(LinkError::UnresolvedImport {
                        module: imp.module.clone(),
                        name: imp.name.clone(),
                    })?;
                let m = store.get_memory(addr).ok_or(LinkError::TypeMismatch {
                    context: "memory import addr",
                    expected: format!("existing Memory({:?})", mt.limits),
                    found: "invalid address".to_string(),
                })?;
                if m.size_pages() < mt.limits.min {
                    return Err(LinkError::TypeMismatch {
                        context: "memory import limits",
                        expected: format!("min >= {}", mt.limits.min),
                        found: format!("size {}", m.size_pages()),
                    });
                }
                memories.push(addr);
            }
            ImportDesc::Global(gt) => {
                let addr = resolver
                    .resolve_global(&imp.module, &imp.name, gt)
                    .ok_or(LinkError::UnresolvedImport {
                        module: imp.module.clone(),
                        name: imp.name.clone(),
                    })?;
                let g = store.get_global(addr).ok_or(LinkError::TypeMismatch {
                    context: "global import addr",
                    expected: format!("Global({:?})", gt),
                    found: "invalid address".to_string(),
                })?;
                if g.ty() != gt {
                    return Err(LinkError::TypeMismatch {
                        context: "global import type",
                        expected: format!("{:?}", gt),
                        found: format!("{:?}", g.ty()),
                    });
                }
                globals.push(addr);
            }
        }
    }

    // 2) Define module functions
    for (def_index, type_idx) in module.func_type_indices.iter().cloned().enumerate() {
        let addr = store.alloc_func(FuncInstance::Wasm { type_idx, def_index, module: module_index });
        funcs.push(addr);
    }

    // 3) Define tables
    for tt in &module.tables {
        let addr = store.alloc_table(TableInstance::new(tt));
        tables.push(addr);
    }

    // 4) Define memories
    for mt in &module.memories {
        let addr = store.alloc_memory(MemoryInstance::new(mt));
        memories.push(addr);
    }

    // Helpers to eval const exprs (no borrowing of closures over pos).
    fn read_u8_at(body: &[u8], pos: &mut usize) -> Result<u8, LinkError> {
        body.get(*pos).copied().ok_or(LinkError::Unimplemented("expr EOF")).map(|b| { *pos += 1; b })
    }
    fn eval_const_expr(
        expr: &model::Expr,
        store: &runtime::Store,
        module_inst: &runtime::ModuleInstance,
    ) -> Result<model::Value, LinkError> {
        use crate::binary::{cursor::Cursor as BinCursor, leb128};
        let body = &expr.body;
        let mut pos = 0usize;
        let op = read_u8_at(body, &mut pos)?;
        match op {
            0x41 /* i32.const */ => {
                let mut c = BinCursor::new(&body[pos..]);
                let v = leb128::read_sleb_i32(&mut c).map_err(|_| LinkError::Unimplemented("bad sleb32 in i32.const"))?;
                pos += c.offset();
                if read_u8_at(body, &mut pos)? != 0x0B { return Err(LinkError::Unimplemented("expr missing end")); }
                Ok(model::Value::I32(v))
            }
            0x42 /* i64.const */ => {
                let mut c = BinCursor::new(&body[pos..]);
                let v = leb128::read_sleb_i64(&mut c).map_err(|_| LinkError::Unimplemented("bad sleb64 in i64.const"))?;
                pos += c.offset();
                if read_u8_at(body, &mut pos)? != 0x0B { return Err(LinkError::Unimplemented("expr missing end")); }
                Ok(model::Value::I64(v))
            }
            0x43 /* f32.const */ => {
                if pos + 4 > body.len() { return Err(LinkError::Unimplemented("expr EOF f32.const")); }
                let bits = u32::from_le_bytes([body[pos], body[pos + 1], body[pos + 2], body[pos + 3]]);
                pos += 4;
                if read_u8_at(body, &mut pos)? != 0x0B { return Err(LinkError::Unimplemented("expr missing end")); }
                Ok(model::Value::F32(bits))
            }
            0x44 /* f64.const */ => {
                if pos + 8 > body.len() { return Err(LinkError::Unimplemented("expr EOF f64.const")); }
                let bits = u64::from_le_bytes([
                    body[pos], body[pos + 1], body[pos + 2], body[pos + 3],
                    body[pos + 4], body[pos + 5], body[pos + 6], body[pos + 7],
                ]);
                pos += 8;
                if read_u8_at(body, &mut pos)? != 0x0B { return Err(LinkError::Unimplemented("expr missing end")); }
                Ok(model::Value::F64(bits))
            }
            0x23 /* global.get */ => {
                // Only imported immutable globals supported in init exprs (MVP subset here).
                let mut c = BinCursor::new(&body[pos..]);
                let idx = leb128::read_uleb_u32(&mut c).map_err(|_| LinkError::Unimplemented("bad uleb in global.get"))?;
                pos += c.offset();
                if read_u8_at(body, &mut pos)? != 0x0B { return Err(LinkError::Unimplemented("expr missing end")); }
                let gaddr = *module_inst.globals.get(idx as usize)
                    .ok_or(LinkError::Unimplemented("global.get index out of bounds in const expr"))?;
                let g = store.get_global(gaddr).ok_or(LinkError::Unimplemented("global addr invalid"))?;
                if g.ty().mutable {
                    return Err(LinkError::TypeMismatch {
                        context: "global.get in const expr requires immutable global",
                        expected: "immutable".into(),
                        found: "mutable".into(),
                    });
                }
                Ok(g.get())
            }
            _ => Err(LinkError::Unimplemented("unsupported opcode in const expr")),
        }
    }

    // Temporary instance view for const exprs and segment init
    let mut tmp_inst_for_init = runtime::ModuleInstance {
        funcs: funcs.clone(),
        tables: tables.clone(),
        memories: memories.clone(),
        globals: globals.clone(),
        exports: HashMap::new(),
        module_ir: module.clone(),
    };

    // 5) Define globals (evaluate init expressions)
    for glob in &module.globals {
        let init_val = eval_const_expr(&glob.init, store, &tmp_inst_for_init)?;
        let expected_ty = glob.ty.val_type;
        let ok = match (expected_ty, init_val) {
            (model::ValType::I32, model::Value::I32(_))
            | (model::ValType::I64, model::Value::I64(_))
            | (model::ValType::F32, model::Value::F32(_))
            | (model::ValType::F64, model::Value::F64(_)) => true,
            _ => false,
        };
        if !ok {
            return Err(LinkError::TypeMismatch {
                context: "global init expr",
                expected: format!("{:?}", expected_ty),
                found: format!("{:?}", init_val),
            });
        }
        let addr = store.alloc_global(GlobalInstance::new(glob.ty.clone(), init_val));
        globals.push(addr);
    }
    tmp_inst_for_init.globals = globals.clone();

    // 6) Initialize element segments (tables)
    for seg in &module.elements {
        let table_idx = seg.table as usize;
        let taddr = *tables.get(table_idx)
            .ok_or(LinkError::Unimplemented("element segment refers to missing table"))?;
        let offset_val = eval_const_expr(&seg.offset, store, &tmp_inst_for_init)?;
        let base = match offset_val {
            model::Value::I32(v) if v >= 0 => v as u32,
            _ => return Err(LinkError::ElemOutOfBounds),
        };
        let t_ro = store.get_table(taddr).ok_or(LinkError::Unimplemented("bad table addr"))?;
        let needed = base.saturating_add(seg.init.len() as u32);
        if needed > t_ro.size() {
            return Err(LinkError::ElemOutOfBounds);
        }
        drop(t_ro);
        let t = store.get_table_mut(taddr).ok_or(LinkError::Unimplemented("bad table addr"))?;
        for (i, funcidx) in seg.init.iter().enumerate() {
            let faddr = *funcs.get(*funcidx as usize)
                .ok_or(LinkError::Unimplemented("element refers to invalid funcidx"))?;
            t.set(base + (i as u32), Some(faddr)).map_err(|_| LinkError::ElemOutOfBounds)?;
        }
    }

    // 7) Initialize data segments (memories)
    for seg in &module.data {
        let mem_idx = seg.memory as usize;
        let maddr = *memories.get(mem_idx)
            .ok_or(LinkError::Unimplemented("data segment refers to missing memory"))?;
        let offset_val = eval_const_expr(&seg.offset, store, &tmp_inst_for_init)?;
        let base = match offset_val {
            model::Value::I32(v) if v >= 0 => v as usize,
            _ => return Err(LinkError::DataOutOfBounds),
        };
        let m = store.get_memory_mut(maddr).ok_or(LinkError::Unimplemented("bad memory addr"))?;
        let buf = m.data_mut();
        let end = base.saturating_add(seg.init.len());
        if end > buf.len() {
            return Err(LinkError::DataOutOfBounds);
        }
        buf[base..end].copy_from_slice(&seg.init);
    }

    // 8) Build exports map
    let mut exports_map: HashMap<String, RuntimeExportDesc> = HashMap::new();
    for ex in &module.exports {
        match ex.desc {
            ExportDesc::Func(fidx) => {
                let addr = *funcs
                    .get(fidx as usize)
                    .ok_or(LinkError::Unimplemented("export func index OOB"))?;
                exports_map.insert(ex.name.clone(), RuntimeExportDesc::Func(addr));
            }
            ExportDesc::Table(tidx) => {
                let addr = *tables
                    .get(tidx as usize)
                    .ok_or(LinkError::Unimplemented("export table index OOB"))?;
                exports_map.insert(ex.name.clone(), RuntimeExportDesc::Table(addr));
            }
            ExportDesc::Memory(midx) => {
                let addr = *memories
                    .get(midx as usize)
                    .ok_or(LinkError::Unimplemented("export memory index OOB"))?;
                exports_map.insert(ex.name.clone(), RuntimeExportDesc::Memory(addr));
            }
            ExportDesc::Global(gidx) => {
                let addr = *globals
                    .get(gidx as usize)
                    .ok_or(LinkError::Unimplemented("export global index OOB"))?;
                exports_map.insert(ex.name.clone(), RuntimeExportDesc::Global(addr));
            }
        }
    }

    // 9) Commit instance fields and start function if present
    {
        let module_inst = store
            .get_module_mut(module_index)
            .expect("module just allocated");
        module_inst.funcs = funcs;
        module_inst.tables = tables;
        module_inst.memories = memories;
        module_inst.globals = globals;
        module_inst.exports = exports_map;

        if let Some(start_idx) = module.start {
            let faddr = *module_inst
                .funcs
                .get(start_idx as usize)
                .ok_or(LinkError::Unimplemented("start func index OOB"))?;
            match crate::vm::interpreter::run_function(store, handle, faddr, &[]) {
                Ok(_ret) => {}
                Err(trap) => return Err(LinkError::StartTrap(trap)),
            }
        }
    }

    Ok(handle)
}

/// Invoke an exported function.
pub fn invoke_export(
    store: &mut runtime::Store,
    instance: runtime::InstanceHandle,
    export_name: &str,
    args: &[Value],
) -> Result<Option<Value>, error::Trap> {
    use crate::runtime::instances::RuntimeExportDesc;
    let module_inst = store
        .get_module(instance.0)
        .ok_or(error::Trap::Unimplemented("bad instance handle"))?;
    match module_inst.resolve_export(export_name) {
        Some(RuntimeExportDesc::Func(func_addr)) => {
            crate::vm::interpreter::run_function(store, instance, func_addr, args)
        }
        Some(RuntimeExportDesc::Table(_))
        | Some(RuntimeExportDesc::Memory(_))
        | Some(RuntimeExportDesc::Global(_)) => Err(error::Trap::Unimplemented(
            "non-function export invocation",
        )),
        None => Err(error::Trap::Unimplemented("export not found")),
    }
}
