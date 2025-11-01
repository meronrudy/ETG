//! MVP interpreter core with structured control flow (block/loop/if-else) and branches.
//! Implements a local seekable cursor and a lightweight scanner for matching else/end.

use crate::error::Trap;
use crate::model::Value;
use crate::runtime::{instances::FuncInstance, InstanceHandle, Store};
use crate::runtime::memory::MemoryInstance;
use crate::vm::frames::{BlockKind, ControlFrame};
use crate::vm::instructions::op;
use crate::vm::stack::ValueStack;

use crate::binary::{cursor::Cursor as BinCursor, leb128};

/// Local seekable cursor over bytecode.
struct SeekCursor {
    data: std::sync::Arc<[u8]>,
    pos: usize,
}
impl SeekCursor {
    fn new(data: &[u8]) -> Self { Self { data: std::sync::Arc::from(data), pos: 0 } }
    fn from_arc(data: std::sync::Arc<[u8]>) -> Self { Self { data, pos: 0 } }
    fn pos(&self) -> usize { self.pos }
    fn set_pos(&mut self, p: usize) -> Result<(), Trap> {
        if p > self.data.len() { return Err(Trap::Unimplemented("seek out of bounds")); }
        self.pos = p; Ok(())
    }
    fn is_eof(&self) -> bool { self.pos >= self.data.len() }
    fn read_u8(&mut self) -> Result<u8, Trap> {
        let b = *self.data.get(self.pos).ok_or(Trap::Unimplemented("unexpected EOF"))?;
        self.pos += 1; Ok(b)
    }
    fn read_bytes(&mut self, n: usize) -> Result<&[u8], Trap> {
        let end = self.pos.checked_add(n).ok_or(Trap::Unimplemented("position overflow"))?;
        if end > self.data.len() { return Err(Trap::Unimplemented("unexpected EOF")); }
        let s = &self.data[self.pos..end]; self.pos = end; Ok(s)
    }
    fn remaining(&self) -> usize { self.data.len().saturating_sub(self.pos) }
}

/// Helpers to read immediates from the seek cursor using the binary LEB128 readers.
fn read_uleb_u32_from(seek: &mut SeekCursor) -> Result<u32, Trap> {
    let mut c = BinCursor::new(&seek.data[seek.pos..]);
    let v = leb128::read_uleb_u32(&mut c).map_err(|_| Trap::Unimplemented("bad uleb32"))?;
    seek.pos += c.offset();
    Ok(v)
}
fn read_sleb_i32_from(seek: &mut SeekCursor) -> Result<i32, Trap> {
    let mut c = BinCursor::new(&seek.data[seek.pos..]);
    let v = leb128::read_sleb_i32(&mut c).map_err(|_| Trap::Unimplemented("bad sleb32"))?;
    seek.pos += c.offset();
    Ok(v)
}
fn read_sleb_i64_from(seek: &mut SeekCursor) -> Result<i64, Trap> {
    let mut c = BinCursor::new(&seek.data[seek.pos..]);
    let v = leb128::read_sleb_i64(&mut c).map_err(|_| Trap::Unimplemented("bad sleb64"))?;
    seek.pos += c.offset();
    Ok(v)
}
fn read_f32_bits_from(seek: &mut SeekCursor) -> Result<u32, Trap> {
    let b = seek.read_bytes(4)?; Ok(u32::from_le_bytes([b[0], b[1], b[2], b[3]]))
}
fn read_f64_bits_from(seek: &mut SeekCursor) -> Result<u64, Trap> {
    let b = seek.read_bytes(8)?; Ok(u64::from_le_bytes([b[0], b[1], b[2], b[3], b[4], b[5], b[6], b[7]]))
}

#[inline]
fn read_memarg(seek: &mut SeekCursor) -> Result<(u32, u32), Trap> {
    let align = read_uleb_u32_from(seek)?;
    let offset = read_uleb_u32_from(seek)?;
    Ok((align, offset))
}

/// Read and skip a blocktype immediate (MVP support).
fn skip_blocktype(seek: &mut SeekCursor) -> Result<(), Trap> {
    // Blocktype encodings: 0x40 (empty), valtype (0x7F..0x7C), or typeidx (uleb)
    let b = seek.read_u8()?;
    match b {
        0x40 | 0x7F | 0x7E | 0x7D | 0x7C => Ok(()),
        _other => {
            // Treat as first byte of uleb; step back one and read uleb fully.
            seek.pos -= 1;
            let _ = read_uleb_u32_from(seek)?; // typeidx (ignored)
            Ok(())
        }
    }
}

/// Skip immediates for a single instruction opcode for scanning purposes.
fn scan_skip_immediates(seek: &mut SeekCursor, opcode: u8) -> Result<(), Trap> {
    match opcode {
        // Control instructions with blocktype
        op::BLOCK | op::LOOP | op::IF => {
            skip_blocktype(seek)?;
        }
        op::ELSE | op::END | op::RETURN | op::UNREACHABLE | op::NOP => {
            // no immediates
        }
        // Parametric
        op::DROP | op::SELECT => {}
        // Consts
        op::I32_CONST => { let _ = read_sleb_i32_from(seek)?; }
        op::I64_CONST => { let _ = read_sleb_i64_from(seek)?; }
        op::F32_CONST => { let _ = read_f32_bits_from(seek)?; }
        op::F64_CONST => { let _ = read_f64_bits_from(seek)?; }
        // Br family
        op::BR | op::BR_IF => { let _ = read_uleb_u32_from(seek)?; }
        op::BR_TABLE => {
            let count = read_uleb_u32_from(seek)? as usize;
            for _ in 0..count { let _ = read_uleb_u32_from(seek)?; }
            let _default = read_uleb_u32_from(seek)?;
        }
        // Calls
        0x10 /* CALL */ => { let _ = read_uleb_u32_from(seek)?; }
        0x11 /* CALL_INDIRECT */ => { let _ = read_uleb_u32_from(seek)?; let _table = seek.read_u8()?; }
        // Locals/globals
        0x20..=0x24 => { let _ = read_uleb_u32_from(seek)?; }
        // Memory loads/stores (memarg: align + offset)
        0x28..=0x3E => {
            let _ = read_uleb_u32_from(seek)?; // align
            let _ = read_uleb_u32_from(seek)?; // offset
        }
        // Memory.size / memory.grow (reserved immediate byte)
        0x3F | 0x40 => { let _ = seek.read_u8()?; }
        // Everything else: assume no immediate for scanning; safe default.
        _ => {}
    }
    Ok(())
}

/// Scan forward from current position to find matching ELSE (if any) and END for a control construct.
/// Returns (else_pos_opt, end_pos) as absolute byte offsets just after the opcode bytes (ELSE/END).
fn scan_matching_else_end(seek: &mut SeekCursor, initial_kind: BlockKind) -> Result<(Option<usize>, usize), Trap> {
    let mut depth: usize = 1;
    // Track kinds to identify ELSE applicability at current top
    let mut kinds: Vec<BlockKind> = vec![initial_kind];
    let mut else_pos: Option<usize> = None;

    while !seek.is_eof() {
        let op = seek.read_u8()?;
        match op {
            op::BLOCK => { skip_blocktype(seek)?; kinds.push(BlockKind::Block); depth += 1; }
            op::LOOP  => { skip_blocktype(seek)?; kinds.push(BlockKind::Loop);  depth += 1; }
            op::IF    => { skip_blocktype(seek)?; kinds.push(BlockKind::If);    depth += 1; }
            op::ELSE => {
                if depth == 1 && kinds.last().copied() == Some(BlockKind::If) {
                    else_pos = Some(seek.pos());
                }
                // ELSE belongs to an IF; no depth change.
            }
            op::END => {
                // END matches current top
                let _ = kinds.pop();
                depth -= 1;
                if depth == 0 {
                    let end_pos = seek.pos();
                    return Ok((else_pos, end_pos));
                }
            }
            _ => {
                // Skip immediates for reliable scanning
                scan_skip_immediates(seek, op)?;
            }
        }
    }

    // If we got here, no matching end.
    Err(Trap::Unimplemented("scan: unmatched end"))
}

fn i32_bool(b: bool) -> Value { Value::I32(if b { 1 } else { 0 }) }

fn pop_i32(stack: &mut ValueStack) -> Result<i32, Trap> {
    match stack.pop()? { Value::I32(v) => Ok(v), _ => Err(Trap::Unimplemented("type mismatch: expected i32")) }
}
fn pop_i64(stack: &mut ValueStack) -> Result<i64, Trap> {
    match stack.pop()? { Value::I64(v) => Ok(v), _ => Err(Trap::Unimplemented("type mismatch: expected i64")) }
}
fn pop_f32_bits(stack: &mut ValueStack) -> Result<u32, Trap> {
    match stack.pop()? { Value::F32(b) => Ok(b), _ => Err(Trap::Unimplemented("type mismatch: expected f32")) }
}
fn pop_f64_bits(stack: &mut ValueStack) -> Result<u64, Trap> {
    match stack.pop()? { Value::F64(b) => Ok(b), _ => Err(Trap::Unimplemented("type mismatch: expected f64")) }
}

fn binop_i32<F>(stack: &mut ValueStack, f: F) -> Result<(), Trap> where F: Fn(i32, i32) -> Result<i32, Trap> {
    let rhs = pop_i32(stack)?; let lhs = pop_i32(stack)?; let r = f(lhs, rhs)?; stack.push(Value::I32(r)); Ok(())
}
fn binop_i64<F>(stack: &mut ValueStack, f: F) -> Result<(), Trap> where F: Fn(i64, i64) -> Result<i64, Trap> {
    let rhs = pop_i64(stack)?; let lhs = pop_i64(stack)?; let r = f(lhs, rhs)?; stack.push(Value::I64(r)); Ok(())
}
fn binop_f32<F>(stack: &mut ValueStack, f: F) -> Result<(), Trap> where F: Fn(f32, f32) -> f32 {
    let rhs_bits = pop_f32_bits(stack)?; let lhs_bits = pop_f32_bits(stack)?;
    let r = f(f32::from_bits(lhs_bits), f32::from_bits(rhs_bits)); stack.push(Value::F32(r.to_bits())); Ok(())
}
fn binop_f64<F>(stack: &mut ValueStack, f: F) -> Result<(), Trap> where F: Fn(f64, f64) -> f64 {
    let rhs_bits = pop_f64_bits(stack)?; let lhs_bits = pop_f64_bits(stack)?;
    let r = f(f64::from_bits(lhs_bits), f64::from_bits(rhs_bits)); stack.push(Value::F64(r.to_bits())); Ok(())
}

fn cmpop_i32<F>(stack: &mut ValueStack, f: F) -> Result<(), Trap> where F: Fn(i32, i32) -> bool {
    let rhs = pop_i32(stack)?; let lhs = pop_i32(stack)?; stack.push(i32_bool(f(lhs, rhs))); Ok(())
}
fn cmpop_i64<F>(stack: &mut ValueStack, f: F) -> Result<(), Trap> where F: Fn(i64, i64) -> bool {
    let rhs = pop_i64(stack)?; let lhs = pop_i64(stack)?; stack.push(i32_bool(f(lhs, rhs))); Ok(())
}
fn cmpop_u32<F>(stack: &mut ValueStack, f: F) -> Result<(), Trap> where F: Fn(u32, u32) -> bool {
    let rhs = pop_i32(stack)? as u32; let lhs = pop_i32(stack)? as u32; stack.push(i32_bool(f(lhs, rhs))); Ok(())
}
fn cmpop_u64<F>(stack: &mut ValueStack, f: F) -> Result<(), Trap> where F: Fn(u64, u64) -> bool {
    let rhs = pop_i64(stack)? as u64; let lhs = pop_i64(stack)? as u64; stack.push(i32_bool(f(lhs, rhs))); Ok(())
}
fn cmpop_f32<F>(stack: &mut ValueStack, f: F) -> Result<(), Trap> where F: Fn(f32, f32) -> bool {
    let rhs = f32::from_bits(pop_f32_bits(stack)?); let lhs = f32::from_bits(pop_f32_bits(stack)?);
    stack.push(i32_bool(f(lhs, rhs))); Ok(())
}
fn cmpop_f64<F>(stack: &mut ValueStack, f: F) -> Result<(), Trap> where F: Fn(f64, f64) -> bool {
    let rhs = f64::from_bits(pop_f64_bits(stack)?); let lhs = f64::from_bits(pop_f64_bits(stack)?);
    stack.push(i32_bool(f(lhs, rhs))); Ok(())
}

/// Internal executor for a single WASM-defined function (no host calls yet).
pub fn run_function(
    store: &mut Store,
    instance: InstanceHandle,
    func_addr: usize,
    args: &[Value],
) -> Result<Option<Value>, Trap> {
    // Instance handle currently unused in this executor path.
    let _ = instance;

    // Zero initialization helper for locals by ValType.
    #[inline]
    fn zero_for(t: &crate::model::ValType) -> Value {
        use crate::model::ValType::*;
        match t {
            I32 => Value::I32(0),
            I64 => Value::I64(0),
            F32 => Value::F32(0f32.to_bits()),
            F64 => Value::F64(0f64.to_bits()),
        }
    }

    // Per-function execution context.
    struct FuncCtx {
        cur: SeekCursor,
        ctrl: Vec<ControlFrame>,
        locals: Vec<Value>,
        module_index: usize,
        func_addr: usize,
        type_idx: u32, // TypeIdx alias
    }

    // Resolve initial function and prepare first context.
    let func = store.get_func(func_addr).cloned().ok_or(Trap::Unimplemented("bad func addr"))?;
    let (mut ctx0, mut stack): (FuncCtx, ValueStack) = match func {
        FuncInstance::Host { ty, f } => {
            if ty.params.len() != args.len() {
                return Err(Trap::Unimplemented("argument count mismatch"));
            }
            let ret = (f.as_ref())(args)?;
            return Ok(ret);
        }
        FuncInstance::Wasm { type_idx, def_index, module } => {
            let module_index = module;
            // Gather everything needed from the module in a tight scope to drop immutable borrows
            let (func_ty_params_len, code_bytes, code_len, locals_decl) = {
                let module_inst = store
                    .get_module(module_index)
                    .ok_or(Trap::Unimplemented("bad module index"))?;
                let code_body = module_inst
                    .code_body(def_index)
                    .ok_or(Trap::Unimplemented("code body not found"))?;
                let func_ty = module_inst
                    .func_type_by_typeidx(type_idx)
                    .ok_or(Trap::Unimplemented("func type not found"))?;
                // clone bytes into an owned Arc buffer so no borrow from the Store remains
                let code_bytes: std::sync::Arc<[u8]> = code_body.body.clone().into();
                let code_len = code_bytes.len();
                let locals_decl = code_body.locals.clone();
                (func_ty.params.len(), code_bytes, code_len, locals_decl)
            };

            // Initialize locals: params from args (declared order), then zero-initialized locals.
            if func_ty_params_len != args.len() {
                return Err(Trap::Unimplemented("argument count mismatch"));
            }
            let mut locals: Vec<Value> = Vec::with_capacity(
                func_ty_params_len
                    + locals_decl.iter().map(|d| d.count as usize).sum::<usize>(),
            );
            locals.extend_from_slice(args);
            for d in &locals_decl {
                for _ in 0..d.count {
                    locals.push(zero_for(&d.val_type));
                }
            }

            let mut ctrl: Vec<ControlFrame> = Vec::new();
            ctrl.push(ControlFrame::new(
                BlockKind::Function,
                0,
                Vec::new(),
                0,
                code_len,
                None,
            ));

            (
                FuncCtx {
                    cur: SeekCursor::from_arc(code_bytes),
                    ctrl,
                    locals,
                    module_index,
                    func_addr,
                    type_idx: type_idx,
                },
                ValueStack::new(),
            )
        }
    };

    // Function call stack (no Rust recursion).
    let mut call_stack: Vec<FuncCtx> = vec![ctx0];

    // Main interpreter loop
    loop {
        let ctx = call_stack
            .last_mut()
            .ok_or(Trap::Unimplemented("empty call stack"))?;
        let opcode = ctx
            .cur
            .read_u8()
            .map_err(|_| Trap::Unimplemented("unexpected EOF in code"))?;

        match opcode {
            // basic control
            op::UNREACHABLE => return Err(Trap::Unimplemented("unreachable executed")),
            op::NOP => {}

            // structured control
            op::BLOCK => {
                skip_blocktype(&mut ctx.cur)?;
                let start_of_block = ctx.cur.pos();
                let (_else_pos, end_pos) = scan_matching_else_end(
                    &mut SeekCursor {
                        data: ctx.cur.data.clone(),
                        pos: ctx.cur.pos,
                    },
                    BlockKind::Block,
                )?;
                ctx.ctrl.push(ControlFrame::new(
                    BlockKind::Block,
                    stack.len(),
                    Vec::new(),
                    start_of_block,
                    end_pos,
                    None,
                ));
            }
            op::LOOP => {
                skip_blocktype(&mut ctx.cur)?;
                let start_of_loop = ctx.cur.pos();
                let (_else_pos, end_pos) = scan_matching_else_end(
                    &mut SeekCursor {
                        data: ctx.cur.data.clone(),
                        pos: ctx.cur.pos,
                    },
                    BlockKind::Loop,
                )?;
                ctx.ctrl.push(ControlFrame::new(
                    BlockKind::Loop,
                    stack.len(),
                    Vec::new(),
                    start_of_loop,
                    end_pos,
                    None,
                ));
            }
            op::IF => {
                skip_blocktype(&mut ctx.cur)?;
                let cond = pop_i32(&mut stack)?;
                let start_then = ctx.cur.pos();
                let (else_pos, end_pos) = scan_matching_else_end(
                    &mut SeekCursor {
                        data: ctx.cur.data.clone(),
                        pos: ctx.cur.pos,
                    },
                    BlockKind::If,
                )?;
                ctx.ctrl.push(ControlFrame::new(
                    BlockKind::If,
                    stack.len(),
                    Vec::new(),
                    start_then,
                    end_pos,
                    else_pos,
                ));
                if cond == 0 {
                    if let Some(ep) = else_pos {
                        ctx.cur.set_pos(ep)?; // jump to else body
                    } else {
                        ctx.cur.set_pos(end_pos)?; // skip then entirely
                    }
                }
            }
            op::ELSE => {
                // Skip the else body by jumping to end of the IF frame
                if let Some(top) = ctx.ctrl.last() {
                    if top.kind != BlockKind::If {
                        return Err(Trap::Unimplemented("else without if"));
                    }
                    ctx.cur.set_pos(top.label_end)?;
                } else {
                    return Err(Trap::Unimplemented("control stack underflow at else"));
                }
            }
            op::END => {
                if let Some(frame) = ctx.ctrl.pop() {
                    stack.clear_to_height(frame.start_stack_height)?;
                    if frame.kind == BlockKind::Function {
                        // Return from current function
                        let module_inst = store
                            .get_module(ctx.module_index)
                            .ok_or(Trap::Unimplemented("bad module index"))?;
                        let fty = module_inst
                            .func_type_by_typeidx(ctx.type_idx)
                            .ok_or(Trap::Unimplemented("func type not found"))?;
                        let ret = if !fty.results.is_empty() {
                            Some(stack.pop()?)
                        } else {
                            None
                        };

                        // Pop callee context
                        call_stack.pop();
                        if call_stack.is_empty() {
                            return Ok(ret);
                        } else {
                            if let Some(v) = ret {
                                stack.push(v);
                            }
                            continue;
                        }
                    }
                    // For other blocks, continue execution after END.
                } else {
                    return Err(Trap::Unimplemented("control stack underflow at end"));
                }
            }

            // branches
            op::BR => {
                let depth = read_uleb_u32_from(&mut ctx.cur)? as usize;
                if depth >= ctx.ctrl.len() {
                    return Err(Trap::Unimplemented("br depth out of range"));
                }
                let target_index = ctx.ctrl.len() - 1 - depth;
                let target = ctx.ctrl[target_index].clone();
                match target.kind {
                    BlockKind::Loop => {
                        while ctx.ctrl.len() - 1 > target_index {
                            ctx.ctrl.pop();
                        }
                        stack.clear_to_height(target.start_stack_height)?;
                        ctx.cur.set_pos(target.label_start)?;
                    }
                    BlockKind::Block | BlockKind::If => {
                        while ctx.ctrl.len() > target_index {
                            ctx.ctrl.pop();
                        }
                        stack.clear_to_height(target.start_stack_height)?;
                        ctx.cur.set_pos(target.label_end)?;
                    }
                    BlockKind::Function => {
                        // Return from function
                        let module_inst = store
                            .get_module(ctx.module_index)
                            .ok_or(Trap::Unimplemented("bad module index"))?;
                        let fty = module_inst
                            .func_type_by_typeidx(ctx.type_idx)
                            .ok_or(Trap::Unimplemented("func type not found"))?;
                        let ret = if !fty.results.is_empty() {
                            Some(stack.pop()?)
                        } else {
                            None
                        };
                        call_stack.pop();
                        if call_stack.is_empty() {
                            return Ok(ret);
                        } else {
                            if let Some(v) = ret {
                                stack.push(v);
                            }
                            continue;
                        }
                    }
                }
            }
            op::BR_IF => {
                let depth = read_uleb_u32_from(&mut ctx.cur)? as usize;
                let cond = pop_i32(&mut stack)?;
                if cond != 0 {
                    if depth >= ctx.ctrl.len() {
                        return Err(Trap::Unimplemented("br_if depth out of range"));
                    }
                    let target_index = ctx.ctrl.len() - 1 - depth;
                    let target = ctx.ctrl[target_index].clone();
                    match target.kind {
                        BlockKind::Loop => {
                            while ctx.ctrl.len() - 1 > target_index {
                                ctx.ctrl.pop();
                            }
                            stack.clear_to_height(target.start_stack_height)?;
                            ctx.cur.set_pos(target.label_start)?;
                        }
                        BlockKind::Block | BlockKind::If => {
                            while ctx.ctrl.len() > target_index {
                                ctx.ctrl.pop();
                            }
                            stack.clear_to_height(target.start_stack_height)?;
                            ctx.cur.set_pos(target.label_end)?;
                        }
                        BlockKind::Function => {
                            let module_inst = store
                                .get_module(ctx.module_index)
                                .ok_or(Trap::Unimplemented("bad module index"))?;
                            let fty = module_inst
                                .func_type_by_typeidx(ctx.type_idx)
                                .ok_or(Trap::Unimplemented("func type not found"))?;
                            let ret = if !fty.results.is_empty() {
                                Some(stack.pop()?)
                            } else {
                                None
                            };
                            call_stack.pop();
                            if call_stack.is_empty() {
                                return Ok(ret);
                            } else {
                                if let Some(v) = ret {
                                    stack.push(v);
                                }
                                continue;
                            }
                        }
                    }
                }
            }
            op::BR_TABLE => {
                let count = read_uleb_u32_from(&mut ctx.cur)? as usize;
                let mut targets = Vec::with_capacity(count);
                for _ in 0..count {
                    targets.push(read_uleb_u32_from(&mut ctx.cur)? as usize);
                }
                let default = read_uleb_u32_from(&mut ctx.cur)? as usize;
                let idx = pop_i32(&mut stack)? as usize;
                let depth = *targets.get(idx).unwrap_or(&default);
                if depth >= ctx.ctrl.len() {
                    return Err(Trap::Unimplemented("br_table depth out of range"));
                }
                let target_index = ctx.ctrl.len() - 1 - depth;
                let target = ctx.ctrl[target_index].clone();
                match target.kind {
                    BlockKind::Loop => {
                        while ctx.ctrl.len() - 1 > target_index {
                            ctx.ctrl.pop();
                        }
                        stack.clear_to_height(target.start_stack_height)?;
                        ctx.cur.set_pos(target.label_start)?;
                    }
                    BlockKind::Block | BlockKind::If => {
                        while ctx.ctrl.len() > target_index {
                            ctx.ctrl.pop();
                        }
                        stack.clear_to_height(target.start_stack_height)?;
                        ctx.cur.set_pos(target.label_end)?;
                    }
                    BlockKind::Function => {
                        let module_inst = store
                            .get_module(ctx.module_index)
                            .ok_or(Trap::Unimplemented("bad module index"))?;
                        let fty = module_inst
                            .func_type_by_typeidx(ctx.type_idx)
                            .ok_or(Trap::Unimplemented("func type not found"))?;
                        let ret = if !fty.results.is_empty() {
                            Some(stack.pop()?)
                        } else {
                            None
                        };
                        call_stack.pop();
                        if call_stack.is_empty() {
                            return Ok(ret);
                        } else {
                            if let Some(v) = ret {
                                stack.push(v);
                            }
                            continue;
                        }
                    }
                }
            }

            // return
            op::RETURN => {
                let module_inst = store
                    .get_module(ctx.module_index)
                    .ok_or(Trap::Unimplemented("bad module index"))?;
                let fty = module_inst
                    .func_type_by_typeidx(ctx.type_idx)
                    .ok_or(Trap::Unimplemented("func type not found"))?;
                let ret = if !fty.results.is_empty() {
                    Some(stack.pop()?)
                } else {
                    None
                };
                call_stack.pop();
                if call_stack.is_empty() {
                    return Ok(ret);
                } else {
                    if let Some(v) = ret {
                        stack.push(v);
                    }
                    continue;
                }
            }

            // Parametric
            op::DROP => {
                let _ = stack.pop()?;
            }
            op::SELECT => {
                let cond = pop_i32(&mut stack)?;
                let v2 = stack.pop()?; // val2
                let v1 = stack.pop()?; // val1
                let same_type =
                    core::mem::discriminant(&v1) == core::mem::discriminant(&v2);
                if !same_type {
                    return Err(Trap::Unimplemented("select operand type mismatch"));
                }
                stack.push(if cond != 0 { v1 } else { v2 });
            }

            // Locals
            op::GET_LOCAL => {
                let idx = read_uleb_u32_from(&mut ctx.cur)? as usize;
                let v = ctx
                    .locals
                    .get(idx)
                    .cloned()
                    .ok_or(Trap::Unimplemented("get_local OOB"))?;
                stack.push(v);
            }
            op::SET_LOCAL => {
                let idx = read_uleb_u32_from(&mut ctx.cur)? as usize;
                let v = stack.pop()?;
                let slot = ctx
                    .locals
                    .get_mut(idx)
                    .ok_or(Trap::Unimplemented("set_local OOB"))?;
                *slot = v;
            }
            op::TEE_LOCAL => {
                let idx = read_uleb_u32_from(&mut ctx.cur)? as usize;
                let v = stack.pop()?;
                let slot = ctx
                    .locals
                    .get_mut(idx)
                    .ok_or(Trap::Unimplemented("tee_local OOB"))?;
                *slot = v.clone();
                stack.push(v);
            }

            // Globals
            op::GET_GLOBAL => {
                let idx = read_uleb_u32_from(&mut ctx.cur)? as usize;
                let gaddr = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .globals
                        .get(idx)
                        .ok_or(Trap::Unimplemented("get_global OOB"))?
                };
                let g = store
                    .get_global(gaddr)
                    .ok_or(Trap::Unimplemented("bad global index"))?;
                stack.push(g.get());
            }
            op::SET_GLOBAL => {
                let idx = read_uleb_u32_from(&mut ctx.cur)? as usize;
                let v = stack.pop()?;
                // Get global address in a scoped immutable borrow, then mutate separately
                let gaddr = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .globals
                        .get(idx)
                        .ok_or(Trap::Unimplemented("set_global OOB"))?
                };
                let g = store
                    .get_global_mut(gaddr)
                    .ok_or(Trap::Unimplemented("bad global index"))?;
                if g.set(v).is_err() {
                    return Err(Trap::Unimplemented("global is immutable"));
                }
            }

            // Memory loads
            op::I32_LOAD => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                let v = m.load_u32(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I32(v as i32));
            }
            op::I64_LOAD => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                let v = m.load_u64(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I64(v as i64));
            }
            op::F32_LOAD => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                let bits = m.load_u32(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::F32(bits));
            }
            op::F64_LOAD => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                let bits = m.load_u64(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::F64(bits));
            }
            op::I32_LOAD8_S => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                let v = m.load_u8(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I32((v as i8) as i32));
            }
            op::I32_LOAD8_U => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                let v = m.load_u8(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I32((v as u32) as i32));
            }
            op::I32_LOAD16_S => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                let v = m.load_u16(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I32((v as i16) as i32));
            }
            op::I32_LOAD16_U => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                let v = m.load_u16(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I32((v as u32) as i32));
            }
            op::I64_LOAD8_S => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                let v = m.load_u8(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I64((v as i8) as i64));
            }
            op::I64_LOAD8_U => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                let v = m.load_u8(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I64((v as u64) as i64));
            }
            op::I64_LOAD16_S => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                let v = m.load_u16(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I64((v as i16) as i64));
            }
            op::I64_LOAD16_U => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                let v = m.load_u16(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I64((v as u64) as i64));
            }
            op::I64_LOAD32_S => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                let v = m.load_u32(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I64((v as i32) as i64));
            }
            op::I64_LOAD32_U => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                let v = m.load_u32(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I64((v as u64) as i64));
            }

            // Memory stores
            op::I32_STORE => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let v = pop_i32(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                m.store_u32(ea, v as u32).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }
            op::I64_STORE => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let v = pop_i64(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                m.store_u64(ea, v as u64).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }
            op::F32_STORE => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let bits = pop_f32_bits(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                m.store_u32(ea, bits).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }
            op::F64_STORE => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let bits = pop_f64_bits(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                m.store_u64(ea, bits).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }
            op::I32_STORE8 => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let v = pop_i32(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let byte = ((v as u32) & 0xFF) as u8;
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                m.store_u8(ea, byte).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }
            op::I32_STORE16 => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let v = pop_i32(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let half = ((v as u32) & 0xFFFF) as u16;
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                m.store_u16(ea, half).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }
            op::I64_STORE8 => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let v = pop_i64(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let byte = ((v as u64) & 0xFF) as u8;
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                m.store_u8(ea, byte).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }
            op::I64_STORE16 => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let v = pop_i64(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let half = ((v as u64) & 0xFFFF) as u16;
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                m.store_u16(ea, half).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }
            op::I64_STORE32 => {
                let (_align, offset) = read_memarg(&mut ctx.cur)?;
                let v = pop_i64(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let word = ((v as u64) & 0xFFFF_FFFF) as u32;
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                m.store_u32(ea, word).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }

            // Memory queries
            op::MEMORY_SIZE => {
                let _reserved = ctx.cur.read_u8()?; // 0x00
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                stack.push(Value::I32(m.size_pages() as i32));
            }
            op::MEMORY_GROW => {
                let _reserved = ctx.cur.read_u8()?; // 0x00
                let delta_pages = pop_i32(&mut stack)?;
                let mem_idx = {
                    let module_inst = store
                        .get_module(ctx.module_index)
                        .ok_or(Trap::Unimplemented("bad module index"))?;
                    *module_inst
                        .memories
                        .get(0)
                        .ok_or(Trap::Unimplemented("memory op requires memory context"))?
                };
                let m = store
                    .get_memory_mut(mem_idx)
                    .ok_or(Trap::Unimplemented("bad memory index"))?;
                let prev = m.size_pages() as i32;
                if m.grow(delta_pages as u32).is_some() {
                    stack.push(Value::I32(prev));
                } else {
                    stack.push(Value::I32(-1));
                }
            }

            // Calls
            op::CALL => {
                let funcidx = read_uleb_u32_from(&mut ctx.cur)? as usize;
                let module_inst = store
                    .get_module(ctx.module_index)
                    .ok_or(Trap::Unimplemented("bad module index"))?;
                let callee_addr = *module_inst
                    .funcs
                    .get(funcidx)
                    .ok_or(Trap::Unimplemented("call funcidx OOB"))?;
                let callee = store
                    .get_func(callee_addr)
                    .ok_or(Trap::Unimplemented("bad callee addr"))?;
                match callee {
                    FuncInstance::Host { ty, f } => {
                        let nparams = ty.params.len();
                        let mut call_args: Vec<Value> = Vec::with_capacity(nparams);
                        for _ in 0..nparams {
                            call_args.push(stack.pop()?);
                        }
                        call_args.reverse();
                        let ret = (f.as_ref())(&call_args)?;
                        if let Some(v) = ret {
                            stack.push(v);
                        }
                    }
                    FuncInstance::Wasm {
                        type_idx: callee_tidx,
                        def_index: callee_def,
                        module: callee_mod,
                    } => {
                        let callee_module_index = *callee_mod;
                        let callee_module_inst = store
                            .get_module(callee_module_index)
                            .ok_or(Trap::Unimplemented("bad callee module"))?;
                        let callee_ty = callee_module_inst
                            .func_type_by_typeidx(*callee_tidx)
                            .ok_or(Trap::Unimplemented("callee type not found"))?;
                        let nparams = callee_ty.params.len();
                        let mut call_args: Vec<Value> = Vec::with_capacity(nparams);
                        for _ in 0..nparams {
                            call_args.push(stack.pop()?);
                        }
                        call_args.reverse();

                        let callee_code = callee_module_inst
                            .code_body(*callee_def)
                            .ok_or(Trap::Unimplemented("callee code not found"))?;

                        let mut locals = call_args;
                        for d in &callee_code.locals {
                            for _ in 0..d.count {
                                locals.push(zero_for(&d.val_type));
                            }
                        }

                        let mut callee_ctrl: Vec<ControlFrame> = Vec::new();
                        callee_ctrl.push(ControlFrame::new(
                            BlockKind::Function,
                            stack.len(),
                            Vec::new(),
                            0,
                            callee_code.body.len(),
                            None,
                        ));

                        // Push new context
                        call_stack.push(FuncCtx {
                            cur: SeekCursor::new(&callee_code.body),
                            ctrl: callee_ctrl,
                            locals,
                            module_index: callee_module_index,
                            func_addr: callee_addr,
                            type_idx: *callee_tidx,
                        });
                    }
                }
            }
            op::CALL_INDIRECT => {
                let type_idx_imm = read_uleb_u32_from(&mut ctx.cur)? as u32;
                let _table = ctx.cur.read_u8()?; // MVP reserved (0x00)
                let table_index_val = pop_i32(&mut stack)? as u32;

                let module_inst = store
                    .get_module(ctx.module_index)
                    .ok_or(Trap::Unimplemented("bad module index"))?;
                let table0 = *module_inst
                    .tables
                    .get(0)
                    .ok_or(Trap::Unimplemented("call_indirect: table 0 missing"))?;
                let table_inst = store
                    .get_table(table0)
                    .ok_or(Trap::Unimplemented("bad table index"))?;
                let elem = table_inst
                    .get(table_index_val)
                    .ok_or(Trap::Unimplemented(
                        "call_indirect: table index out of bounds",
                    ))?;
                let callee_addr = elem.ok_or(Trap::Unimplemented(
                    "call_indirect: uninitialized table element",
                ))?;
                let callee = store
                    .get_func(callee_addr)
                    .ok_or(Trap::Unimplemented("bad callee addr"))?;
                match callee {
                    FuncInstance::Host { ty, f } => {
                        // Type-check host function against table's expected type
                        let expected = module_inst
                            .func_type_by_typeidx(type_idx_imm)
                            .ok_or(Trap::Unimplemented("callee type not found"))?
                            .clone();
                        if *ty != expected {
                            return Err(Trap::Unimplemented("call_indirect: type mismatch"));
                        }
                        let nparams = ty.params.len();
                        let mut call_args: Vec<Value> = Vec::with_capacity(nparams);
                        for _ in 0..nparams {
                            call_args.push(stack.pop()?);
                        }
                        call_args.reverse();
                        let ret = (f.as_ref())(&call_args)?;
                        if let Some(v) = ret {
                            stack.push(v);
                        }
                    }
                    FuncInstance::Wasm {
                        type_idx: callee_tidx,
                        def_index: callee_def,
                        module: callee_mod,
                    } => {
                        if *callee_tidx != type_idx_imm {
                            return Err(Trap::Unimplemented(
                                "call_indirect: type mismatch",
                            ));
                        }
                        let callee_module_index = *callee_mod;
                        let callee_module_inst = store
                            .get_module(callee_module_index)
                            .ok_or(Trap::Unimplemented("bad callee module"))?;
                        let callee_ty = callee_module_inst
                            .func_type_by_typeidx(*callee_tidx)
                            .ok_or(Trap::Unimplemented("callee type not found"))?;
                        let nparams = callee_ty.params.len();
                        let mut call_args: Vec<Value> = Vec::with_capacity(nparams);
                        for _ in 0..nparams {
                            call_args.push(stack.pop()?);
                        }
                        call_args.reverse();

                        let callee_code = callee_module_inst
                            .code_body(*callee_def)
                            .ok_or(Trap::Unimplemented("callee code not found"))?;

                        let mut locals = call_args;
                        for d in &callee_code.locals {
                            for _ in 0..d.count {
                                locals.push(zero_for(&d.val_type));
                            }
                        }

                        let mut callee_ctrl: Vec<ControlFrame> = Vec::new();
                        callee_ctrl.push(ControlFrame::new(
                            BlockKind::Function,
                            stack.len(),
                            Vec::new(),
                            0,
                            callee_code.body.len(),
                            None,
                        ));

                        call_stack.push(FuncCtx {
                            cur: SeekCursor::new(&callee_code.body),
                            ctrl: callee_ctrl,
                            locals,
                            module_index: callee_module_index,
                            func_addr: callee_addr,
                            type_idx: *callee_tidx,
                        });
                    }
                }
            }

            // Consts
            op::I32_CONST => {
                let v = read_sleb_i32_from(&mut ctx.cur)?;
                stack.push(Value::I32(v));
            }
            op::I64_CONST => {
                let v = read_sleb_i64_from(&mut ctx.cur)?;
                stack.push(Value::I64(v));
            }
            op::F32_CONST => {
                let bits = read_f32_bits_from(&mut ctx.cur)?;
                stack.push(Value::F32(bits));
            }
            op::F64_CONST => {
                let bits = read_f64_bits_from(&mut ctx.cur)?;
                stack.push(Value::F64(bits));
            }

            // Integer comparisons
            0x46 /* I32_EQ */ => cmpop_i32(&mut stack, |a, b| a == b)?,
            0x48 /* I32_LT_S */ => cmpop_i32(&mut stack, |a, b| a < b)?,
            0x49 /* I32_LT_U */ => cmpop_u32(&mut stack, |a, b| a < b)?,
            0x51 /* I64_EQ */ => cmpop_i64(&mut stack, |a, b| a == b)?,
            0x53 /* I64_LT_S */ => cmpop_i64(&mut stack, |a, b| a < b)?,
            0x54 /* I64_LT_U */ => cmpop_u64(&mut stack, |a, b| a < b)?,

            // Float comparisons
            0x5B /* F32_EQ */ => cmpop_f32(&mut stack, |a, b| a == b)?,
            0x5D /* F32_LT */ => cmpop_f32(&mut stack, |a, b| a < b)?,
            0x61 /* F64_EQ */ => cmpop_f64(&mut stack, |a, b| a == b)?,
            0x63 /* F64_LT */ => cmpop_f64(&mut stack, |a, b| a < b)?,

            // Integer arithmetic
            0x6A /* I32_ADD */ => binop_i32(&mut stack, |a, b| Ok(a.wrapping_add(b)))?,
            0x6B /* I32_SUB */ => binop_i32(&mut stack, |a, b| Ok(a.wrapping_sub(b)))?,
            0x6C /* I32_MUL */ => binop_i32(&mut stack, |a, b| Ok(a.wrapping_mul(b)))?,
            0x6D /* I32_DIV_S */ => binop_i32(&mut stack, |a, b| {
                if b == 0 {
                    return Err(Trap::Unimplemented("i32.div_s divide by zero"));
                }
                if a == i32::MIN && b == -1 {
                    return Err(Trap::Unimplemented("i32.div_s overflow"));
                }
                Ok(a / b)
            })?,
            0x6E /* I32_DIV_U */ => {
                let b = pop_i32(&mut stack)? as u32;
                let a = pop_i32(&mut stack)? as u32;
                if b == 0 {
                    return Err(Trap::Unimplemented("i32.div_u divide by zero"));
                }
                stack.push(Value::I32((a / b) as i32));
            }

            0x7C /* I64_ADD */ => binop_i64(&mut stack, |a, b| Ok(a.wrapping_add(b)))?,
            0x7D /* I64_SUB */ => binop_i64(&mut stack, |a, b| Ok(a.wrapping_sub(b)))?,
            0x7E /* I64_MUL */ => binop_i64(&mut stack, |a, b| Ok(a.wrapping_mul(b)))?,
            0x7F /* I64_DIV_S */ => binop_i64(&mut stack, |a, b| {
                if b == 0 {
                    return Err(Trap::Unimplemented("i64.div_s divide by zero"));
                }
                if a == i64::MIN && b == -1 {
                    return Err(Trap::Unimplemented("i64.div_s overflow"));
                }
                Ok(a / b)
            })?,
            0x80 /* I64_DIV_U */ => {
                let b = pop_i64(&mut stack)? as u64;
                let a = pop_i64(&mut stack)? as u64;
                if b == 0 {
                    return Err(Trap::Unimplemented("i64.div_u divide by zero"));
                }
                stack.push(Value::I64((a / b) as i64));
            }

            // Float arithmetic
            0x92 /* F32_ADD */ => binop_f32(&mut stack, |a, b| a + b)?,
            0x93 /* F32_SUB */ => binop_f32(&mut stack, |a, b| a - b)?,
            0x94 /* F32_MUL */ => binop_f32(&mut stack, |a, b| a * b)?,
            0x95 /* F32_DIV */ => binop_f32(&mut stack, |a, b| a / b)?,

            0xA0 /* F64_ADD */ => binop_f64(&mut stack, |a, b| a + b)?,
            0xA1 /* F64_SUB */ => binop_f64(&mut stack, |a, b| a - b)?,
            0xA2 /* F64_MUL */ => binop_f64(&mut stack, |a, b| a * b)?,
            0xA3 /* F64_DIV */ => binop_f64(&mut stack, |a, b| a / b)?,

            _ => {
                return Err(Trap::Unimplemented("opcode not implemented"));
            }
        }
    }
}

fn run_with_ctx(code: &[u8], mut mem: Option<&mut MemoryInstance>) -> Result<Option<Value>, Trap> {
    let mut cur = SeekCursor::new(code);
    let mut stack = ValueStack::new();
    let mut ctrl: Vec<ControlFrame> = Vec::new();

    // Enter function block
    ctrl.push(ControlFrame::new(BlockKind::Function, 0, Vec::new(), 0, code.len(), None));

    loop {
        let opcode = cur.read_u8().map_err(|_| Trap::Unimplemented("unexpected EOF in code"))?;
        match opcode {
            // basic control
            op::UNREACHABLE => return Err(Trap::Unimplemented("unreachable executed")),
            op::NOP => {}

            // structured control
            op::BLOCK => {
                skip_blocktype(&mut cur)?;
                let start_of_block = cur.pos();
                let (_else_pos, end_pos) = scan_matching_else_end(&mut SeekCursor { data: cur.data.clone(), pos: cur.pos }, BlockKind::Block)?;
                ctrl.push(ControlFrame::new(BlockKind::Block, stack.len(), Vec::new(), start_of_block, end_pos, None));
            }
            op::LOOP => {
                skip_blocktype(&mut cur)?;
                let start_of_loop = cur.pos();
                let (_else_pos, end_pos) = scan_matching_else_end(&mut SeekCursor { data: cur.data.clone(), pos: cur.pos }, BlockKind::Loop)?;
                ctrl.push(ControlFrame::new(BlockKind::Loop, stack.len(), Vec::new(), start_of_loop, end_pos, None));
            }
            op::IF => {
                skip_blocktype(&mut cur)?;
                let cond = pop_i32(&mut stack)?;
                let start_then = cur.pos();
                let (else_pos, end_pos) = scan_matching_else_end(&mut SeekCursor { data: cur.data.clone(), pos: cur.pos }, BlockKind::If)?;
                ctrl.push(ControlFrame::new(BlockKind::If, stack.len(), Vec::new(), start_then, end_pos, else_pos));
                if cond == 0 {
                    if let Some(ep) = else_pos {
                        cur.set_pos(ep)?; // jump to else body
                    } else {
                        cur.set_pos(end_pos)?; // skip then entirely
                    }
                }
            }
            op::ELSE => {
                if let Some(top) = ctrl.last() {
                    if top.kind != BlockKind::If { return Err(Trap::Unimplemented("else without if")); }
                    cur.set_pos(top.label_end)?;
                } else {
                    return Err(Trap::Unimplemented("control stack underflow at else"));
                }
            }
            op::END => {
                if let Some(frame) = ctrl.pop() {
                    stack.clear_to_height(frame.start_stack_height)?;
                    if frame.kind == BlockKind::Function {
                        let ret = if stack.len() > 0 { Some(stack.pop()?) } else { None };
                        return Ok(ret);
                    }
                } else {
                    return Err(Trap::Unimplemented("control stack underflow at end"));
                }
            }

            // branches
            op::BR => {
                let depth = read_uleb_u32_from(&mut cur)? as usize;
                if depth >= ctrl.len() { return Err(Trap::Unimplemented("br depth out of range")); }
                let target_index = ctrl.len() - 1 - depth;
                let target = ctrl[target_index].clone();
                match target.kind {
                    BlockKind::Loop => {
                        while ctrl.len() - 1 > target_index { ctrl.pop(); }
                        stack.clear_to_height(target.start_stack_height)?;
                        cur.set_pos(target.label_start)?;
                    }
                    BlockKind::Block | BlockKind::If => {
                        while ctrl.len() > target_index { ctrl.pop(); }
                        stack.clear_to_height(target.start_stack_height)?;
                        cur.set_pos(target.label_end)?;
                    }
                    BlockKind::Function => {
                        while let Some(frame) = ctrl.pop() {
                            if frame.kind == BlockKind::Function {
                                let ret = if stack.len() > 0 { Some(stack.pop()?) } else { None };
                                return Ok(ret);
                            }
                        }
                        return Err(Trap::Unimplemented("br to function without function frame"));
                    }
                }
            }
            op::BR_IF => {
                let depth = read_uleb_u32_from(&mut cur)? as usize;
                let cond = pop_i32(&mut stack)?;
                if cond != 0 {
                    if depth >= ctrl.len() { return Err(Trap::Unimplemented("br_if depth out of range")); }
                    let target_index = ctrl.len() - 1 - depth;
                    let target = ctrl[target_index].clone();
                    match target.kind {
                        BlockKind::Loop => {
                            while ctrl.len() - 1 > target_index { ctrl.pop(); }
                            stack.clear_to_height(target.start_stack_height)?;
                            cur.set_pos(target.label_start)?;
                        }
                        BlockKind::Block | BlockKind::If => {
                            while ctrl.len() > target_index { ctrl.pop(); }
                            stack.clear_to_height(target.start_stack_height)?;
                            cur.set_pos(target.label_end)?;
                        }
                        BlockKind::Function => {
                            while let Some(frame) = ctrl.pop() {
                                if frame.kind == BlockKind::Function {
                                    let ret = if stack.len() > 0 { Some(stack.pop()?) } else { None };
                                    return Ok(ret);
                                }
                            }
                            return Err(Trap::Unimplemented("br_if to function without function frame"));
                        }
                    }
                }
            }
            op::BR_TABLE => {
                let count = read_uleb_u32_from(&mut cur)? as usize;
                let mut targets = Vec::with_capacity(count);
                for _ in 0..count { targets.push(read_uleb_u32_from(&mut cur)? as usize); }
                let default = read_uleb_u32_from(&mut cur)? as usize;
                let idx = pop_i32(&mut stack)? as usize;
                let depth = *targets.get(idx).unwrap_or(&default);
                if depth >= ctrl.len() { return Err(Trap::Unimplemented("br_table depth out of range")); }
                let target_index = ctrl.len() - 1 - depth;
                let target = ctrl[target_index].clone();
                match target.kind {
                    BlockKind::Loop => {
                        while ctrl.len() - 1 > target_index { ctrl.pop(); }
                        stack.clear_to_height(target.start_stack_height)?;
                        cur.set_pos(target.label_start)?;
                    }
                    BlockKind::Block | BlockKind::If => {
                        while ctrl.len() > target_index { ctrl.pop(); }
                        stack.clear_to_height(target.start_stack_height)?;
                        cur.set_pos(target.label_end)?;
                    }
                    BlockKind::Function => {
                        while let Some(frame) = ctrl.pop() {
                            if frame.kind == BlockKind::Function {
                                let ret = if stack.len() > 0 { Some(stack.pop()?) } else { None };
                                return Ok(ret);
                            }
                        }
                        return Err(Trap::Unimplemented("br_table to function without function frame"));
                    }
                }
            }

            // return
            op::RETURN => {
                while let Some(frame) = ctrl.pop() {
                    if frame.kind == BlockKind::Function {
                        let ret = if stack.len() > 0 { Some(stack.pop()?) } else { None };
                        return Ok(ret);
                    }
                }
                return Err(Trap::Unimplemented("return without function frame"));
            }

            // Parametric
            op::DROP => { let _ = stack.pop()?; }
            op::SELECT => {
                let cond = pop_i32(&mut stack)?;
                let v2 = stack.pop()?; // val2
                let v1 = stack.pop()?; // val1
                let same_type = core::mem::discriminant(&v1) == core::mem::discriminant(&v2);
                if !same_type { return Err(Trap::Unimplemented("select operand type mismatch")); }
                stack.push(if cond != 0 { v1 } else { v2 });
            }

            // Memory loads
            op::I32_LOAD => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                let v = m.load_u32(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I32(v as i32));
            }
            op::I64_LOAD => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                let v = m.load_u64(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I64(v as i64));
            }
            op::F32_LOAD => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                let bits = m.load_u32(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::F32(bits));
            }
            op::F64_LOAD => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                let bits = m.load_u64(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::F64(bits));
            }
            op::I32_LOAD8_S => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                let v = m.load_u8(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I32((v as i8) as i32));
            }
            op::I32_LOAD8_U => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                let v = m.load_u8(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I32((v as u32) as i32));
            }
            op::I32_LOAD16_S => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                let v = m.load_u16(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I32((v as i16) as i32));
            }
            op::I32_LOAD16_U => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                let v = m.load_u16(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I32((v as u32) as i32));
            }
            op::I64_LOAD8_S => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                let v = m.load_u8(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I64((v as i8) as i64));
            }
            op::I64_LOAD8_U => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                let v = m.load_u8(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I64((v as u64) as i64));
            }
            op::I64_LOAD16_S => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                let v = m.load_u16(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I64((v as i16) as i64));
            }
            op::I64_LOAD16_U => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                let v = m.load_u16(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I64((v as u64) as i64));
            }
            op::I64_LOAD32_S => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                let v = m.load_u32(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I64((v as i32) as i64));
            }
            op::I64_LOAD32_U => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                let v = m.load_u32(ea).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
                stack.push(Value::I64((v as u64) as i64));
            }

            // Memory stores
            op::I32_STORE => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let v = pop_i32(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                m.store_u32(ea, v as u32).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }
            op::I64_STORE => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let v = pop_i64(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                m.store_u64(ea, v as u64).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }
            op::F32_STORE => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let bits = pop_f32_bits(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                m.store_u32(ea, bits).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }
            op::F64_STORE => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let bits = pop_f64_bits(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                m.store_u64(ea, bits).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }
            op::I32_STORE8 => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let v = pop_i32(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let byte = ((v as u32) & 0xFF) as u8;
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                m.store_u8(ea, byte).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }
            op::I32_STORE16 => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let v = pop_i32(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let half = ((v as u32) & 0xFFFF) as u16;
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                m.store_u16(ea, half).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }
            op::I64_STORE8 => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let v = pop_i64(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let byte = ((v as u64) & 0xFF) as u8;
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                m.store_u8(ea, byte).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }
            op::I64_STORE16 => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let v = pop_i64(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let half = ((v as u64) & 0xFFFF) as u16;
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                m.store_u16(ea, half).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }
            op::I64_STORE32 => {
                let (_align, offset) = read_memarg(&mut cur)?;
                let v = pop_i64(&mut stack)?;
                let addr = pop_i32(&mut stack)?;
                let ea = (addr as u32).wrapping_add(offset);
                let word = ((v as u64) & 0xFFFF_FFFF) as u32;
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                m.store_u32(ea, word).map_err(|_| Trap::Unimplemented("memory out of bounds"))?;
            }

            // Memory queries
            op::MEMORY_SIZE => {
                let _reserved = cur.read_u8()?; // 0x00
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                stack.push(Value::I32(m.size_pages() as i32));
            }
            op::MEMORY_GROW => {
                let _reserved = cur.read_u8()?; // 0x00
                let delta_pages = pop_i32(&mut stack)?;
                let m = mem.as_deref_mut().ok_or(Trap::Unimplemented("memory op requires memory context"))?;
                let prev = m.size_pages() as i32;
                if m.grow(delta_pages as u32).is_some() {
                    stack.push(Value::I32(prev));
                } else {
                    stack.push(Value::I32(-1));
                }
            }

            // Consts
            op::I32_CONST => { let v = read_sleb_i32_from(&mut cur)?; stack.push(Value::I32(v)); }
            op::I64_CONST => { let v = read_sleb_i64_from(&mut cur)?; stack.push(Value::I64(v)); }
            op::F32_CONST => { let bits = read_f32_bits_from(&mut cur)?; stack.push(Value::F32(bits)); }
            op::F64_CONST => { let bits = read_f64_bits_from(&mut cur)?; stack.push(Value::F64(bits)); }

            // Integer comparisons
            0x46 /* I32_EQ */ => cmpop_i32(&mut stack, |a,b| a == b)?,
            0x48 /* I32_LT_S */ => cmpop_i32(&mut stack, |a,b| a < b)?,
            0x49 /* I32_LT_U */ => cmpop_u32(&mut stack, |a,b| a < b)?,
            0x51 /* I64_EQ */ => cmpop_i64(&mut stack, |a,b| a == b)?,
            0x53 /* I64_LT_S */ => cmpop_i64(&mut stack, |a,b| a < b)?,
            0x54 /* I64_LT_U */ => cmpop_u64(&mut stack, |a,b| a < b)?,

            // Float comparisons
            0x5B /* F32_EQ */ => cmpop_f32(&mut stack, |a,b| a == b)?,
            0x5D /* F32_LT */ => cmpop_f32(&mut stack, |a,b| a < b)?,
            0x61 /* F64_EQ */ => cmpop_f64(&mut stack, |a,b| a == b)?,
            0x63 /* F64_LT */ => cmpop_f64(&mut stack, |a,b| a < b)?,

            // Integer arithmetic
            0x6A /* I32_ADD */ => binop_i32(&mut stack, |a,b| Ok(a.wrapping_add(b)))?,
            0x6B /* I32_SUB */ => binop_i32(&mut stack, |a,b| Ok(a.wrapping_sub(b)))?,
            0x6C /* I32_MUL */ => binop_i32(&mut stack, |a,b| Ok(a.wrapping_mul(b)))?,
            0x6D /* I32_DIV_S */ => binop_i32(&mut stack, |a,b| {
                if b == 0 { return Err(Trap::Unimplemented("i32.div_s divide by zero")); }
                if a == i32::MIN && b == -1 { return Err(Trap::Unimplemented("i32.div_s overflow")); }
                Ok(a / b)
            })?,
            0x6E /* I32_DIV_U */ => {
                let b = pop_i32(&mut stack)? as u32;
                let a = pop_i32(&mut stack)? as u32;
                if b == 0 { return Err(Trap::Unimplemented("i32.div_u divide by zero")); }
                stack.push(Value::I32((a / b) as i32));
            }

            0x7C /* I64_ADD */ => binop_i64(&mut stack, |a,b| Ok(a.wrapping_add(b)))?,
            0x7D /* I64_SUB */ => binop_i64(&mut stack, |a,b| Ok(a.wrapping_sub(b)))?,
            0x7E /* I64_MUL */ => binop_i64(&mut stack, |a,b| Ok(a.wrapping_mul(b)))?,
            0x7F /* I64_DIV_S */ => binop_i64(&mut stack, |a,b| {
                if b == 0 { return Err(Trap::Unimplemented("i64.div_s divide by zero")); }
                if a == i64::MIN && b == -1 { return Err(Trap::Unimplemented("i64.div_s overflow")); }
                Ok(a / b)
            })?,
            0x80 /* I64_DIV_U */ => {
                let b = pop_i64(&mut stack)? as u64;
                let a = pop_i64(&mut stack)? as u64;
                if b == 0 { return Err(Trap::Unimplemented("i64.div_u divide by zero")); }
                stack.push(Value::I64((a / b) as i64));
            }

            // Float arithmetic
            0x92 /* F32_ADD */ => binop_f32(&mut stack, |a,b| a + b)?,
            0x93 /* F32_SUB */ => binop_f32(&mut stack, |a,b| a - b)?,
            0x94 /* F32_MUL */ => binop_f32(&mut stack, |a,b| a * b)?,
            0x95 /* F32_DIV */ => binop_f32(&mut stack, |a,b| a / b)?,

            0xA0 /* F64_ADD */ => binop_f64(&mut stack, |a,b| a + b)?,
            0xA1 /* F64_SUB */ => binop_f64(&mut stack, |a,b| a - b)?,
            0xA2 /* F64_MUL */ => binop_f64(&mut stack, |a,b| a * b)?,
            0xA3 /* F64_DIV */ => binop_f64(&mut stack, |a,b| a / b)?,

            _ => {
                return Err(Trap::Unimplemented("opcode not implemented"));
            }
        }
    }
}

/// Execute raw code bytes with a value stack and full structured control flow (no memory context).
pub fn run_code_bytes(code: &[u8]) -> Result<Option<Value>, Trap> {
    run_with_ctx(code, None)
}

/// Execute code bytes with a provided memory context.
pub fn run_code_bytes_with_memory(code: &[u8], mem: &mut MemoryInstance) -> Result<Option<Value>, Trap> {
    run_with_ctx(code, Some(mem))
}
