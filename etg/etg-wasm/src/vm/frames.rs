//! Call and control frames used by the interpreter.

use crate::model::{ValType, Value};

#[derive(Debug)]
pub struct CallFrame {
    pub module_index: usize,
    pub func_addr: usize,      // index into Store.funcs
    pub code_def_index: usize, // index into Module.codes for this function
    pub locals: Vec<Value>,
}

impl CallFrame {
    pub fn new(module_index: usize, func_addr: usize, code_def_index: usize, locals: Vec<Value>) -> Self {
        Self { module_index, func_addr, code_def_index, locals }
    }
}

/// Structured control frames track block boundaries.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BlockKind {
    Block,
    Loop,
    If,
    Function,
}

#[derive(Debug, Clone)]
pub struct ControlFrame {
    pub kind: BlockKind,
    pub start_stack_height: usize,
    pub result_types: Vec<ValType>,
    /// Byte offset (instruction pointer) to jump to when branching to this label.
    /// For Block/If: end of the construct (just after its END).
    /// For Loop: the start of the loop body (just after the loop header).
    pub label_start: usize,
    /// Byte offset just after the matching END of this construct.
    pub label_end: usize,
    /// For If: position just after ELSE opcode if present; None if no ELSE.
    pub label_else: Option<usize>,
}

impl ControlFrame {
    pub fn new(kind: BlockKind, start_stack_height: usize, result_types: Vec<ValType>, label_start: usize, label_end: usize, label_else: Option<usize>) -> Self {
        Self { kind, start_stack_height, result_types, label_start, label_end, label_else }
    }
}
