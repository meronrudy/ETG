#![allow(dead_code)]
//! Value stack for the interpreter.

use crate::error::Trap;
use crate::model::{ValType, Value};

#[derive(Debug, Default)]
pub struct ValueStack {
    stack: Vec<Value>,
}

impl ValueStack {
    pub fn new() -> Self {
        Self { stack: Vec::new() }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.stack.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    pub fn push(&mut self, v: Value) {
        self.stack.push(v);
    }

    pub fn pop(&mut self) -> Result<Value, Trap> {
        self.stack.pop().ok_or(Trap::Unimplemented("stack underflow"))
    }

    pub fn pop_typed(&mut self, _t: ValType) -> Result<Value, Trap> {
        // For MVP scaffolding, we don't enforce types here; the validator will.
        self.pop()
    }

    pub fn peek(&self) -> Option<&Value> {
        self.stack.last()
    }

    pub fn clear_to_height(&mut self, height: usize) -> Result<(), Trap> {
        if height > self.stack.len() {
            return Err(Trap::Unimplemented("invalid stack height"));
        }
        self.stack.truncate(height);
        Ok(())
    }
}
