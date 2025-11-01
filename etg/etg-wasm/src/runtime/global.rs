//! Global instance: value + mutability per declared GlobalType.

use crate::model::{GlobalType, Value};

#[derive(Debug, Clone)]
pub struct GlobalInstance {
    ty: GlobalType,
    val: Value,
}

impl GlobalInstance {
    pub fn new(ty: GlobalType, init: Value) -> Self {
        Self { ty, val: init }
    }

    pub fn get(&self) -> Value {
        self.val
    }

    pub fn set(&mut self, v: Value) -> Result<(), ()> {
        if self.ty.mutable {
            // Type check is deferred to validator/executor in MVP.
            self.val = v;
            Ok(())
        } else {
            Err(())
        }
    }

    pub fn ty(&self) -> &GlobalType {
        &self.ty
    }
}
