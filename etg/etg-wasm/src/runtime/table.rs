//! Table instance for funcref (MVP only). Stores optional function indices into the Store.

use crate::model::TableType;

#[derive(Debug, Clone)]
pub struct TableInstance {
    elems: Vec<Option<usize>>, // indices into Store.funcs
    min: u32,
    max: Option<u32>,
}

impl TableInstance {
    pub fn new(ty: &TableType) -> Self {
        let min = ty.limits.min;
        let max = ty.limits.max;
        let mut elems = Vec::with_capacity(min as usize);
        elems.resize(min as usize, None);
        Self { elems, min, max }
    }

    pub fn size(&self) -> u32 {
        self.elems.len() as u32
    }

    pub fn get(&self, idx: u32) -> Option<Option<usize>> {
        self.elems.get(idx as usize).cloned()
    }

    pub fn set(&mut self, idx: u32, val: Option<usize>) -> Result<(), ()> {
        if (idx as usize) < self.elems.len() {
            self.elems[idx as usize] = val;
            Ok(())
        } else {
            Err(())
        }
    }

    /// Grow table by delta elements (None if exceeds declared max).
    pub fn grow(&mut self, delta: u32) -> Option<u32> {
        let prev = self.size();
        let new = prev.saturating_add(delta);
        if let Some(max) = self.max {
            if new > max {
                return None;
            }
        }
        self.elems.resize(new as usize, None);
        Some(prev)
    }
}
