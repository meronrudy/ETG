//! Runtime store and instance types for the WASM MVP interpreter runtime.

pub mod store;
pub mod instances;
pub mod memory;
pub mod table;
pub mod global;

pub use store::Store;
pub use instances::{FuncInstance, ModuleInstance};
pub use memory::{MemoryInstance, PAGE_SIZE};
pub use table::TableInstance;
pub use global::GlobalInstance;

/// Handle to a live module instance within the Store.
/// This is a thin wrapper around the module index in the store.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct InstanceHandle(pub usize);
