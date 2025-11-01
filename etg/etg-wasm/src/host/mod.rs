pub mod func;

use crate::model::{FuncType, GlobalType, MemoryType, TableType};
pub use func::HostFunc;

/// Host import resolver. Provides addresses for imported items and host functions.
/// - Tables/memories/globals return pre-allocated Store indices (addresses).
/// - Functions return an Arc to a host callable with the expected FuncType.
pub trait ImportResolver {
    fn resolve_func(
        &self,
        module: &str,
        name: &str,
        ty: &FuncType,
    ) -> Option<std::sync::Arc<HostFunc>>;

    fn resolve_table(&self, module: &str, name: &str, tt: &TableType) -> Option<usize>;
    fn resolve_memory(&self, module: &str, name: &str, mt: &MemoryType) -> Option<usize>;
    fn resolve_global(&self, module: &str, name: &str, gt: &GlobalType) -> Option<usize>;
}
