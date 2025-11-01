use crate::error::Trap;
use crate::model::Value;

/// Host function callable from WASM/host bridge.
/// MVP supports at most one return value.
pub type HostFunc = dyn Fn(&[Value]) -> Result<Option<Value>, Trap> + Send + Sync;
