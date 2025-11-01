 //! Central store for all runtime instances allocated by the engine.
 //! Owns function, table, memory, global, and module instances. Provides allocation helpers.

 use super::{
     global::GlobalInstance,
     instances::{FuncInstance, ModuleInstance},
     memory::MemoryInstance,
     table::TableInstance,
     InstanceHandle,
 };

#[derive(Debug, Default)]
pub struct Store {
    pub funcs: Vec<FuncInstance>,
    pub tables: Vec<TableInstance>,
    pub mems: Vec<MemoryInstance>,
    pub globals: Vec<GlobalInstance>,
    pub modules: Vec<ModuleInstance>,
}

impl Store {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn alloc_func(&mut self, f: FuncInstance) -> usize {
        let idx = self.funcs.len();
        self.funcs.push(f);
        idx
    }

    pub fn alloc_table(&mut self, t: TableInstance) -> usize {
        let idx = self.tables.len();
        self.tables.push(t);
        idx
    }

    pub fn alloc_memory(&mut self, m: MemoryInstance) -> usize {
        let idx = self.mems.len();
        self.mems.push(m);
        idx
    }

    pub fn alloc_global(&mut self, g: GlobalInstance) -> usize {
        let idx = self.globals.len();
        self.globals.push(g);
        idx
    }

    pub fn alloc_module(&mut self, m: ModuleInstance) -> usize {
        let idx = self.modules.len();
        self.modules.push(m);
        idx
    }

    /// Allocate a ModuleInstance with only the IR set; other fields defaulted.
    /// Returns an InstanceHandle for the module.
    pub fn alloc_module_ir(&mut self, module_ir: std::sync::Arc<crate::model::Module>) -> InstanceHandle {
        let mut m = ModuleInstance::default();
        m.module_ir = module_ir;
        let idx = self.modules.len();
        self.modules.push(m);
        InstanceHandle(idx)
    }

    pub fn get_module(&self, idx: usize) -> Option<&ModuleInstance> {
        self.modules.get(idx)
    }

    pub fn get_module_mut(&mut self, idx: usize) -> Option<&mut ModuleInstance> {
        self.modules.get_mut(idx)
    }

    pub fn get_func(&self, idx: usize) -> Option<&FuncInstance> {
        self.funcs.get(idx)
    }

    pub fn get_table(&self, idx: usize) -> Option<&TableInstance> {
        self.tables.get(idx)
    }

    pub fn get_memory(&self, idx: usize) -> Option<&MemoryInstance> {
        self.mems.get(idx)
    }

    pub fn get_global(&self, idx: usize) -> Option<&GlobalInstance> {
        self.globals.get(idx)
    }

    pub fn get_memory_mut(&mut self, idx: usize) -> Option<&mut MemoryInstance> {
        self.mems.get_mut(idx)
    }

    pub fn get_table_mut(&mut self, idx: usize) -> Option<&mut TableInstance> {
        self.tables.get_mut(idx)
    }

    pub fn get_global_mut(&mut self, idx: usize) -> Option<&mut GlobalInstance> {
        self.globals.get_mut(idx)
    }
}
