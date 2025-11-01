//! WASM MVP sections: ids, headers, payload decoders, and a top-level module parser.
//! This layer reports errors using BinaryReadError; the public API will adapt later.

use super::{
    cursor::Cursor,
    leb128,
    reader::{read_len_prefixed_bytes, read_name, read_vec},
    BinaryReadError, Result,
};
use crate::model::{
    CodeBody, DataSegment, ElementSegment, Expr, Export, ExportDesc, FuncIdx, FuncType, Global,
    GlobalType, Import, ImportDesc, Limits, MemIdx, MemoryType, Module, RefType, TableIdx,
    TableType, TypeIdx, ValType, Value,
};

/// Standard section identifiers in the WASM binary format (MVP).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SectionId {
    Custom = 0,
    Type = 1,
    Import = 2,
    Function = 3,
    Table = 4,
    Memory = 5,
    Global = 6,
    Export = 7,
    Start = 8,
    Element = 9,
    Code = 10,
    Data = 11,
}

impl SectionId {
    pub fn from_byte(b: u8) -> Option<Self> {
        Some(match b {
            0 => SectionId::Custom,
            1 => SectionId::Type,
            2 => SectionId::Import,
            3 => SectionId::Function,
            4 => SectionId::Table,
            5 => SectionId::Memory,
            6 => SectionId::Global,
            7 => SectionId::Export,
            8 => SectionId::Start,
            9 => SectionId::Element,
            10 => SectionId::Code,
            11 => SectionId::Data,
            _ => return None,
        })
    }

    fn ordering_key(&self) -> u8 {
        *self as u8
    }
}

/// Header describing a section’s id, payload length, and the payload start offset.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SectionHeader {
    pub id: SectionId,
    pub payload_len: u32,
    pub payload_offset: usize,
}

/// Read a section header: id (u8) + payload_len (ULEB128). Returns header.
pub fn read_section_header(cur: &mut Cursor) -> Result<SectionHeader> {
    let id_byte = cur.read_u8()?;
    let id = SectionId::from_byte(id_byte).ok_or(BinaryReadError::Malformed {
        offset: cur.offset(),
        msg: "unknown section id",
    })?;
    let payload_len = leb128::read_uleb_u32(cur)?;
    let payload_offset = cur.offset();
    Ok(SectionHeader {
        id,
        payload_len,
        payload_offset,
    })
}

/* ---------- Decoding helpers ---------- */

fn read_val_type(cur: &mut Cursor) -> Result<ValType> {
    let b = cur.read_u8()?;
    match b {
        0x7F => Ok(ValType::I32),
        0x7E => Ok(ValType::I64),
        0x7D => Ok(ValType::F32),
        0x7C => Ok(ValType::F64),
        _ => Err(BinaryReadError::Malformed {
            offset: cur.offset(),
            msg: "invalid valtype",
        }),
    }
}

fn read_ref_type(cur: &mut Cursor) -> Result<RefType> {
    let b = cur.read_u8()?;
    match b {
        0x70 => Ok(RefType::FuncRef),
        _ => Err(BinaryReadError::Malformed {
            offset: cur.offset(),
            msg: "invalid reftype (expected funcref)",
        }),
    }
}

fn read_limits(cur: &mut Cursor) -> Result<Limits> {
    let tag = cur.read_u8()?;
    match tag {
        0x00 => {
            let min = leb128::read_uleb_u32(cur)?;
            Ok(Limits { min, max: None })
        }
        0x01 => {
            let min = leb128::read_uleb_u32(cur)?;
            let max = leb128::read_uleb_u32(cur)?;
            if max < min {
                return Err(BinaryReadError::Malformed {
                    offset: cur.offset(),
                    msg: "limits max < min",
                });
            }
            Ok(Limits {
                min,
                max: Some(max),
            })
        }
        _ => Err(BinaryReadError::Malformed {
            offset: cur.offset(),
            msg: "invalid limits tag",
        }),
    }
}

fn read_func_type(cur: &mut Cursor) -> Result<FuncType> {
    let form = cur.read_u8()?;
    if form != 0x60 {
        return Err(BinaryReadError::Malformed {
            offset: cur.offset(),
            msg: "expected functype (0x60)",
        });
    }
    let params = read_vec(cur, read_val_type)?;
    let results = read_vec(cur, read_val_type)?;
    Ok(FuncType { params, results })
}

fn read_table_type(cur: &mut Cursor) -> Result<TableType> {
    let elem = read_ref_type(cur)?;
    let limits = read_limits(cur)?;
    Ok(TableType { elem, limits })
}

fn read_memory_type(cur: &mut Cursor) -> Result<MemoryType> {
    let limits = read_limits(cur)?;
    Ok(MemoryType { limits })
}

fn read_global_type(cur: &mut Cursor) -> Result<GlobalType> {
    let val_type = read_val_type(cur)?;
    let mutability = cur.read_u8()?;
    let mutable = match mutability {
        0x00 => false,
        0x01 => true,
        _ => {
            return Err(BinaryReadError::Malformed {
                offset: cur.offset(),
                msg: "invalid global mutability",
            })
        }
    };
    Ok(GlobalType { val_type, mutable })
}

/// Read an initializer expression (sequence ending with 0x0B 'end').
fn read_expr(cur: &mut Cursor) -> Result<Expr> {
    let start = cur.offset();
    let mut body = Vec::new();
    loop {
        let b = cur.read_u8()?;
        body.push(b);
        if b == 0x0B {
            break;
        }
        // Defensive bound: expression must end within remaining payload; if not, UnexpectedEof triggers.
        if body.len() > 1_000_000 {
            // Arbitrary very large guard to avoid pathological data.
            return Err(BinaryReadError::Malformed {
                offset: start,
                msg: "expression too long without end",
            });
        }
    }
    Ok(Expr { body })
}

/* ---------- Section readers ---------- */

fn read_type_section(cur: &mut Cursor) -> Result<Vec<FuncType>> {
    read_vec(cur, read_func_type)
}

fn read_import_section(cur: &mut Cursor) -> Result<(Vec<Import>, u32, u32, u32, u32)> {
    let mut imports: Vec<Import> = Vec::new();
    let mut funcs = 0u32;
    let mut tables = 0u32;
    let mut mems = 0u32;
    let mut globals = 0u32;

    let count = leb128::read_uleb_u32(cur)? as usize;
    imports.reserve(count);
    for _ in 0..count {
        let module = read_name(cur)?;
        let name = read_name(cur)?;
        let kind = cur.read_u8()?;
        let desc = match kind {
            0x00 => {
                let type_idx = leb128::read_uleb_u32(cur)?;
                funcs += 1;
                ImportDesc::Func(type_idx)
            }
            0x01 => {
                let tt = read_table_type(cur)?;
                tables += 1;
                ImportDesc::Table(tt)
            }
            0x02 => {
                let mt = read_memory_type(cur)?;
                mems += 1;
                ImportDesc::Memory(mt)
            }
            0x03 => {
                let gt = read_global_type(cur)?;
                globals += 1;
                ImportDesc::Global(gt)
            }
            _ => {
                return Err(BinaryReadError::Malformed {
                    offset: cur.offset(),
                    msg: "invalid import desc tag",
                })
            }
        };
        imports.push(Import { module, name, desc });
    }
    Ok((imports, funcs, tables, mems, globals))
}

fn read_function_section(cur: &mut Cursor) -> Result<Vec<TypeIdx>> {
    read_vec(cur, |c| leb128::read_uleb_u32(c))
}

fn read_table_section(cur: &mut Cursor) -> Result<Vec<TableType>> {
    read_vec(cur, read_table_type)
}

fn read_memory_section(cur: &mut Cursor) -> Result<Vec<MemoryType>> {
    read_vec(cur, read_memory_type)
}

fn read_global_section(cur: &mut Cursor) -> Result<Vec<Global>> {
    read_vec(cur, |c| {
        let ty = read_global_type(c)?;
        let init = read_expr(c)?;
        Ok(Global { ty, init })
    })
}

fn read_export_section(cur: &mut Cursor) -> Result<Vec<Export>> {
    read_vec(cur, |c| {
        let name = read_name(c)?;
        let kind = c.read_u8()?;
        let desc = match kind {
            0x00 => ExportDesc::Func(leb128::read_uleb_u32(c)?),
            0x01 => ExportDesc::Table(leb128::read_uleb_u32(c)?),
            0x02 => ExportDesc::Memory(leb128::read_uleb_u32(c)?),
            0x03 => ExportDesc::Global(leb128::read_uleb_u32(c)?),
            _ => {
                return Err(BinaryReadError::Malformed {
                    offset: c.offset(),
                    msg: "invalid export desc tag",
                })
            }
        };
        Ok(Export { name, desc })
    })
}

fn read_start_section(cur: &mut Cursor) -> Result<FuncIdx> {
    leb128::read_uleb_u32(cur)
}

fn read_element_section(cur: &mut Cursor) -> Result<Vec<ElementSegment>> {
    // MVP format: vec of segments, each: table_idx, offset expr, vec(funcidx)
    read_vec(cur, |c| {
        let table = leb128::read_uleb_u32(c)? as TableIdx;
        let offset = read_expr(c)?;
        let init = read_vec(c, |c2| leb128::read_uleb_u32(c2))?;
        Ok(ElementSegment {
            table,
            offset,
            init,
        })
    })
}

fn read_code_section(cur: &mut Cursor) -> Result<Vec<CodeBody>> {
    // code: vec of size-prefixed bodies
    let count = leb128::read_uleb_u32(cur)? as usize;
    let mut out = Vec::with_capacity(count);
    for _ in 0..count {
        let body_size = leb128::read_uleb_u32(cur)? as usize;
        let body_bytes = cur.read_bytes(body_size)?;
        let mut sub = Cursor::new(body_bytes);

        // locals: vec of (count, valtype)
        let local_groups = leb128::read_uleb_u32(&mut sub)? as usize;
        let mut locals = Vec::with_capacity(local_groups);
        for _ in 0..local_groups {
            let count = leb128::read_uleb_u32(&mut sub)?;
            let val_type = read_val_type(&mut sub)?;
            locals.push(crate::model::LocalDecl { count, val_type });
        }

        // remaining bytes are the instruction stream (must end with 0x0B per MVP)
        let remaining = sub.remaining();
        let body = if remaining > 0 {
            sub.read_bytes(remaining)?.to_vec()
        } else {
            Vec::new()
        };

        out.push(CodeBody { locals, body });
        if !sub.is_eof() {
            return Err(BinaryReadError::Malformed {
                offset: sub.offset(),
                msg: "did not fully consume code body",
            });
        }
    }
    Ok(out)
}

fn read_data_section(cur: &mut Cursor) -> Result<Vec<DataSegment>> {
    // MVP format: vec of segments, each: memory_idx, offset expr, init bytes
    read_vec(cur, |c| {
        let memory = leb128::read_uleb_u32(c)? as MemIdx;
        let offset = read_expr(c)?;
        let init = read_len_prefixed_bytes(c)?; // Actually MVP uses vec(u8), not length-prefixed-within. Adjust:
        // Correction: data.init is vec(u8) encoded as length (ULEB) + bytes (not nested LP). read_len_prefixed_bytes already does that.
        Ok(DataSegment {
            memory,
            offset,
            init,
        })
    })
}

/* ---------- Top-level module parser (internal) ---------- */

fn ensure_fully_consumed(mut cur: Cursor) -> Result<()> {
    if cur.remaining() != 0 {
        return Err(BinaryReadError::Malformed {
            offset: cur.offset(),
            msg: "section payload not fully consumed",
        });
    }
    Ok(())
}

/// Parse a complete module from raw bytes into the IR Module (internal parser).
/// Uses BinaryReadError; public API will wrap/translate later.
pub fn parse_module_from_bytes(bytes: &[u8]) -> Result<Module> {
    let mut cur = Cursor::new(bytes);

    // Magic "\0asm" and version 1
    let magic = cur.read_u32_le()?;
    if magic != 0x6D_73_61_00 {
        return Err(BinaryReadError::Malformed {
            offset: 0,
            msg: "bad magic header",
        });
    }
    let version = cur.read_u32_le()?;
    if version != 0x01_00_00_00 {
        return Err(BinaryReadError::Malformed {
            offset: 4,
            msg: "unsupported version",
        });
    }

    let mut module = Module::default();
    let mut seen = [false; 12]; // index by SectionId as u8 (0..=11)
    let mut last_order_key: u8 = 0;

    while !cur.is_eof() {
        let header = read_section_header(&mut cur)?;
        // Bound payload cursor
        let payload = cur.read_bytes(header.payload_len as usize)?;
        let mut pcur = Cursor::new(payload);

        match header.id {
            SectionId::Custom => {
                // Skip custom section payload
                // Optional: read name via read_name(&mut pcur) and ignore the rest.
                // Best-effort: attempt to read name, but tolerate errors by skipping.
                let _ = read_name(&mut pcur);
                // rest of payload is ignored
            }
            id => {
                // Ordering: must be non-decreasing; Custom ignored
                let key = id.ordering_key();
                if key < last_order_key {
                    return Err(BinaryReadError::Malformed {
                        offset: header.payload_offset,
                        msg: "section out of order",
                    });
                }
                last_order_key = key;

                // Duplicate check for standard sections
                let idx = key as usize;
                if idx < seen.len() {
                    if seen[idx] {
                        return Err(BinaryReadError::Malformed {
                            offset: header.payload_offset,
                            msg: "duplicate standard section",
                        });
                    }
                    seen[idx] = true;
                }

                match id {
                    SectionId::Type => {
                        module.types = read_type_section(&mut pcur)?;
                    }
                    SectionId::Import => {
                        let (imports, f, t, m, g) = read_import_section(&mut pcur)?;
                        module.imports = imports;
                        module.imported_funcs = f;
                        module.imported_tables = t;
                        module.imported_memories = m;
                        module.imported_globals = g;
                    }
                    SectionId::Function => {
                        module.func_type_indices = read_function_section(&mut pcur)?;
                    }
                    SectionId::Table => {
                        module.tables = read_table_section(&mut pcur)?;
                    }
                    SectionId::Memory => {
                        module.memories = read_memory_section(&mut pcur)?;
                        if module.memories.len() > 1 {
                            return Err(BinaryReadError::Malformed {
                                offset: header.payload_offset,
                                msg: "multiple memories not supported in MVP",
                            });
                        }
                    }
                    SectionId::Global => {
                        module.globals = read_global_section(&mut pcur)?;
                    }
                    SectionId::Export => {
                        module.exports = read_export_section(&mut pcur)?;
                    }
                    SectionId::Start => {
                        // Start must contain exactly one func idx.
                        module.start = Some(read_start_section(&mut pcur)?);
                    }
                    SectionId::Element => {
                        module.elements = read_element_section(&mut pcur)?;
                    }
                    SectionId::Code => {
                        module.codes = read_code_section(&mut pcur)?;
                    }
                    SectionId::Data => {
                        module.data = read_data_section(&mut pcur)?;
                    }
                    SectionId::Custom => unreachable!(),
                }
            }
        }

        // Ensure we consumed payload fully for standard sections
        ensure_fully_consumed(pcur)?;
    }

    // Cross-section basic consistency checks (leave deep checks to validator)
    if module.func_type_indices.len() != module.codes.len() {
        return Err(BinaryReadError::Malformed {
            offset: 0,
            msg: "function and code section length mismatch",
        });
    }

    Ok(module)
}

/* ---------- Tests (smoke for headers) ---------- */
#[cfg(test)]
mod tests {
    use super::*;
    use crate::binary::cursor::Cursor;

    #[test]
    fn header_ok() {
        // id=Type(1), payload_len=3, then three bytes (ignored)
        let data = [1u8, 0x03, 0xAA, 0xBB, 0xCC];
        let mut c = Cursor::new(&data);
        let h = read_section_header(&mut c).unwrap();
        assert_eq!(h.id, SectionId::Type);
        assert_eq!(h.payload_len, 3);
        assert_eq!(h.payload_offset, 2);
    }
}
