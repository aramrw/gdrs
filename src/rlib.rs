//! rlib.rs
//! Compact binary container (`.rlib`) holding crate metadata, transitive
//! extern/native link metadata, source/template files, and compiled object code.

const RLIB_MAGIC: &[u8; 8] = b"GDRSLIB2";

#[derive(Debug, Clone)]
pub struct RlibSourceFile {
    pub rel_name: String,
    pub mod_prefix: Vec<String>,
    pub source: String,
}

#[derive(Debug, Clone)]
pub struct RlibPackage {
    pub crate_name: String,
    pub extern_aliases: Vec<(String, String)>,
    pub lib_dirs: Vec<String>,
    pub libs: Vec<String>,
    pub sources: Vec<RlibSourceFile>,
    pub object_bytes: Vec<u8>,
}

fn push_str(buf: &mut Vec<u8>, s: &str) {
    let bytes = s.as_bytes();
    buf.extend_from_slice(&(bytes.len() as u32).to_le_bytes());
    buf.extend_from_slice(bytes);
}

fn push_str_vec(buf: &mut Vec<u8>, items: &[String]) {
    buf.extend_from_slice(&(items.len() as u32).to_le_bytes());
    for item in items {
        push_str(buf, item);
    }
}

fn read_u32(data: &[u8], pos: &mut usize) -> Result<u32, String> {
    if *pos + 4 > data.len() {
        return Err("Corrupt .rlib file: unexpected end of data".to_string());
    }
    let val = u32::from_le_bytes(data[*pos..*pos + 4].try_into().unwrap());
    *pos += 4;
    Ok(val)
}

fn read_u64(data: &[u8], pos: &mut usize) -> Result<u64, String> {
    if *pos + 8 > data.len() {
        return Err("Corrupt .rlib file: unexpected end of data".to_string());
    }
    let val = u64::from_le_bytes(data[*pos..*pos + 8].try_into().unwrap());
    *pos += 8;
    Ok(val)
}

fn read_str(data: &[u8], pos: &mut usize) -> Result<String, String> {
    let len = read_u32(data, pos)? as usize;
    if *pos + len > data.len() {
        return Err("Corrupt .rlib file: string length out of bounds".to_string());
    }
    let s = std::str::from_utf8(&data[*pos..*pos + len])
        .map_err(|_| "Corrupt .rlib file: invalid UTF-8 string".to_string())?
        .to_string();
    *pos += len;
    Ok(s)
}

fn read_str_vec(data: &[u8], pos: &mut usize) -> Result<Vec<String>, String> {
    let count = read_u32(data, pos)? as usize;
    let mut items = Vec::with_capacity(count);
    for _ in 0..count {
        items.push(read_str(data, pos)?);
    }
    Ok(items)
}

pub fn encode_rlib(pkg: &RlibPackage) -> Vec<u8> {
    let mut out = Vec::new();
    out.extend_from_slice(RLIB_MAGIC);
    push_str(&mut out, &pkg.crate_name);
    out.extend_from_slice(&(pkg.extern_aliases.len() as u32).to_le_bytes());
    for (alias, target_crate) in &pkg.extern_aliases {
        push_str(&mut out, alias);
        push_str(&mut out, target_crate);
    }
    push_str_vec(&mut out, &pkg.lib_dirs);
    push_str_vec(&mut out, &pkg.libs);
    out.extend_from_slice(&(pkg.sources.len() as u32).to_le_bytes());
    for src in &pkg.sources {
        push_str(&mut out, &src.rel_name);
        push_str_vec(&mut out, &src.mod_prefix);
        push_str(&mut out, &src.source);
    }
    out.extend_from_slice(&(pkg.object_bytes.len() as u64).to_le_bytes());
    out.extend_from_slice(&pkg.object_bytes);
    out
}

pub fn decode_rlib(data: &[u8]) -> Result<RlibPackage, String> {
    if data.len() < RLIB_MAGIC.len() || &data[..RLIB_MAGIC.len()] != RLIB_MAGIC {
        return Err("Invalid .rlib archive: unrecognized header magic".to_string());
    }
    let mut pos = RLIB_MAGIC.len();
    let crate_name = read_str(data, &mut pos)?;
    let num_aliases = read_u32(data, &mut pos)? as usize;
    let mut extern_aliases = Vec::with_capacity(num_aliases);
    for _ in 0..num_aliases {
        let alias = read_str(data, &mut pos)?;
        let target_crate = read_str(data, &mut pos)?;
        extern_aliases.push((alias, target_crate));
    }
    let lib_dirs = read_str_vec(data, &mut pos)?;
    let libs = read_str_vec(data, &mut pos)?;
    let num_sources = read_u32(data, &mut pos)? as usize;
    let mut sources = Vec::with_capacity(num_sources);
    for _ in 0..num_sources {
        let rel_name = read_str(data, &mut pos)?;
        let mod_prefix = read_str_vec(data, &mut pos)?;
        let source = read_str(data, &mut pos)?;
        sources.push(RlibSourceFile {
            rel_name,
            mod_prefix,
            source,
        });
    }
    let obj_len = read_u64(data, &mut pos)? as usize;
    if pos + obj_len > data.len() {
        return Err("Corrupt .rlib file: object section truncated".to_string());
    }
    let object_bytes = data[pos..pos + obj_len].to_vec();
    Ok(RlibPackage {
        crate_name,
        extern_aliases,
        lib_dirs,
        libs,
        sources,
        object_bytes,
    })
}
