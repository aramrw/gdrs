use clap::{Args, Parser, Subcommand};
use std::path::{Path, PathBuf};

use crate::codegen::object::OptLevel;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum CrateType {
    #[default]
    Bin,
    Lib,
    StaticLib,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExternSpec {
    pub alias: String,
    pub path: PathBuf,
}

#[derive(Args, Debug, Clone, Default)]
pub struct CrateFlags {
    /// Crate output kind: bin, lib, or staticlib
    #[arg(long = "crate-type", value_name = "TYPE", value_parser = parse_crate_type, default_value = "bin")]
    pub crate_type: CrateType,

    /// Explicit crate name (defaults to sanitized entry file stem)
    #[arg(long = "crate-name", value_name = "NAME")]
    pub crate_name: Option<String>,

    /// External library dependency mapping (`alias=path/to/lib.rlib`)
    #[arg(long = "extern", value_name = "NAME=PATH", value_parser = parse_extern_spec)]
    pub externs: Vec<ExternSpec>,

    /// Output directory for built artifacts
    #[arg(long = "out-dir", value_name = "DIR")]
    pub out_dir: Option<PathBuf>,

    /// Comma-separated artifact outputs (`obj`, `link`, `all`)
    #[arg(long = "emit", value_name = "KINDS")]
    pub emit: Option<String>,
}

impl CrateFlags {
    pub fn resolve_crate_name(&self, src: Option<&Path>) -> String {
        if let Some(name) = &self.crate_name {
            return name.replace('-', "_");
        }
        src.and_then(|p| p.file_stem())
            .and_then(|s| s.to_str())
            .map(|s| s.replace('-', "_"))
            .unwrap_or_else(|| "main".to_string())
    }

    pub fn emit_kinds(&self) -> Result<(bool, bool), String> {
        let Some(raw) = &self.emit else {
            return Ok((false, true));
        };
        let mut emit_obj = false;
        let mut emit_link = false;
        for part in raw.split(',').map(|s| s.trim()).filter(|s| !s.is_empty()) {
            match part {
                "obj" => emit_obj = true,
                "link" => emit_link = true,
                "all" => {
                    emit_obj = true;
                    emit_link = true;
                }
                other => {
                    return Err(format!(
                        "Unknown --emit kind '{}': expected `obj`, `link`, or `all`",
                        other
                    ));
                }
            }
        }
        if !emit_obj && !emit_link {
            emit_link = true;
        }
        Ok((emit_obj, emit_link))
    }

    pub fn resolve_build_output(&self, src: &Path, explicit_output: Option<&str>) -> PathBuf {
        let crate_name = self.resolve_crate_name(Some(src));
        if let Some(out) = explicit_output {
            let p = PathBuf::from(out);
            if p.is_relative() {
                if let Some(dir) = &self.out_dir {
                    if p.parent().is_none_or(|par| par.as_os_str().is_empty()) {
                        return dir.join(p);
                    }
                }
            }
            return p;
        }
        let file_name = match self.crate_type {
            CrateType::Bin => {
                if self.crate_name.is_some() || self.out_dir.is_some() {
                    crate_name
                } else {
                    "main".to_string()
                }
            }
            CrateType::Lib => format!("lib{crate_name}.rlib"),
            CrateType::StaticLib => format!("lib{crate_name}.a"),
        };
        if let Some(dir) = &self.out_dir {
            dir.join(file_name)
        } else {
            PathBuf::from(file_name)
        }
    }

    pub fn resolve_obj_output(&self, src: &Path, explicit_output: Option<&str>, also_link: bool) -> PathBuf {
        let crate_name = self.resolve_crate_name(Some(src));
        if !also_link {
            if let Some(out) = explicit_output {
                return PathBuf::from(out);
            }
        }
        let obj_name = format!("{crate_name}.o");
        if let Some(dir) = &self.out_dir {
            dir.join(obj_name)
        } else if let Some(out) = explicit_output {
            PathBuf::from(out).with_extension("o")
        } else {
            PathBuf::from(obj_name)
        }
    }
}

fn parse_crate_type(val: &str) -> Result<CrateType, String> {
    match val {
        "bin" => Ok(CrateType::Bin),
        "lib" | "rlib" => Ok(CrateType::Lib),
        "staticlib" => Ok(CrateType::StaticLib),
        _ => Err(format!(
            "Invalid --crate-type '{}': expected `bin`, `lib`, or `staticlib`",
            val
        )),
    }
}

fn parse_extern_spec(val: &str) -> Result<ExternSpec, String> {
    let Some((alias, path)) = val.split_once('=') else {
        return Err(format!(
            "Invalid --extern '{}': expected `NAME=PATH`",
            val
        ));
    };
    let alias = alias.trim();
    let path = path.trim();
    if alias.is_empty() || path.is_empty() {
        return Err(format!(
            "Invalid --extern '{}': both alias name and library path must be non-empty",
            val
        ));
    }
    Ok(ExternSpec {
        alias: alias.to_string(),
        path: PathBuf::from(path),
    })
}

#[derive(Args, Debug, Clone, Default)]
pub struct OptFlags {
    /// Optimize generated code for speed (equivalent to --opt-level 3)
    #[arg(long)]
    pub release: bool,

    /// Optimization level: 0 (none), 1-3 (speed), s/z (speed_and_size)
    #[arg(long = "opt-level", value_name = "LEVEL", value_parser = parse_opt_level)]
    pub opt_level: Option<OptLevel>,
}

impl OptFlags {
    pub fn resolved(&self) -> OptLevel {
        if let Some(level) = self.opt_level {
            level
        } else if self.release {
            OptLevel::Speed
        } else {
            OptLevel::None
        }
    }
}

fn parse_opt_level(val: &str) -> Result<OptLevel, String> {
    match val {
        "0" | "none" => Ok(OptLevel::None),
        "1" | "2" | "3" | "speed" => Ok(OptLevel::Speed),
        "s" | "z" | "speed_and_size" => Ok(OptLevel::SpeedAndSize),
        _ => Err(format!(
            "Invalid optimization level '{}': expected 0, 1, 2, 3, s, z, none, speed, or speed_and_size",
            val
        )),
    }
}

#[derive(Parser, Debug)]
#[command(name = "gdrs", version = "0.1", about = "gdrs programming language compiler toolchain")]
pub struct Cli {
    #[command(subcommand)]
    pub command: Option<Commands>,

    /// Native C library search paths
    #[arg(short = 'L', value_name = "DIR")]
    pub lib_dirs: Vec<String>,

    /// Link native C libraries
    #[arg(short = 'l', value_name = "LIB")]
    pub libs: Vec<String>,

    #[command(flatten)]
    pub opt: OptFlags,

    #[command(flatten)]
    pub crate_flags: CrateFlags,

    /// Direct input source files to build and execute (e.g. `gdrs main.gdrs`)
    #[arg(value_parser = validate_gdrs_extension)]
    pub srcs: Vec<PathBuf>,
}

#[derive(Subcommand, Debug)]
pub enum Commands {
    /// Build and run a program natively
    Run {
        /// Source file to run
        #[arg(value_parser = validate_gdrs_extension)]
        src: PathBuf,

        /// Native C library search paths
        #[arg(short = 'L', value_name = "DIR")]
        lib_dirs: Vec<String>,

        /// Link native C libraries
        #[arg(short = 'l', value_name = "LIB")]
        libs: Vec<String>,

        #[command(flatten)]
        opt: OptFlags,

        #[command(flatten)]
        crate_flags: CrateFlags,

        /// Additional arguments passed to the gdrs script
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// AOT compile to a standalone native binary, .rlib library, or .a staticlib
    Build {
        /// Source file to build
        #[arg(value_parser = validate_gdrs_extension)]
        src: PathBuf,

        /// Output artifact path
        #[arg(short, long)]
        output: Option<String>,

        /// Native C library search paths
        #[arg(short = 'L', value_name = "DIR")]
        lib_dirs: Vec<String>,

        /// Link native C libraries
        #[arg(short = 'l', value_name = "LIB")]
        libs: Vec<String>,

        #[command(flatten)]
        opt: OptFlags,

        #[command(flatten)]
        crate_flags: CrateFlags,
    },
    /// Parse and type-check a program (or stdlib if no file is given) without codegen
    Check {
        /// Optional source file to check (omit to check std/)
        #[arg(value_parser = validate_gdrs_extension)]
        src: Option<PathBuf>,

        #[command(flatten)]
        crate_flags: CrateFlags,
    },
}

fn validate_gdrs_extension(val: &str) -> Result<PathBuf, String> {
    let path = PathBuf::from(val);
    match path.extension() {
        Some(ext) if ext == "gdrs" => Ok(path),
        _ => Err(format!(
            "Invalid file extension. Only '.gdrs' files are allowed: '{}'",
            val
        )),
    }
}
