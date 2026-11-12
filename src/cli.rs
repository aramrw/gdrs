use clap::{Parser, Subcommand};
use std::path::PathBuf;

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

        /// Additional arguments passed to the gdrs script
        #[arg(trailing_var_arg = true, allow_hyphen_values = true)]
        args: Vec<String>,
    },
    /// AOT compile to a standalone native binary executable
    Build {
        /// Source file to build
        #[arg(value_parser = validate_gdrs_extension)]
        src: PathBuf,

        /// Output binary executable path
        #[arg(short, long, default_value = "main")]
        output: String,

        /// Native C library search paths
        #[arg(short = 'L', value_name = "DIR")]
        lib_dirs: Vec<String>,

        /// Link native C libraries
        #[arg(short = 'l', value_name = "LIB")]
        libs: Vec<String>,
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
