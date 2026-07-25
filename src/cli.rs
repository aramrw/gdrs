use clap::{Parser, Subcommand};
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(name = "gdrs", version = "0.1", about = "gdrs programming language compiler toolchain")]
pub struct Cli {
    #[command(subcommand)]
    pub command: Option<Commands>,

    /// Direct input source files for JIT execution (e.g. `gdrs main.gdrs`)
    #[arg(value_parser = validate_gdrs_extension)]
    pub srcs: Vec<PathBuf>,
}

#[derive(Subcommand, Debug)]
pub enum Commands {
    /// JIT compile and run directly in memory (0.06s fast dev loop)
    Run {
        /// Source file to run
        #[arg(value_parser = validate_gdrs_extension)]
        src: PathBuf,

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
