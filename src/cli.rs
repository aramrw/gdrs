use clap::Parser;
use std::path::PathBuf;

#[derive(Parser, Debug)]
#[command(name = "compiler", version = "0.1", about = "Compiler Cli")]
pub struct Cli {
    /// The input source files to compile (must end with .gdrs)
    #[arg(required = true, value_parser = validate_gdrs_extension)]
    pub srcs: Vec<PathBuf>, 
}

/// Custom validator to check for the .gdrs extension
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
