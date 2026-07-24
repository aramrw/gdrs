#!/usr/bin/env nu

def main [file: string, ...args: string] {
    # Extract the filename without .sr and format the binary name
    let binary_name = $"sr_($file | path parse | get stem)"

    # 1. Run the compiler
    RUSTFLAGS="-Awarnings" cargo run -- $file

    # 2. Run the generated binary if it exists
    if ($binary_name | path exists) {
        ^$"./($binary_name)" ...$args
        # 3. Clean up
        # rm $binary_name
    }
}
