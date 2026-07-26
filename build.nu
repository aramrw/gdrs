#!/usr/bin/env nu

def main [
    file: string = "main.gdrs"
    --output (-o): string    # Compile to a native binary at this path
    ...rest: string          # Arguments forwarded to the gdrs program
] {
    if ($output | is-not-empty) {
        RUSTFLAGS="-Awarnings -C symbol-mangling-version=v0" cargo build --quiet
        ./target/debug/gdrs build $file -o $output
    } else {
        RUSTFLAGS="-Awarnings -C symbol-mangling-version=v0" cargo r -- run $file ...$rest
    }
}
