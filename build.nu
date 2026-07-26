#!/usr/bin/env nu

def main [
    file: string = "main.gdrs"
    --output (-o): string    # Compile to a native binary at this path
    ...rest: string          # Arguments forwarded to the gdrs program
] {
    if ($output | is-not-empty) {
        RUSTFLAGS="-Awarnings" cargo build --quiet
        ./target/debug/gdrs build $file -o $output
    } else {
        RUSTFLAGS="-Awarnings" cargo r -- run $file ...$rest
    }
}
