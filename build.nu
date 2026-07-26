#!/usr/bin/env nu

def main [
    file: string = "main.gdrs"
    --output (-o): string    # Compile to a native binary at this path
    ...rest: string          # Arguments forwarded to the gdrs program
] {
    if ($output | is-not-empty) {
        RUSTFLAGS="-Awarnings -C link-arg=-Wl,-ld_classic" cargo build --quiet
        ./target/debug/gdrs build $file -o $output
    } else {
        RUSTFLAGS="-Awarnings -C link-arg=-Wl,-ld_classic" cargo r -- run $file ...$rest
    }
}
