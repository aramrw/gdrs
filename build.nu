#!/usr/bin/env nu

def main [file: string = "main.gdrs"] {
    RUSTFLAGS="-Awarnings -C link-arg=-Wl,-ld_classic" cargo r -- $file
}
