//! Copies its input to its output with every Rust symbol in it demangled
//! (without hashes), as rustfilt does: v0 symbols with enum const generics too,
//! which objdump's `-C` leaves mangled. For `just stencil-sizes`.

use std::io::{BufRead, Write};

fn main() {
    let stdin = std::io::stdin();
    let mut out = std::io::BufWriter::new(std::io::stdout().lock());
    for line in stdin.lock().lines() {
        let line = line.expect("input");
        let mut rest = line.as_str();
        // Each run of symbol characters, demangled if it is a symbol.
        while !rest.is_empty() {
            let end = rest.find(|c: char| !(c.is_ascii_alphanumeric() || c == '_' || c == '$' || c == '.')).unwrap_or(rest.len());
            let (word, tail) = rest.split_at(end.max(1));
            match rustc_demangle::try_demangle(word) {
                Ok(symbol) => write!(out, "{symbol:#}"),
                Err(_) => write!(out, "{word}"),
            }
            .expect("output");
            rest = tail;
        }
        writeln!(out).expect("output");
    }
}
