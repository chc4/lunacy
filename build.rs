//! Compiles the library written in Lua (src/library.lua) with `luac5.1`, for
//! the VM to run before every program. See Note [Library natives] in `library`.

use std::path::PathBuf;
use std::process::Command;

fn main() {
    let source = "src/library.lua";
    println!("cargo:rerun-if-changed={source}");
    let out = PathBuf::from(std::env::var("OUT_DIR").unwrap()).join("library.luac");
    let status = Command::new("luac5.1")
        .arg("-o")
        .arg(&out)
        .arg(source)
        .status()
        .expect("running luac5.1, which the devshell has");
    assert!(status.success(), "luac5.1 failed on {source}");
}
