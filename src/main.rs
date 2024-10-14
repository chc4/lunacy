#![feature(trait_alias)]
use std::error::Error;
use std::ffi::OsString;
use std::io::Read;
use std::fmt::Debug;

use log::debug;

mod chunk;
use chunk::InstBits;

mod vm;
use vm::Vm;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() -> Result<(), Box<dyn Error>> {
    env_logger::init();

    let input = std::env::args().nth(1);
    let inputs = if let Some(input) = input {
        vec![OsString::from(input)]
    } else {
        let mut dumped = std::fs::read_dir("./dumped")?;
        let mut dumped_sorted = dumped.flatten().map(|v| v.path().into_os_string()).collect::<Vec<_>>();
        dumped_sorted.sort();
        dumped_sorted
    };
    for bytecode_file in inputs {
        println!("--------------------- {:?}", bytecode_file);
        let bytecode = std::fs::read(bytecode_file)?;
        let header = chunk::header(&bytecode[..]);
        debug!("header {:?}", &header);
        if let Ok((rest, header)) = header {
            let mut intern = internment::Arena::new();
            let k = &intern;
            let header = header.globally_intern(k);
            let mut vm = Vm::new(header.top_level);
            let r_vals = vm.run()?;
            dbg!(r_vals);
        }
    }

    Ok(())
}
