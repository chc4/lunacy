#![feature(trait_alias, specialization)]
use std::error::Error;
use std::ffi::OsString;
use std::io::Read;
use std::fmt::Debug;

use log::debug;

use qcell::TCellOwner;

mod chunk;
use chunk::InstBits;

mod vm;
use vm::Vm;

#[global_allocator]
static GLOBAL: mimalloc::MiMalloc = mimalloc::MiMalloc;

fn main() -> Result<(), Box<dyn Error>> {
    env_logger::init();
    let mut owner = TCellOwner::new();


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
        let mut intern_strings = internment::Arena::new();
        if let Ok((rest, header)) = header {
            let header = header.globally_intern(&intern_strings);
            let mut vm = Vm::new(&header.top_level as *const _);
            {
                let _G = vm.global_env(&mut owner, &intern_strings);
                let r_vals = vm.run(&mut owner, _G.clone())?;
                dbg!(&r_vals);
            }
        }
    }

    Ok(())
}
