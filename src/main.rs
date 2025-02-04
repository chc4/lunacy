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

const TIMES: f64 = 10.0;

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
        let intern_strings = internment::Arena::new();
        if let Ok((rest, header)) = header {
            let header = header.globally_intern(&intern_strings);
            let vm = Vm::new(&header.top_level as *const _);
            {
                let _G = vm.global_env(&mut owner, &intern_strings);
                let clos = vm::Tc::new(vm::LClosure::new(vm.top_level));
                let r_vals = vm.run(&mut owner, _G.clone(), clos, vec![].into())?;
                if let Some(vm::LValue::LClosure(run_iter)) = _G.get(&owner, &vm::InternString::intern(&intern_strings, "run_iter\0")) {
                    println!("> starting benchmark");
                    vm.run(&mut owner, _G.clone(), run_iter, vec![vm::LValue::Number(vm::Number(TIMES))].into()).unwrap();
                }
                dbg!(&r_vals);
            }
        }
    }

    Ok(())
}
