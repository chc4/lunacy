use std::error::Error;
use std::io::Read;
use std::fmt::Debug;

mod chunk;
use chunk::InstBits;

mod vm;
use vm::Vm;

fn main() -> Result<(), Box<dyn Error>> {
    println!("Hello, world!");
    let mut dumped = std::fs::read_dir("./dumped")?;
    for bytecode_file in dumped {
        let bytecode_file = bytecode_file?;
        println!("---------------------");
        let bytecode = std::fs::read(bytecode_file.path())?;
        let header = chunk::header(&bytecode[..]);
        dbg!(&header);
        if let Ok((rest, header)) = header {
            let mut vm = Vm::new(header.top_level);
            let r_vals = vm.run()?;
            dbg!(r_vals);
        }
    }

    Ok(())
}
