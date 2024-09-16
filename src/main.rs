use std::error::Error;
use std::io::Read;
use std::fmt::Debug;

mod chunk;
use chunk::InstBits;

mod vm;
use vm::Vm;

fn main() -> Result<(), Box<dyn Error>> {
    println!("Hello, world!");
    for i in 1..=6 {
        let mut dumped = std::fs::File::open(format!("./dumped_{}.bin", i))?;
        let mut dumped_bytes = vec![];
        dumped.read_to_end(&mut dumped_bytes)?;

        {
            let header = chunk::header(&dumped_bytes[..]);
            dbg!(&header);
            if let Ok((rest, header)) = header {
                let mut vm = Vm::new(header.top_level);
                let r_vals = vm.run()?;
                dbg!(r_vals);
            }
        }
    }

    Ok(())
}
