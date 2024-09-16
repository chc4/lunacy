use std::error::Error;
use std::io::Read;
use std::fmt::Debug;

mod chunk;
use chunk::InstBits;

trait Instruction {
    type Unpack: Unpacker;
}

trait Unpacker {
    type Unpacked;
    #[inline(always)]
    fn unpack(inst: InstBits) -> Self::Unpacked;
}

struct AB;
impl Unpacker for AB {
    type Unpacked = (u8, u16); // A: 8, B: 9
    fn unpack(inst: InstBits) -> Self::Unpacked {
        (inst.A() as u8, inst.B() as u16)
    }
}

struct MOVE;
impl Instruction for MOVE { type Unpack = AB; }

fn main() -> Result<(), Box<dyn Error>> {
    println!("Hello, world!");
    for i in 1..=2 {
        let mut dumped = std::fs::File::open(format!("./dumped_{}.bin", i))?;
        let mut dumped_bytes = vec![];
        dumped.read_to_end(&mut dumped_bytes)?;

        {
            let header = chunk::header(&dumped_bytes[..]);
            dbg!(header);
        }
    }

    Ok(())
}
