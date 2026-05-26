use std::error::Error;
use qcell::TCellOwner;
use lunacy::Vm;
use lunacy::chunk;
use lunacy::vm;

const TIMES: f64 = 10.0;
const LBBV: bool = true;

fn main() -> Result<(), Box<dyn Error>> {
    env_logger::builder().format_timestamp(None).format_source_path(true).init();
    let mut owner = TCellOwner::new();

    let input = std::env::args().nth(1).ok_or("usage: bench <file>")?;
    let bytecode = std::fs::read(input)?;
    let header = chunk::header(&bytecode[..]);
    let intern_strings = internment::Arena::new();
    if let Ok((_rest, header)) = header {
        let header = header.globally_intern(&intern_strings);
        let vm = Vm::new(&header.top_level as *const _);
        {
            let _g = vm.global_env(&mut owner, &intern_strings);
            let clos = vm::Tc::new(vm::LClosure::new(vm.top_level));
            let mut _r_vals = vm.run::<LBBV>(&mut owner, _g.clone(), clos, vec![].into())?;

            let vm::LValue::LClosure(run_iter) = _g.get(&owner, &vm::InternString::intern(&intern_strings, "run_iter")).ok_or("no run_iter")? else { panic!() };
            println!("> starting benchmark");
            _r_vals = vm.run::<LBBV>(&mut owner, _g.clone(), run_iter, vec![vm::LValue::Number(vm::Number(TIMES))].into())?;
        }
    }

    Ok(())
}
