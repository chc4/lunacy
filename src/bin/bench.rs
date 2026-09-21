use std::error::Error;
use lunacy::Owner;
use lunacy::Vm;
use lunacy::chunk;
use lunacy::vm;

const TIMES: usize = 10;
// LBBV (lazy basic-block versioning / specializer) lives in the `generator`
// module, gated by the `lbbv` feature (independent of the native `jit`). In
// interpreter-only builds it is disabled so execution stays in the vm.rs
// `run()` loop.
const LBBV: bool = cfg!(feature = "lbbv");

fn main() -> Result<(), Box<dyn Error>> {
    env_logger::builder().format_timestamp(None).format_source_path(true).init();
    let mut owner = Owner::new();

    let input = std::env::args().nth(1).ok_or("usage: bench <file>")?;
    let times: usize = std::env::args().nth(2).map_or_else(|| Ok(TIMES), |s| str::parse(&s[..]))?;
    let bytecode = std::fs::read(input)?;
    let header = chunk::header(&bytecode[..]);
    let intern_strings = internment::Arena::new();
    if let Ok((_rest, header)) = header {
        let header = header.globally_intern(&intern_strings);
        let vm = Vm::new(&header.top_level as *const _);
        // Both runs share `_g` and the `run_iter` closure it holds, so they live in one GC
        // scope (branded `'gc`); the heap is hard-reset when the scope returns. See Vm::scope.
        vm.scope(&intern_strings, &mut owner, |s, owner| -> Result<(), Box<dyn Error>> {
            let _g = s.global_env();
            let clos = vm::Tc::new(vm::LClosure::new(s.vm().top_level));
            let mut _r_vals = s.run::<LBBV>(owner, _g.clone(), clos, vec![].into())?;

            let run_iter_key = vm::LBoxed::box_lvalue(vm::InternString::intern(s.intern(), "run_iter"));
            let run_iter_boxed = _g.get(owner, &run_iter_key, s.intern()).ok_or("no run_iter")?;
            let vm::LValue::LClosure(run_iter) = run_iter_boxed.unbox() else { panic!() };
            println!("> starting benchmark");
            _r_vals = s.run::<LBBV>(owner, _g.clone(), run_iter, vec![vm::LBoxed::from_number(times as f64)].into())?;
            Ok(())
        })?;
    }

    Ok(())
}
