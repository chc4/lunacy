#![feature(trait_alias)]
pub struct TCellOwner;
pub struct RunState;
pub type ExecCallback<'a> = &'a mut dyn FnMut();
pub fn call_it(f: &dyn Fn(&mut TCellOwner, &mut RunState, ExecCallback)) {
    let mut owner = TCellOwner;
    let mut state = RunState;
    let mut cb = || {};
    f(&mut owner, &mut state, &mut cb);
}
