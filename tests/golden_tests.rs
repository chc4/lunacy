#![feature(iter_intersperse)]
use std::fs;
use std::path::Path;
use std::process::Command;
use regex::Regex;

use lunacy::Vm;
use lunacy::chunk;
use lunacy::vm;
use lunacy::{TLCell, TlcOwner, Owner};

thread_local! {
    // The metatable of `make_userdata`'s userdata, as its bits: a native captures nothing. The
    // global `userdata_metatable` holds it too, which keeps it alive.
    static USERDATA_METATABLE: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    // The metatable of `make_counter`'s userdata, as `USERDATA_METATABLE`; the global
    // `counter_metatable` holds it.
    static COUNTER_METATABLE: std::cell::Cell<u64> = const { std::cell::Cell::new(0) };
    // The owner is per-thread (a second `Owner::new()` on a thread panics), so a shared
    // `static` cell — which would have to be `Sync` — can't hold it; each test thread gets
    // its own capture buffer instead.
    static CAPTURED: TLCell<TlcOwner, Vec<String>> = const { TLCell::new(Vec::new()) };
}

#[test]
fn test_golden() {
    let test_dir = Path::new("lua_tests");
    // `LUNACY_GOLDEN`: only the tests of those names, separated by commas.
    let only = std::env::var("LUNACY_GOLDEN").ok();
    let named = |stem: &std::ffi::OsStr| only.as_ref().is_none_or(|names| names.split(',').any(|name| stem == name));
    let mut entries: Vec<_> = fs::read_dir(test_dir)
        .unwrap()
        .map(|r| r.unwrap())
        .filter(|e| e.path().file_stem().is_some_and(named))
        .collect();
    entries.sort_by_key(|e| e.path());

    for entry in entries {
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) == Some("lua") {
            run_timed(&path, false);
        }
    }
}

#[test]
fn test_lua_baseline() {
    let test_dir = Path::new("lua_tests");
    let mut entries: Vec<_> = fs::read_dir(test_dir)
        .unwrap()
        .map(|r| r.unwrap())
        .collect();
    entries.sort_by_key(|e| e.path());

    for entry in entries {
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) == Some("lua") {
            run_timed(&path, true);
        }
    }
}

/// `run_test_file` on a thread of its own, failing if it runs past `LUNACY_GOLDEN_TIMEOUT`
/// seconds (120 by default): a golden test is small, and one running that long is stuck. The
/// thread is left running, and ends with the test process.
fn run_timed(path: &Path, lua_baseline: bool) {
    let limit = std::env::var("LUNACY_GOLDEN_TIMEOUT").ok().and_then(|s| s.parse().ok()).unwrap_or(120);
    // `LUNACY_GOLDEN_GAS_SEED`: each test run with gas (feature `gas`) the seed and its name
    // choose, from 1 to about a million, as likely small as large: JIT code stopping anywhere
    // must leave the run as it would have been.
    if let Some(seed) = std::env::var("LUNACY_GOLDEN_GAS_SEED").ok().filter(|_| !lua_baseline) {
        use std::hash::{Hash, Hasher};
        let mut hasher = std::hash::DefaultHasher::new();
        (seed, path).hash(&mut hasher);
        let bits = hasher.finish();
        let gas = (1u64 << (bits % 21)) + (bits >> 32) % (1u64 << (bits % 21));
        println!("{} with gas {gas}", path.display());
        // Read when the run starts, on the test's thread; nothing else runs meanwhile.
        unsafe { std::env::set_var("LUNACY_GAS", gas.to_string()) };
    }
    // `LUNACY_GOLDEN_EFFECT_SEED`: each test run once to count the specializer's yields, then again
    // with an effect applied at one the seed and its name choose, and which effect
    // (`LUNACY_GOLDEN_EFFECT_AT`, `yield:effect`, instead names them): code knowing less must give
    // the same output. See Note [Conservative information].
    #[cfg(feature = "conservative_information")]
    let named = std::env::var("LUNACY_GOLDEN_EFFECT_AT").ok().and_then(|s| {
        let (at, effect) = s.split_once(':').unwrap_or((&s, "0"));
        Some((at.parse::<u64>().ok()?, effect.parse::<usize>().ok()?))
    });
    #[cfg(feature = "conservative_information")]
    let at = match (std::env::var("LUNACY_GOLDEN_EFFECT_SEED").ok(), named) {
        (_, Some(at)) if !lua_baseline => Some(at),
        (Some(seed), None) if !lua_baseline => {
            let owned = path.to_path_buf();
            let ticks = std::thread::spawn(move || {
                run_test_file(&owned, lua_baseline);
                lunacy::specialize::conservative::TICKS.with(|ticks| ticks.get())
            }).join().unwrap_or_else(|panic| std::panic::resume_unwind(panic));
            use std::hash::{Hash, Hasher};
            let mut hasher = std::hash::DefaultHasher::new();
            (seed, path).hash(&mut hasher);
            let bits = hasher.finish();
            (ticks > 0).then(|| (1 + bits % ticks, (bits >> 32) as usize % lunacy::specialize::conservative::EFFECTS.len()))
        },
        _ => None,
    };
    #[cfg(feature = "conservative_information")]
    if let Some((at, effect)) = at {
        println!("{} with effect {effect} at yield {at} (LUNACY_GOLDEN_EFFECT_AT={at}:{effect})", path.display());
    }
    // `LUNACY_GOLDEN_EFFECT_EVERY`: the test run with each effect at each of its yields in turn, and
    // how many of those runs fail, to see how likely a random one is to.
    #[cfg(feature = "conservative_information")]
    if std::env::var_os("LUNACY_GOLDEN_EFFECT_EVERY").is_some() && !lua_baseline {
        let owned = path.to_path_buf();
        let ticks = std::thread::spawn(move || {
            run_test_file(&owned, lua_baseline);
            lunacy::specialize::conservative::TICKS.with(|ticks| ticks.get())
        }).join().unwrap_or_else(|panic| std::panic::resume_unwind(panic));
        let effects = lunacy::specialize::conservative::EFFECTS.len();
        let failed: Vec<String> = (1..=ticks).flat_map(|at| (0..effects).map(move |effect| (at, effect))).filter(|&(at, effect)| {
            let owned = path.to_path_buf();
            std::thread::spawn(move || {
                lunacy::specialize::conservative::AT.with(|cell| cell.set(Some((at, effect))));
                run_test_file(&owned, lua_baseline);
            }).join().is_err()
        }).map(|(at, effect)| format!("{at}:{effect}")).collect();
        println!("{}: {} of {} effects at its {ticks} yields fail: {:?}", path.display(), failed.len(), ticks as usize * effects, &failed[..failed.len().min(20)]);
        assert!(failed.is_empty(), "{} fails with {} of the effects at its yields", path.display(), failed.len());
        return;
    }
    let owned = path.to_path_buf();
    let (done, finished) = std::sync::mpsc::channel();
    let test = std::thread::spawn(move || {
        #[cfg(feature = "conservative_information")]
        lunacy::specialize::conservative::AT.with(|cell| cell.set(at));
        run_test_file(&owned, lua_baseline);
        let _ = done.send(());
    });
    // A panic drops the sender: the test's own failure, from its thread.
    match finished.recv_timeout(std::time::Duration::from_secs(limit)) {
        Err(std::sync::mpsc::RecvTimeoutError::Timeout) => panic!("{} ran past {limit}s", path.display()),
        _ => if let Err(panic) = test.join() { std::panic::resume_unwind(panic) },
    }
}

fn run_test_file(path: &Path, lua_baseline: bool) {
    let content = fs::read_to_string(path).unwrap();
    // `-- FEATURE: watchpoints`: a test of what only that cargo feature has, skipped without it;
    // `-- FEATURE: !conservative_information`, a test skipped with that feature.
    let enabled = |feature: &str| match feature {
        "watchpoints" => cfg!(feature = "watchpoints"),
        "conservative_information" => cfg!(feature = "conservative_information"),
        _ => panic!("{}: an unknown feature {feature}", path.display()),
    };
    let skipped = content.lines().filter_map(|l| l.strip_prefix("-- FEATURE: ")).any(|feature| match feature.strip_prefix('!') {
        Some(feature) => enabled(feature),
        None => !enabled(feature),
    });
    if !lua_baseline && skipped {
        return;
    }
    let expected: Vec<String> = content
        .lines()
        .filter(|l| l.starts_with("-- EXPECT: "))
        .map(|l| l.trim_start_matches("-- EXPECT: ").to_string())
        .collect();

    if expected.is_empty() && content.contains("print") {
        // Skip
    } else if expected.is_empty() && !content.contains("print") && !content.contains("assert") {
        return;
    }

    let actual = if lua_baseline {
        let status = Command::new("lua5.1")
            .arg(path)
            .output()
            .expect("Failed to run lua5.1");
        if !status.status.success() {
            return;
        }
        let out = String::from_utf8_lossy(&status.stdout);
        out.lines().map(|l| l.to_string()).collect()
    } else {
        // Compile to bytecode
        let bin_path = path.with_extension("bin");
        let status = Command::new("luac5.1")
            .arg("-o")
            .arg(&bin_path)
            .arg(path)
            .status()
            .expect("Failed to run luac5.1");
        assert!(status.success(), "Failed to compile {:?}", path);

        let bytecode = fs::read(&bin_path).unwrap();
        fs::remove_file(&bin_path).unwrap();

        let header = chunk::header(&bytecode).unwrap().1;
        let intern_strings = internment::Arena::new();
        let header = header.globally_intern(&intern_strings);

        let mut owner = Owner::new();
        let vm = Vm::new(&header.top_level as *const _);

        println!("Running golden test {}", path.display());
        // Only the captured output (plain Strings) escapes the scope. See Vm::scope.
        vm.scope(&intern_strings, &mut owner, |s, owner| -> Vec<String> {
            CAPTURED.with(|c| *c.rw(owner) = Vec::new());

            let mut _g = s.global_env(owner);

            // Override print
            let print_key = vm::LBoxed::box_lvalue(vm::InternString::intern(s.intern(), "print"));
            let custom_print = vm::LBoxed::box_lvalue(vm::LValue::NClosure(vm::NClosure::new(|seq, args, _returns, owner| {
                let s = args.ro(&seq).iter().map(|val| val.unbox().as_string(owner)).flat_map(|maybe_str|
                    maybe_str.map(|s| -> String { String::from(String::from_utf8_lossy(s.as_slice()).to_owned()) })
                ).collect::<Vec<_>>();
                let output = s.into_iter().intersperse("\t".to_string()).collect::<String>();
                CAPTURED.with(|c| c.rw(owner).push(output));
                Ok(0)
            })));
            _g.set(owner, print_key, custom_print, s.intern());

            // `blackbox(...)`: its arguments, from a native that isn't pure, so a call of it is
            // opaque to the specializer. A test runs under Lua 5.1 with an identity in its place.
            let blackbox = vm::LBoxed::box_lvalue(vm::LValue::NClosure(vm::NClosure::new(|mut seq, args, returns, _owner| {
                let args: Vec<vm::LBoxed> = args.ro(&seq).to_vec();
                let returns = returns.rw(&mut seq);
                for (i, slot) in returns.iter_mut().enumerate() {
                    *slot = args.get(i).copied().unwrap_or(vm::LBoxed::NIL);
                }
                Ok(args.len().min(returns.len()))
            })));
            _g.set(owner, vm::LBoxed::box_lvalue(vm::InternString::intern(s.intern(), "blackbox")), blackbox, s.intern());

            // `make_userdata()`: a userdata whose metatable's `__index` table has `answer`, a
            // native returning 42, as a library's objects have methods.
            let mut index = vm::Table::new(0, 1);
            index.insert_lvalue(vm::InternString::intern(s.intern(), "answer"), vm::LValue::NClosure(vm::NClosure::pure(|mut seq, _args, returns, _owner| {
                returns.rw(&mut seq).iter_mut().next().map(|r| *r = vm::LBoxed::from_double(42.0));
                Ok(1)
            })));
            let mut metatable = vm::Table::new(0, 1);
            metatable.insert_lvalue(vm::InternString::intern(s.intern(), "__index"), vm::LValue::Table(vm::Tc::new(index)));
            let metatable = vm::LBoxed::box_lvalue(vm::LValue::Table(vm::Tc::new(metatable)));
            USERDATA_METATABLE.with(|bits| bits.set(metatable.bits()));
            _g.set(owner, vm::LBoxed::box_lvalue(vm::InternString::intern(s.intern(), "userdata_metatable")), metatable, s.intern());
            let make_userdata = vm::LBoxed::box_lvalue(vm::LValue::NClosure(vm::NClosure::pure(|mut seq, _args, returns, _owner| {
                // Safety: the global `userdata_metatable` keeps it alive.
                let metatable = unsafe { vm::LBoxed::from_bits(USERDATA_METATABLE.with(|bits| bits.get())) }.as_table();
                let userdata = vm::LValue::Userdata(vm::Tc::new(vm::Userdata::new(metatable)));
                returns.rw(&mut seq).iter_mut().next().map(|r| *r = vm::LBoxed::box_lvalue(userdata));
                Ok(1)
            })));
            _g.set(owner, vm::LBoxed::box_lvalue(vm::InternString::intern(s.intern(), "make_userdata")), make_userdata, s.intern());

            // `make_counter()`: a userdata whose data is a count, from 0, which its
            // method `bump` adds one to and returns, as a library's objects keep
            // native state.
            let mut index = vm::Table::new(0, 1);
            index.insert_lvalue(vm::InternString::intern(s.intern(), "bump"), vm::LValue::NClosure(vm::NClosure::new(|mut seq, args, returns, owner| {
                let vm::LValue::Userdata(counter) = args.ro(&seq)[0].unbox() else { return Err(vm::LBoxed::NIL) };
                let count = counter.ro(owner).data::<std::cell::Cell<i32>>().expect("a counter's count");
                count.set(count.get() + 1);
                returns.rw(&mut seq).iter_mut().next().map(|r| *r = vm::LBoxed::from_int(count.get()));
                Ok(1)
            })));
            let mut metatable = vm::Table::new(0, 1);
            metatable.insert_lvalue(vm::InternString::intern(s.intern(), "__index"), vm::LValue::Table(vm::Tc::new(index)));
            let metatable = vm::LBoxed::box_lvalue(vm::LValue::Table(vm::Tc::new(metatable)));
            COUNTER_METATABLE.with(|bits| bits.set(metatable.bits()));
            _g.set(owner, vm::LBoxed::box_lvalue(vm::InternString::intern(s.intern(), "counter_metatable")), metatable, s.intern());
            let make_counter = vm::LBoxed::box_lvalue(vm::LValue::NClosure(vm::NClosure::pure(|mut seq, _args, returns, _owner| {
                // Safety: the global `counter_metatable` keeps it alive.
                let metatable = unsafe { vm::LBoxed::from_bits(COUNTER_METATABLE.with(|bits| bits.get())) }.as_table();
                let counter = vm::LValue::Userdata(vm::Tc::new(vm::Userdata::with_data(metatable, std::cell::Cell::new(0i32))));
                returns.rw(&mut seq).iter_mut().next().map(|r| *r = vm::LBoxed::box_lvalue(counter));
                Ok(1)
            })));
            _g.set(owner, vm::LBoxed::box_lvalue(vm::InternString::intern(s.intern(), "make_counter")), make_counter, s.intern());

            let clos = vm::Tc::new(vm::LClosure::new(s.vm().top_level));
            let args = vec![].into();

            s.run(owner, _g.clone(), clos, args).expect("VM failed");
            CAPTURED.with(|c| c.ro(owner).clone())
        })
    };

    let table_re = Regex::new(r"(table|tc|native|function):?\s*(0x[0-9a-f]+|\(0x[0-9a-f]+\))").unwrap();

    // Standardize comparison
    let actual_norm: Vec<String> = actual.iter().map(|s| table_re.replace_all(s, "table: <addr>").to_string()).collect();
    let expected_norm: Vec<String> = expected.iter().map(|s| table_re.replace_all(s, "table: <addr>").to_string()).collect();

    assert_eq!(actual_norm.len(), expected_norm.len(), "Output length mismatch for {:?}. Actual: {:?}, Expected: {:?}", path, actual_norm, expected_norm);
    for (a, e) in actual_norm.iter().zip(expected_norm.iter()) {
        assert_eq!(a, e, "Output mismatch for {:?}", path);
    }
}
