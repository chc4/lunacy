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
    // The owner is per-thread (a second `Owner::new()` on a thread panics), so a shared
    // `static` cell — which would have to be `Sync` — can't hold it; each test thread gets
    // its own capture buffer instead.
    static CAPTURED: TLCell<TlcOwner, Vec<String>> = const { TLCell::new(Vec::new()) };
}

#[test]
fn test_golden() {
    let test_dir = Path::new("lua_tests");
    // `LUNACY_GOLDEN`: only the test of that name.
    let only = std::env::var("LUNACY_GOLDEN").ok();
    let mut entries: Vec<_> = fs::read_dir(test_dir)
        .unwrap()
        .map(|r| r.unwrap())
        .filter(|e| only.as_ref().is_none_or(|name| e.path().file_stem().is_some_and(|stem| stem == name.as_str())))
        .collect();
    entries.sort_by_key(|e| e.path());

    for entry in entries {
        let path = entry.path();
        if path.extension().and_then(|s| s.to_str()) == Some("lua") {
            run_test_file(&path, false);
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
            run_test_file(&path, true);
        }
    }
}

fn run_test_file(path: &Path, lua_baseline: bool) {
    let content = fs::read_to_string(path).unwrap();
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
