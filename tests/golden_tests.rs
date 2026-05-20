#![feature(iter_intersperse)]
use std::fs;
use std::path::Path;
use std::process::Command;
use regex::Regex;

use lunacy::Vm;
use lunacy::chunk;
use lunacy::vm;
use qcell::{TCell, TCellOwner};

static CAPTURED: TCell<vm::TcOwner, Vec<String>> = TCell::new(Vec::new());

#[test]
fn test_golden() {
    let test_dir = Path::new("lua_tests");
    let mut entries: Vec<_> = fs::read_dir(test_dir)
        .unwrap()
        .map(|r| r.unwrap())
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

        let header = chunk::header(&bytecode[..]).unwrap().1;
        let intern_strings = internment::Arena::new();
        let header = header.globally_intern(&intern_strings);

        let mut owner = TCellOwner::new();
        let vm = Vm::new(&header.top_level as *const _);

        {
            *CAPTURED.rw(&mut owner) = Vec::new();

            let mut _g = vm.global_env(&mut owner, &intern_strings);

            // Override print
            let print_key = vm::InternString::intern(&intern_strings, "print");
            let custom_print = vm::LValue::NClosure(vm::NClosure::new(|seq, args, _returns, owner| {
                let s = args.ro(&seq).iter().map(|val| val.as_string(owner)).flat_map(|maybe_str|
                    maybe_str.map(|s| -> String { String::from(String::from_utf8_lossy(s.as_slice()).to_owned()) })
                ).collect::<Vec<_>>();
                let output = s.into_iter().intersperse("\t".to_string()).collect::<String>();
                CAPTURED.rw(owner).push(output);
            }));
            _g.set(&mut owner, print_key, custom_print);

            let clos = vm::Tc::new(vm::LClosure::new(vm.top_level));
            let args = vec![].into();

            vm.run::<true>(&mut owner, _g.clone(), clos, args).expect("VM failed");
        }
        CAPTURED.ro(&owner).clone()
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
