use std::{env, error::Error, path::PathBuf, process};

use oxc_allocator::Allocator;
use oxc_checker::{
    checker::{Checker, NodeRef},
    program::{FsProgramHost, ProgramStoreBuilder},
};

fn main() {
    let mut args = env::args_os();
    let program_name = args
        .next()
        .and_then(|arg| arg.into_string().ok())
        .unwrap_or_else(|| "type_check".to_string());

    let Some(path) = args.next() else {
        eprintln!("usage: {program_name} <path-to-file>");
        process::exit(2);
    };

    if args.next().is_some() {
        eprintln!("usage: {program_name} <path-to-file>");
        process::exit(2);
    }

    if let Err(error) = run(PathBuf::from(path)) {
        eprintln!("error: {error}");
        process::exit(1);
    }
}

fn run(path: PathBuf) -> Result<(), Box<dyn Error>> {
    let allocator = Allocator::default();
    let store = ProgramStoreBuilder::new(&allocator, FsProgramHost::new())
        .add_root_file(path)
        .build()?;
    let checker = Checker::new(&store);

    for entry in store.entries().iter().filter(|entry| !entry.is_lib()) {
        for (node_id, _node) in entry.semantic().nodes().iter_enumerated() {
            let _ty = checker.get_type_at_location(NodeRef::new(entry.id(), node_id));
        }
    }

    Ok(())
}
