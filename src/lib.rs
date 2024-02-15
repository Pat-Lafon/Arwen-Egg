#![feature(fn_traits)]
#![feature(unboxed_closures)]
#![feature(impl_trait_in_assoc_type)]
use std::{fs::File, io::Write, path::PathBuf, sync::Mutex};

use itertools::Itertools;
use language::{BaseType, Examples, Operation, Program, RefinementType, Signature};
use synthgraph::OpMap;
use tracing::info;

use crate::language::Variable;

pub mod data_structures;
pub mod language;
pub mod program_parser_interface;
pub mod spec_parser_interface;
pub mod sketch;
pub mod synthgraph;
pub mod utils;

pub type Libraries<T> = Vec<Operation<T>>;

lazy_static::lazy_static! {
    pub static ref OP_LIST: Mutex<Vec<String>> = Mutex::new(Vec::new());
}

pub fn update_global_oplist<T>(o: &OpMap<T>) {
    let mut map = OP_LIST.lock().unwrap();
    *map = o.arr.iter().map(|o| o.name.clone()).collect_vec();
}

lazy_static::lazy_static! {
    pub static ref DATADIR: Mutex<PathBuf> = Mutex::new(PathBuf::new());
}

fn set_global_datadir(p: PathBuf) {
    let mut d = DATADIR.lock().unwrap();
    *d = p;
}

pub fn data_logging_helper(file_name: String, f: impl Fn(File)) {
    let mut d = DATADIR.lock().unwrap();
    d.push(file_name);
    let file = File::create(&*d).unwrap();
    f(file);
    d.pop();
}

pub fn synthesis(
    sig: Signature<RefinementType>,
    l: &Libraries<BaseType>,
    tests: Examples,
    mut size: u8,
    mut output_folder: PathBuf,
) -> Option<Program<BaseType>> {
    // Setup folder to put output information
    output_folder.push(format!("examples_{}", &tests.len().to_string()));
    let _ = std::fs::remove_dir_all(&output_folder);
    std::fs::create_dir_all(&output_folder).unwrap();
    set_global_datadir(output_folder);

    // tracing for logging debug messages
    tracing_subscriber::fmt()
        // enable everything
        .with_max_level(tracing::Level::INFO)
        // display source code file paths
        .with_file(true)
        // display source code line numbers
        .with_line_number(true)
        // disable targets
        .with_target(false)
        // sets this to be the default, global collector for this application.
        .init();

    let variables = sig
        .input
        .iter()
        .enumerate()
        .map(|(i, ty)| Variable {
            name: format!("arg{i}"),
            ty: (ty.clone()).into(),
        })
        .collect();

    let mut g = synthgraph::SynthesisGraph::new(&tests, variables, l, sig.clone().into());

    data_logging_helper(format!("size_{}_enumeration", 1), |f| {
        g.dump_all_programs(f)
    });

    // Just by creating the graph you get all componenets of size 1
    // So we start iterating from 2 up to the expected size
    for i in 2..=size {
        dbg!(&i);
        g.increment(l);
        g.update_inverse_map();

        data_logging_helper(format!("size_{}_enumeration", i), |f| {
            g.dump_all_programs(f)
        });
    }

    update_global_oplist(&g.op_lookup);

    if g.example_map.contains_examples(&tests) {
        let x = g.extraction(&tests);
        if let Some(p) = &x {
            dbg!(g.fuzz_spec(p, &sig.clone().into()));
        };

        return x;
    }

    // I want to insert something about the recursive calls here
    // Because there are only so many variations of the recursive calls
    // I'm going to insert them at every step in the execution... in some kind of widening step assuming that non of the examples are contradictory
    let rec_id = g.generate_recursive_calls(&sig.clone().into());
    let r = g.dump_eclass(rec_id, Default::default());
    let t = r.into_iter().map(|x| x.to_string()).join("\n");

    data_logging_helper(format!("rec_eclass"), |mut f| {
        f.write_all(t.as_bytes()).unwrap();
    });

    // Before we do the top-down search, if there is an eclass that exists for our examples, we can extract right away
    g.top_down_prop(&tests, rec_id);

    data_logging_helper(format!("finished_prop"), |f| g.dump_all_programs(f));

    dbg!("Top down prop succeeded");
    update_global_oplist(&g.op_lookup);
    /*     g.egg.dot().to_dot("test.dot").unwrap(); */
    // Else, maybe we do some processing to set up the traces we are walking along
    let x = g.extraction(&tests);
    if let Some(p) = &x {
        dbg!(g.fuzz_spec(p, &sig));
    };

    x
}
