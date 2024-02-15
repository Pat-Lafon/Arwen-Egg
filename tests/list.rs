use std::{fs::File, io::Read};

use arwen_egg::language::Examples;
use arwen_egg::program_parser_interface;
use arwen_egg::spec_parser_interface;

use crate::spec_parser_interface::SpecShim;
use components_n_specs::{list_library, list_nat_library, motivating_example_library};

use arwen_egg::synthesis;

macro_rules! make_test {
    ($test_name:tt, $n:literal, $($libs:tt)*) => {
        #[test]
        fn $test_name() {
            let mut file =
                File::open(format!("tests/benchmarks/{}.mls", stringify!($test_name))).unwrap();
            let mut buffer = String::new();
            file.read_to_string(&mut buffer).unwrap();
            let synth_problem = program_parser_interface::parse(buffer);

            let sig = if /* let Some(mut file) =
                File::open(format!("tests/benchmarks/{}.ml", stringify!($test_name))).ok() */ false {
                let mut buffer = String::new();
                file.read_to_string(&mut buffer).unwrap();
                let SpecShim{
                    spec_map,
                    spec_sig,
                } = spec_parser_interface::parse(buffer, synth_problem.sig);
                spec_sig
            } else {
                synth_problem.sig.into()
            };

            let prog = synthesis(
                sig,
                $($libs)*,
                Examples::new(synth_problem.tests.tests, Vec::new()),
                $n,
                ["data", stringify!($test_name)].iter().collect(),
            );
            insta::assert_display_snapshot!(stringify!($test_name), prog.unwrap());
        }
    };
}

make_test!(motivating_example, 2, &motivating_example_library());

make_test!(elrond_customstk, 3, &list_library());

make_test!(list_append, 3, &list_library());
make_test!(list_compress, 3, &list_library());
/* make_test!(list_concat, &list_library()); */
make_test!(list_drop, 3, &list_nat_library());
make_test!(list_dropeven, 3, &list_library());
make_test!(list_even_parity, 3, &list_library());
make_test!(list_hd, 3, &list_nat_library());
make_test!(list_inc, 3, &list_library());
make_test!(list_length, 3, &list_nat_library());
make_test!(list_make, 3, &list_library());
make_test!(list_nth, 3, &list_library());
make_test!(list_pairwise, 3, &list_library());
make_test!(list_range, 3, &list_library());
make_test!(list_rev_app, 3, &list_library());
make_test!(list_rev_fold, 3, &list_library());
make_test!(list_rev_snoc, 3, &list_library());
make_test!(list_rev_tailcall, 3, &list_library());
make_test!(list_snoc, 3, &list_library());
make_test!(list_sort_sorted_insert, 3, &list_library());
make_test!(list_sorted_insert, 3, &list_library());
make_test!(list_stutter, 3, &list_library());
make_test!(list_sum, 3, &list_library());
make_test!(list_take, 3, &list_library());
make_test!(list_tl, 3, &list_library());
