use std::{fs::File, io::Read};

use arwen_egg::language::Examples;
use arwen_egg::program_parser_interface::parse;

use components_n_specs::bool_library;

use arwen_egg::synthesis;

macro_rules! make_test {
    ($test_name:tt, $($libs:tt)*) => {
        #[test]
        fn $test_name() {
            let mut file =
                File::open(format!("tests/benchmarks/{}.mls", stringify!($test_name))).unwrap();
            let mut buffer = String::new();
            file.read_to_string(&mut buffer).unwrap();
            let synth_problem = parse(buffer);

            let prog = synthesis(
                synth_problem.sig.into(),
                $($libs)*,
                Examples::new(synth_problem.tests.tests, Vec::new()),
                4,
                ["data", stringify!($test_name)].iter().collect(),
            );
            insta::assert_display_snapshot!(stringify!($test_name), prog.unwrap());
        }
    };
}

make_test!(bool_always_false, &bool_library());
make_test!(bool_always_true, &bool_library());
make_test!(bool_band, &bool_library());
make_test!(bool_bor, &bool_library());
make_test!(bool_impl, &bool_library());
make_test!(bool_neg, &bool_library());
make_test!(bool_xor, &bool_library());
