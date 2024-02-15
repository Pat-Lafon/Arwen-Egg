use arwen_egg::language::Examples;
use arwen_egg::{program_parser_interface::parse, synthesis};
use std::{fs::File, io::Read};

use components_n_specs::nat_library;

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
                3,
                ["data", stringify!($test_name)].iter().collect(),
            );
            insta::assert_display_snapshot!(prog.unwrap());
        }
    };
}

make_test!(nat_max, &nat_library());
make_test!(nat_pred, &nat_library());
