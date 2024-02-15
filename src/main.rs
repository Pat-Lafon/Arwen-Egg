/* use arwen_egg::synthgraph::SynthesisGraph;
use arwen_synth::{
    language::{BaseType, Constant, Examples, Signature, TestCase, Variable},
    libraries::nat_library,
}; */

fn main() {
    /* let mut g = SynthesisGraph::new(
        &Examples::new(
            vec![TestCase {
                inputs: vec![Constant::Int(0)],
                output: Constant::Int(1),
            }],
            vec![],
        ),
        vec![Variable {
            name: "arg0".to_string(),
            ty: BaseType::Int,
        }],
        &nat_library(),
        todo!(),
    );
    g.egg.rebuild();

    dbg!(&g.example_map.map);

    g.increment(&nat_library());
    g.increment(&nat_library());
    g.increment(&nat_library());

    g.egg.dot().to_dot("test.dot").unwrap();

    g.egg.dot().to_png("test.png").unwrap();

    dbg!(g.example_map.map); */
}
